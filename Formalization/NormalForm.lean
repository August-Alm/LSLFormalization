import Formalization.Safety
import Formalization.Readback

/-!
# A locally safe normal form reads back as itself

`normal_readsBack`: a closed, locally safe normal form `t` with coherent sharing paths reads
back as `erase t`.

A query walks down to a block `λx₁…xₙ. y a₁…aₘ` of the normal form, then up from the binder of
`y` to the root. `Top` describes the walk up from an address and the walk back down to it.
Local safety is used at one place: the address of an argument differs from the address of the
block that binds any variable visible in it, so `resolve` finds the right binder.
-/

namespace LSL

/-- A token that leaves a lambda through an occurrence of its variable comes back to that
occurrence, with the same exponential stacks. -/
def Coherent (t : Term) : Prop :=
  ∀ (b : Addr) (A : Ty) (body : Term), t.sub b = some (.lam A body) →
    ∀ (o : Addr) (π : Path), (o, π) ∈ occs body 0 (.body :: b) →
      ∀ D : Stacks, select (pushPath D π) (occs body 0 (.body :: b)) = some (o, D)

/-! ## Runs of the machine -/

inductive Reach (t : Term) : State → State → Prop
  | refl {s : State} : Reach t s s
  | head {s s' s'' : State} : step t s = .next s' → Reach t s' s'' → Reach t s s''

namespace Reach

theorem one {t : Term} {s s' : State} (h : step t s = .next s') : Reach t s s' :=
  .head h .refl

theorem trans {t : Term} {s₁ s₂ s₃ : State} (h₁ : Reach t s₁ s₂) :
    Reach t s₂ s₃ → Reach t s₁ s₃ := by
  induction h₁ with
  | refl => exact fun h₂ => h₂
  | head hs _ ih => exact fun h₂ => .head hs (ih h₂)

theorem output {t : Term} {s s' : State} (h : Reach t s s') :
    ∀ {n : Nat} {out : Output}, run n t s' = some out → ∃ n', run n' t s = some out := by
  induction h with
  | refl => exact fun {n} {_} hr => ⟨n, hr⟩
  | head hs _ ih =>
    intro n out hr
    obtain ⟨k, hk⟩ := ih hr
    refine ⟨k + 1, ?_⟩
    simp only [run, hs]
    exact hk

theorem back {t : Term} {s s' : State} (h : Reach t s s') :
    ∀ (n : Nat) (out : Output), run n t s = some out → ∃ n', run n' t s' = some out := by
  induction h with
  | refl => exact fun n _ hr => ⟨n, hr⟩
  | head hs _ ih =>
    intro n out hr
    cases n with
    | zero => simp [run] at hr
    | succ k =>
      simp only [run, hs] at hr
      exact ih k out hr

end Reach

theorem not_out_of_stuck {t : Term} {s : State} (h : step t s = .stuck) :
    ∀ n : Nat, run n t s = none
  | 0 => rfl
  | n + 1 => by simp only [run, h]

theorem step_app {t : Term} {a : Addr} {f u : Term} (h : t.sub a = some (.app f u))
    (D : Stacks) (T : List Side) :
    step t ⟨.down a, D, T⟩ = .next ⟨.down (.fn :: a), D, .q :: T⟩ := by
  simp [step, h]

theorem step_lam_q {t : Term} {a : Addr} {A : Ty} {b : Term} (h : t.sub a = some (.lam A b))
    (D : Stacks) (T : List Side) :
    step t ⟨.down a, D, .q :: T⟩ = .next ⟨.down (.body :: a), D, T⟩ := by
  simp [step, h]

theorem step_lam_p {t : Term} {a : Addr} {A : Ty} {b : Term} (h : t.sub a = some (.lam A b))
    {D S : Stacks} {o : Addr} (hsel : select D (occs b 0 (.body :: a)) = some (o, S))
    (T : List Side) : step t ⟨.down a, D, .p :: T⟩ = .next ⟨.up o, S, T⟩ := by
  simp [step, h, hsel]

theorem step_lam_nil {t : Term} {a : Addr} {A : Ty} {b : Term} (h : t.sub a = some (.lam A b))
    (D : Stacks) : step t ⟨.down a, D, []⟩ = .stuck := by
  simp [step, h]

theorem step_var {t : Term} {a : Addr} {i : Nat} {π : Path} {b : Addr}
    (h : t.sub a = some (.var i π)) (hb : binder a i = .inr b) (D : Stacks) (T : List Side) :
    step t ⟨.down a, D, T⟩ = .next ⟨.up b, pushPath D π, .p :: T⟩ := by
  simp [step, h, hb]

/-! ## Addresses -/

theorem sub_cons (t : Term) (d : Dir) (a : Addr) :
    t.sub (d :: a) = (t.sub a).bind (·.child d) := rfl

theorem sub_append (t : Term) : ∀ (e a : Addr), t.sub (e ++ a) = (t.sub a).bind (·.sub e)
  | [], a => by
    show t.sub a = (t.sub a).bind fun s => some s
    cases t.sub a <;> rfl
  | d :: e, a => by
    show t.sub (d :: (e ++ a)) = _
    rw [sub_cons, sub_append t e a]
    cases t.sub a <;> rfl

theorem binder_replicate_fn : ∀ (k : Nat) (a : Addr) (x : Nat),
    binder (List.replicate k .fn ++ a) x = binder a x
  | 0, _, _ => rfl
  | k + 1, a, x => by
    show binder (.fn :: (List.replicate k .fn ++ a)) x = _
    simp only [binder]
    exact binder_replicate_fn k a x

theorem binder_append : ∀ (e a : Addr) (x : Nat),
    binder (e ++ a) x =
      match binder e x with
      | .inl i => binder a i
      | .inr b => .inr (b ++ a)
  | [], _, _ => by simp [binder]
  | .body :: e, a, 0 => by simp [binder]
  | .body :: e, a, x + 1 => by
    simp only [List.cons_append, binder]
    exact binder_append e a x
  | .fn :: e, a, x => by
    simp only [List.cons_append, binder]
    exact binder_append e a x
  | .arg :: e, a, x => by
    simp only [List.cons_append, binder]
    exact binder_append e a x

theorem binder_inr : ∀ (o : Addr) (x : Nat) (b : Addr), binder o x = .inr b →
    ∃ e, o = e ++ .body :: b ∧ binder e x = .inl 0
  | [], x, b, h => by simp [binder] at h
  | .body :: a, 0, b, h => by
    simp only [binder, Sum.inr.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | .body :: a, x + 1, b, h => by
    simp only [binder] at h
    obtain ⟨e, he, hbe⟩ := binder_inr a x b h
    exact ⟨.body :: e, by simp [he], by simpa [binder] using hbe⟩
  | .fn :: a, x, b, h => by
    simp only [binder] at h
    obtain ⟨e, he, hbe⟩ := binder_inr a x b h
    exact ⟨.fn :: e, by simp [he], by simpa [binder] using hbe⟩
  | .arg :: a, x, b, h => by
    simp only [binder] at h
    obtain ⟨e, he, hbe⟩ := binder_inr a x b h
    exact ⟨.arg :: e, by simp [he], by simpa [binder] using hbe⟩

/-- An occurrence at the relative address `r.reverse` in `s` is listed by `occs`. -/
theorem occs_mem_rel : ∀ (r : List Dir) (s : Term) (i : Nat) (a : Addr) (x : Nat) (π : Path),
    s.sub r.reverse = some (.var x π) → binder r.reverse x = .inl i →
      (r.reverse ++ a, π) ∈ occs s i a
  | [], s, i, a, x, π, hs, hb => by
    simp only [List.reverse_nil, Term.sub, List.foldr_nil, Option.some.injEq] at hs
    simp only [List.reverse_nil, binder, Sum.inl.injEq] at hb
    subst hs
    subst hb
    simp [occs]
  | d :: r, s, i, a, x, π, hs, hb => by
    rw [List.reverse_cons] at hs hb ⊢
    rw [sub_append] at hs
    rw [binder_append] at hb
    cases hbr : binder r.reverse x with
    | inr b' => simp [hbr] at hb
    | inl i' =>
      simp only [hbr] at hb
      cases s with
      | var j ρ => cases d <;> simp [Term.sub, Term.child] at hs
      | lam A s' =>
        cases d with
        | body =>
          cases i' with
          | zero => simp [binder] at hb
          | succ i'' =>
            simp only [binder, Sum.inl.injEq] at hb
            subst hb
            have hs' : s'.sub r.reverse = some (.var x π) := by
              simpa [Term.sub, Term.child] using hs
            have := occs_mem_rel r s' (i'' + 1) (.body :: a) x π hs' hbr
            simpa [occs] using this
        | fn => simp [Term.sub, Term.child] at hs
        | arg => simp [Term.sub, Term.child] at hs
      | app f u =>
        cases d with
        | body => simp [Term.sub, Term.child] at hs
        | fn =>
          simp only [binder, Sum.inl.injEq] at hb
          subst hb
          have hs' : f.sub r.reverse = some (.var x π) := by
            simpa [Term.sub, Term.child] using hs
          have := occs_mem_rel r f i' (.fn :: a) x π hs' hbr
          simp only [occs, List.mem_append]
          exact .inl (by simpa using this)
        | arg =>
          simp only [binder, Sum.inl.injEq] at hb
          subst hb
          have hs' : u.sub r.reverse = some (.var x π) := by
            simpa [Term.sub, Term.child] using hs
          have := occs_mem_rel r u i' (.arg :: a) x π hs' hbr
          simp only [occs, List.mem_append]
          exact .inr (by simpa using this)

theorem occ_mem {t : Term} {o : Addr} {x : Nat} {π : Path} {b : Addr}
    (hs : t.sub o = some (.var x π)) (hb : binder o x = .inr b) :
    ∃ A body, t.sub b = some (.lam A body) ∧ (o, π) ∈ occs body 0 (.body :: b) := by
  obtain ⟨e, he, hbe⟩ := binder_inr o x b hb
  subst he
  rw [sub_append, sub_cons] at hs
  cases hsb : t.sub b with
  | none => simp [hsb] at hs
  | some sb =>
    cases sb with
    | var j ρ => simp [hsb, Term.child] at hs
    | app f u => simp [hsb, Term.child] at hs
    | lam A body =>
      have hs' : body.sub e.reverse.reverse = some (.var x π) := by
        simpa [hsb, Term.child] using hs
      have := occs_mem_rel e.reverse body 0 (.body :: b) x π hs' (by simpa using hbe)
      exact ⟨A, body, rfl, by simpa using this⟩

/-! ## Normal forms -/

def Term.apps (head : Term) (args : List Term) : Term := args.foldl .app head

inductive Nf : Term → Prop
  | lam {A : Ty} {s : Term} : Nf s → Nf (.lam A s)
  | neu {x : Nat} {π : Path} {args : List Term} :
      (∀ u, u ∈ args → Nf u) → Nf (Term.apps (.var x π) args)
  /-- A redex whose argument `g` is not used: `g` is kept, and need not be normal. -/
  | gc {A : Ty} {s g : Term} : occurrences 0 s = 0 → Nf s → Nf (.app (.lam A s) g)

theorem nf_of_normal : ∀ s : Term, (∀ s', ¬ Step s s') → Nf s
  | .var x π, _ => Nf.neu (x := x) (π := π) (args := []) (fun u hu => by simp at hu)
  | .lam A s, h => Nf.lam (nf_of_normal s fun s' hs => h _ (Step.lam hs))
  | .app f u, h => by
    have hf := nf_of_normal f fun f' hs => h _ (Step.appL hs)
    have hu := nf_of_normal u fun u' hs => h _ (Step.appR hs)
    cases hf with
    | lam _ => exact absurd Step.beta (h _)
    | gc _ _ => exact absurd (Step.appL Step.beta) (h _)
    | @neu x π args hargs =>
      have e : Term.app (Term.apps (.var x π) args) u = Term.apps (.var x π) (args ++ [u]) := by
        simp [Term.apps]
      rw [e]
      refine Nf.neu fun v hv => ?_
      rcases List.mem_append.mp hv with hv | hv
      · exact hargs v hv
      · simp only [List.mem_singleton] at hv
        subst hv
        exact hu

theorem erase_apps : ∀ (args : List Term) (h : Term),
    erase (Term.apps h args) = Tm.apps (erase h) (args.map erase)
  | [], _ => rfl
  | u :: rest, h => erase_apps rest (.app h u)

/-! ### Erasure that drops kept arguments -/

/-- The renaming under a lambda. -/
def liftR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- The renaming under the binder of a kept argument, which readback does not see. -/
def skipR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i

/-- The pure term of `t` without its kept arguments: a redex whose argument is not used
stands for its body. `ρ` renames the free variables. -/
def eraseK : (Nat → Nat) → Term → Tm
  | ρ, .var i _ => .var (ρ i)
  | ρ, .lam _ b => .lam (eraseK (liftR ρ) b)
  | ρ, .app (.lam _ b) u =>
    if occurrences 0 b = 0 then eraseK (skipR ρ) b
    else .app (.lam (eraseK (liftR ρ) b)) (eraseK ρ u)
  | ρ, .app f u => .app (eraseK ρ f) (eraseK ρ u)

theorem eraseK_apps (ρ : Nat → Nat) : ∀ (args : List Term) (h : Term),
    (∀ A b, h ≠ .lam A b) →
      eraseK ρ (Term.apps h args) = Tm.apps (eraseK ρ h) (args.map (eraseK ρ))
  | [], _, _ => rfl
  | a :: rest, h, hh => by
    have e : eraseK ρ (.app h a) = .app (eraseK ρ h) (eraseK ρ a) := by
      cases h with
      | lam A b => exact absurd rfl (hh A b)
      | var i π => simp [eraseK]
      | app f g => simp [eraseK]
    show eraseK ρ (Term.apps (.app h a) rest)
      = Tm.apps (eraseK ρ h) (eraseK ρ a :: rest.map (eraseK ρ))
    rw [eraseK_apps ρ rest (.app h a) (fun _ _ e => by cases e), e]
    rfl

/-- On a term without redexes, `eraseK` is `erase`. -/
theorem eraseK_of_normal : ∀ (t : Term) (ρ : Nat → Nat), (∀ i, ρ i = i) →
    (∀ t', ¬ Step t t') → eraseK ρ t = erase t
  | .var i π, ρ, hρ, _ => by simp [eraseK, erase, hρ]
  | .lam A b, ρ, hρ, h => by
    have hl : ∀ i, liftR ρ i = i := fun i => by cases i <;> simp [liftR, hρ]
    simp only [eraseK, erase, eraseK_of_normal b (liftR ρ) hl fun b' hs => h _ (Step.lam hs)]
  | .app (.lam A b) u, _, _, h => absurd Step.beta (h _)
  | .app (.var i π) u, ρ, hρ, h => by
    simp [eraseK, erase, hρ, eraseK_of_normal u ρ hρ fun u' hs => h _ (Step.appR hs)]
  | .app (.app f g) u, ρ, hρ, h => by
    have h1 := eraseK_of_normal (.app f g) ρ hρ fun f' hs => h _ (Step.appL hs)
    have h2 := eraseK_of_normal u ρ hρ fun u' hs => h _ (Step.appR hs)
    simp only [eraseK, erase] at h1 ⊢
    rw [h1, h2]

theorem occ_apps (i : Nat) : ∀ (args : List Term) (h : Term),
    occurrences i h ≤ occurrences i (Term.apps h args) ∧
      ∀ u, u ∈ args → occurrences i u ≤ occurrences i (Term.apps h args)
  | [], h => ⟨Nat.le_refl _, fun u hu => by simp at hu⟩
  | a :: rest, h => by
    obtain ⟨h1, h2⟩ := occ_apps i rest (.app h a)
    have e : occurrences i (.app h a) = occurrences i h + occurrences i a := rfl
    refine ⟨?_, fun u hu => ?_⟩
    · show occurrences i h ≤ occurrences i (Term.apps (.app h a) rest)
      omega
    · rcases List.mem_cons.mp hu with hu' | hu'
      · show occurrences i u ≤ occurrences i (Term.apps (.app h a) rest)
        rw [hu']
        omega
      · exact h2 u hu'

theorem Tm.lams_succ' : ∀ (k : Nat) (u : Tm), Tm.lams (k + 1) u = Tm.lams k (.lam u)
  | 0, _ => rfl
  | k + 1, u => by
    show Tm.lam (Tm.lams (k + 1) u) = Tm.lam (Tm.lams k (.lam u))
    rw [Tm.lams_succ' k u]

theorem getElem?_split {α : Type} : ∀ (l : List α) (i : Nat) (u : α), l[i]? = some u →
    ∃ pre post, l = pre ++ u :: post ∧ pre.length = i
  | [], i, u, h => by simp at h
  | a :: l, 0, u, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨[], l, rfl, rfl⟩
  | a :: l, i + 1, u, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨pre, post, hl, hlen⟩ := getElem?_split l i u h
    exact ⟨a :: pre, post, by simp [hl], by simp [hlen]⟩

/-- The head of a spine, and the walk down to it. -/
theorem spine {t : Term} : ∀ (args : List Term) (h : Term) (c : Addr),
    t.sub c = some (Term.apps h args) →
      t.sub (List.replicate args.length .fn ++ c) = some h ∧
      ∀ (D : Stacks) (T : List Side), Reach t ⟨.down c, D, T⟩
        ⟨.down (List.replicate args.length .fn ++ c), D, List.replicate args.length .q ++ T⟩
  | [], _, _, hs => ⟨hs, fun _ _ => .refl⟩
  | u :: rest, h, c, hs => by
    obtain ⟨hsub, hreach⟩ := spine rest (.app h u) c hs
    refine ⟨?_, fun D T => ?_⟩
    · show t.sub (.fn :: (List.replicate rest.length .fn ++ c)) = some h
      rw [sub_cons, hsub]
      rfl
    · exact (hreach D T).trans (Reach.one (step_app hsub D _))

theorem up_fn {t : Term} : ∀ (i : Nat) (c : Addr) (D : Stacks) (T : List Side),
    Reach t ⟨.up (List.replicate i .fn ++ c), D, List.replicate i .q ++ T⟩ ⟨.up c, D, T⟩
  | 0, _, _, _ => .refl
  | i + 1, c, D, T => .head (s' := ⟨.up (List.replicate i .fn ++ c), D, List.replicate i .q ++ T⟩)
      rfl (up_fn i c D T)

theorem head_facts {t : Term} {c : Addr} {x : Nat} {π : Path} {b : Addr} (pre : List Term)
    (hfn : t.sub (.fn :: c) = some (Term.apps (.var x π) pre)) (hb : binder c x = .inr b) :
    t.sub (List.replicate pre.length .fn ++ .fn :: c) = some (.var x π) ∧
      binder (List.replicate pre.length .fn ++ .fn :: c) x = .inr b := by
  refine ⟨(spine pre _ _ hfn).1, ?_⟩
  rw [binder_replicate_fn]
  simpa [binder] using hb

/-- From an argument up to the binder of the head variable. -/
theorem ascend {t : Term} {c : Addr} {x : Nat} {π : Path} {b : Addr} (pre : List Term)
    (hfn : t.sub (.fn :: c) = some (Term.apps (.var x π) pre)) (hb : binder c x = .inr b)
    (D : Stacks) (T : List Side) :
    Reach t ⟨.up (.arg :: c), D, T⟩
      ⟨.up b, pushPath D π, .p :: (List.replicate pre.length .q ++ .p :: T)⟩ := by
  obtain ⟨hhead, hbh⟩ := head_facts pre hfn hb
  have h1 : Reach t ⟨.up (.arg :: c), D, T⟩ ⟨.down (.fn :: c), D, .p :: T⟩ := Reach.one rfl
  have h2 := (spine pre _ _ hfn).2 D (.p :: T)
  exact h1.trans (h2.trans (Reach.one (step_var hhead hbh D _)))

/-- From the binder of the head variable back down into an argument. -/
theorem descend {t : Term} (hcoh : Coherent t) {c : Addr} {x : Nat} {π : Path} {b : Addr}
    (pre : List Term) (hfn : t.sub (.fn :: c) = some (Term.apps (.var x π) pre))
    (hb : binder c x = .inr b) (D : Stacks) (T : List Side) :
    Reach t ⟨.down b, pushPath D π, .p :: (List.replicate pre.length .q ++ .p :: T)⟩
      ⟨.down (.arg :: c), D, T⟩ := by
  obtain ⟨hhead, hbh⟩ := head_facts pre hfn hb
  obtain ⟨A, body, hlam, hmem⟩ := occ_mem hhead hbh
  have hsel := hcoh b A body hlam _ _ hmem D
  have h1 := Reach.one (step_lam_p hlam hsel (List.replicate pre.length .q ++ .p :: T))
  have h2 := up_fn (t := t) pre.length (.fn :: c) D (.p :: T)
  have h3 : Reach t ⟨.up (.fn :: c), D, .p :: T⟩ ⟨.down (.arg :: c), D, T⟩ := Reach.one rfl
  exact h1.trans (h2.trans h3)

/-! ## The walk up from an address, and back -/

/-- A token going up from `c` leaves at the root with `W` pushed, and a token entering at the
root with the stacks it left with comes back down to `c`. -/
def Top (t : Term) (c : Addr) (W : List Side) : Prop :=
  ∀ (D : Stacks) (T : List Side), ∃ E : Stacks,
    (∃ n, run n t ⟨.up c, D, T⟩ = some (.root, E, W ++ T)) ∧
    ∀ T' : List Side, Reach t ⟨.down [], E, W ++ T'⟩ ⟨.down c, D, T'⟩

theorem top_root (t : Term) : Top t [] [] :=
  fun D _ => ⟨D, ⟨1, rfl⟩, fun _ => .refl⟩

theorem top_body {t : Term} {c : Addr} {W : List Side} {A : Ty} {s : Term} (h : Top t c W)
    (hsub : t.sub c = some (.lam A s)) : Top t (.body :: c) (W ++ [.q]) := by
  intro D T
  obtain ⟨E, ⟨n, hn⟩, hdown⟩ := h D (.q :: T)
  refine ⟨E, ⟨n + 1, ?_⟩, fun T' => ?_⟩
  · rw [List.append_assoc]
    exact hn
  · rw [List.append_assoc]
    exact (hdown (.q :: T')).trans (Reach.one (step_lam_q hsub D T'))

/-- A redex whose argument is not used is transparent for the token. -/
theorem top_gc {t : Term} {c : Addr} {W : List Side} {A : Ty} {s g : Term} (h : Top t c W)
    (hsub : t.sub c = some (.app (.lam A s) g)) : Top t (.body :: .fn :: c) W := by
  intro D T
  obtain ⟨E, ⟨n, hn⟩, hdown⟩ := h D T
  have hfn : t.sub (.fn :: c) = some (.lam A s) := by
    rw [sub_cons, hsub]
    rfl
  refine ⟨E, ⟨n + 2, hn⟩, fun T' => ?_⟩
  exact (hdown T').trans
    ((Reach.one (step_app hsub D T')).trans (Reach.one (step_lam_q hfn D T')))

theorem top_arg {t : Term} (hcoh : Coherent t) {c : Addr} {x : Nat} {π : Path} {b : Addr}
    {W : List Side} (pre : List Term)
    (hfn : t.sub (.fn :: c) = some (Term.apps (.var x π) pre)) (hb : binder c x = .inr b)
    (htop : Top t b W) :
    Top t (.arg :: c) (W ++ .p :: (List.replicate pre.length .q ++ [.p])) := by
  intro D T
  obtain ⟨E, ⟨n, hn⟩, hdown⟩ := htop (pushPath D π) (.p :: (List.replicate pre.length .q ++ .p :: T))
  have e : ∀ T : List Side, W ++ .p :: (List.replicate pre.length .q ++ [.p]) ++ T
      = W ++ .p :: (List.replicate pre.length .q ++ .p :: T) := by
    intro T
    simp
  refine ⟨E, ?_, fun T' => ?_⟩
  · obtain ⟨n', hn'⟩ := (ascend pre hfn hb D T).output hn
    exact ⟨n', by rw [e]; exact hn'⟩
  · rw [e]
    exact (hdown _).trans (descend hcoh pre hfn hb D T')

/-! ## The stacks at the root -/

/-- The type of the block or variable with the given address, in a term of type `A`. -/
def tyAt : Ty → List Side → Option Ty
  | A, [] => some A
  | .arr A _, .p :: W => tyAt A W
  | .arr _ B, .q :: W => tyAt B W
  | .o, _ :: _ => none

theorem tyAt_append : ∀ (W : List Side) (A : Ty) (W' : List Side),
    tyAt A (W ++ W') = (tyAt A W).bind (tyAt · W')
  | [], A, W' => by simp [tyAt]
  | s :: W, .o, W' => by simp [tyAt]
  | .p :: W, .arr A B, W' => by simp [tyAt, tyAt_append W A W']
  | .q :: W, .arr A B, W' => by simp [tyAt, tyAt_append W B W']

theorem tyAt_order : ∀ (l : Nat) (σ τ : Ty),
    tyAt σ (List.replicate l .q ++ [.p]) = some τ → τ.order < σ.order
  | 0, .o, τ, h => by simp [tyAt] at h
  | 0, .arr A B, τ, h => by
    simp only [List.replicate_zero, List.nil_append, tyAt, Option.some.injEq] at h
    subst h
    simp only [Ty.order]
    omega
  | l + 1, .o, τ, h => by simp [List.replicate_succ, tyAt] at h
  | l + 1, .arr A B, τ, h => by
    simp only [List.replicate_succ, List.cons_append, tyAt] at h
    have := tyAt_order l B τ h
    simp only [Ty.order]
    omega

theorem ls_apps : ∀ (args : List Term) (h : Term) (m : Bool) (Γ : List Bind) (B : Ty),
    LS m Γ (Term.apps h args) B →
      ∃ C, LS m Γ h C ∧ ∀ (i : Nat) (u : Term), args[i]? = some u →
        ∃ τ, tyAt C (List.replicate i .q ++ [.p]) = some τ ∧ LS true (hide τ.order Γ) u τ
  | [], _, _, _, B, hls => ⟨B, hls, fun i u hi => by simp at hi⟩
  | u :: rest, h, m, Γ, B, hls => by
    obtain ⟨C, hC, hrest⟩ := ls_apps rest (.app h u) m Γ B hls
    cases hC with
    | @app _ _ A _ _ _ hh hu =>
      refine ⟨.arr A C, hh, fun i v hi => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨A, by simp [tyAt], hu⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨τ, hτ, hv⟩ := hrest j v hi
        exact ⟨τ, by simpa [List.replicate_succ, tyAt] using hτ, hv⟩

theorem dropQ_replicate : ∀ (k : Nat) (r : List Side),
    dropQ (List.replicate k .q ++ r) = (k + (dropQ r).1, (dropQ r).2)
  | 0, r => by simp
  | k + 1, r => by
    show dropQ (.q :: (List.replicate k .q ++ r)) = _
    simp only [dropQ, dropQ_replicate k r]
    congr 1
    omega

theorem parse_addr {V : List Side} {l m : Nat} (hV : dropQ V.reverse = (0, V.reverse)) :
    parse (V ++ List.replicate l .q ++ .p :: List.replicate m .q) = some (V, l, m) := by
  simp [parse, dropQ_replicate, dropQ, hV]

theorem resolve_grow {U : List Side} {anc : List Frame} {V : List Side} {l x k : Nat}
    (h : resolve (⟨U, k⟩ :: anc) V l = some x) :
    resolve (⟨U, k + 1⟩ :: anc) V l = some (x + 1) := by
  simp only [resolve] at h ⊢
  by_cases hUV : U = V
  · simp only [hUV, ite_true] at h ⊢
    by_cases hl : l < k
    · simp only [hl, ite_true, Option.some.injEq] at h
      have hl' : l < k + 1 := by omega
      simp only [hl', ite_true, Option.some.injEq]
      omega
    · simp [hl] at h
  · simp only [hUV, ite_false] at h ⊢
    cases hr : resolve anc V l with
    | none => simp [hr] at h
    | some y =>
      simp only [hr, Option.map_some, Option.some.injEq] at h ⊢
      omega

theorem resolve_enter {U : List Side} {anc : List Frame} {V : List Side} {l x : Nat}
    (hne : U ≠ V) (h : resolve anc V l = some x) : resolve (⟨U, 0⟩ :: anc) V l = some x := by
  simp [resolve, hne, h]

/-! ## Readback of a normal form -/

/-- Every visible variable that occurs in `s` has a binder whose stack `V ++ qˡ` at the root
`resolve` maps back to the variable, renamed by `ρ`. -/
def VarsOK (t : Term) (A₀ : Ty) (F : List Frame) (Γ : List Bind) (c : Addr) (ρ : Nat → Nat)
    (s : Term) : Prop :=
  ∀ (x : Nat) (bnd : Bind), Γ[x]? = some bnd → bnd.zone ≠ .hid → occurrences x s ≠ 0 →
    ∃ (b : Addr) (V : List Side) (l : Nat),
      binder c x = .inr b ∧ Top t b (V ++ List.replicate l .q) ∧ resolve F V l = some (ρ x) ∧
      dropQ V.reverse = (0, V.reverse) ∧
      tyAt A₀ (V ++ List.replicate l .q ++ [.p]) = some bnd.ty ∧
      (bnd.zone = .glob → V = [])

theorem replicate_snoc {α : Type} (a : α) : ∀ (k : Nat) (T : List α),
    List.replicate (k + 1) a ++ T = List.replicate k a ++ a :: T
  | 0, _ => rfl
  | k + 1, T => by
    show a :: (List.replicate (k + 1) a ++ T) = a :: (List.replicate k a ++ a :: T)
    rw [replicate_snoc a k T]

theorem childAddr_append (V : List Side) (l i : Nat) (T : List Side) :
    childAddr V l i ++ T
      = V ++ List.replicate l .q ++ .p :: (List.replicate i .q ++ .p :: T) := by
  simp [childAddr]

/-- `s` is the part of a block below its first `k` lambdas; the block has address `U`. -/
theorem reads_nf {t : Term} {A₀ : Ty} (hcoh : Coherent t) {s : Term} (hnf : Nf s) :
    ∀ (m : Bool) (Γ : List Bind) (τ : Ty) (c : Addr) (anc : List Frame) (U : List Side)
      (k : Nat) (D Din : Stacks) (ρ : Nat → Nat),
      LS m Γ s τ → t.sub c = some s → Top t c (U ++ List.replicate k .q) →
      (∀ T, Reach t ⟨.down [], D, U ++ List.replicate k .q ++ T⟩ ⟨.down c, Din, T⟩) →
      (∀ k', k' < k → ¬ Defined t .root D (U ++ List.replicate k' .q)) →
      dropQ U.reverse = (0, U.reverse) →
      tyAt A₀ (U ++ List.replicate k .q) = some τ →
      (m = false → U = []) →
      VarsOK t A₀ (⟨U, k⟩ :: anc) Γ c ρ s →
      Reads t anc D U (Tm.lams k (eraseK ρ s)) := by
  induction hnf with
  | @gc A s' g hocc _ ih =>
    intro m Γ τ c anc U k D Din ρ hls hsub htop hreach hmin hU hty hroot hvars
    cases hls with
    | app hf _ =>
      cases hf with
      | lam hbody =>
        have hfn : t.sub (.fn :: c) = some (.lam A s') := by
          rw [sub_cons, hsub]
          rfl
        have hsub' : t.sub (.body :: .fn :: c) = some s' := by
          rw [sub_cons, hfn]
          rfl
        have hreach' : ∀ T, Reach t ⟨.down [], D, U ++ List.replicate k .q ++ T⟩
            ⟨.down (.body :: .fn :: c), Din, T⟩ := fun T =>
          (hreach T).trans
            ((Reach.one (step_app hsub Din T)).trans (Reach.one (step_lam_q hfn Din T)))
        have hvars' : VarsOK t A₀ (⟨U, k⟩ :: anc) (⟨A, zoneOf m⟩ :: Γ) (.body :: .fn :: c)
            (skipR ρ) s' := by
          intro x bnd hx hz hx0
          cases x with
          | zero => exact absurd hocc hx0
          | succ y =>
            simp only [List.getElem?_cons_succ] at hx
            have hy : occurrences y (.app (.lam A s') g) ≠ 0 := by
              simp only [occurrences]
              omega
            obtain ⟨b, V, l, hb, htb, hres, hV, htyb, hg⟩ := hvars y bnd hx hz hy
            exact ⟨b, V, l, by simpa [binder] using hb, htb, hres, hV, htyb, hg⟩
        have h := ih m _ τ (.body :: .fn :: c) anc U k D Din (skipR ρ) hbody hsub'
          (top_gc htop hsub) hreach' hmin hU hty hroot hvars'
        simp only [eraseK, hocc, ite_true]
        exact h
  | @lam A s' _ ih =>
    intro m Γ τ c anc U k D Din ρ hls hsub htop hreach hmin hU hty hroot hvars
    cases hls with
    | @lam _ _ _ B _ hbody =>
      have hsub' : t.sub (.body :: c) = some s' := by
        rw [sub_cons, hsub]
        rfl
      have htop' : Top t (.body :: c) (U ++ List.replicate (k + 1) .q) := by
        have h := top_body htop hsub
        rw [List.append_assoc, ← List.replicate_succ'] at h
        exact h
      have hreach' : ∀ T, Reach t ⟨.down [], D, U ++ List.replicate (k + 1) .q ++ T⟩
          ⟨.down (.body :: c), Din, T⟩ := by
        intro T
        have e : U ++ List.replicate (k + 1) .q ++ T = U ++ List.replicate k .q ++ .q :: T := by
          rw [List.append_assoc, replicate_snoc, ← List.append_assoc]
        rw [e]
        exact (hreach (.q :: T)).trans (Reach.one (step_lam_q hsub Din T))
      have hmin' : ∀ k', k' < k + 1 → ¬ Defined t .root D (U ++ List.replicate k' .q) := by
        intro k' hk'
        by_cases hlt : k' < k
        · exact hmin k' hlt
        · have hk : k' = k := by omega
          rw [hk]
          rintro ⟨out, hsem⟩
          obtain ⟨n, hn⟩ := sem_root.mp hsem
          have h1 := hreach []
          rw [List.append_nil] at h1
          obtain ⟨n', hn'⟩ := h1.back n out hn
          rw [not_out_of_stuck (step_lam_nil hsub Din) n'] at hn'
          cases hn'
      have hty' : tyAt A₀ (U ++ List.replicate (k + 1) .q) = some B := by
        rw [List.replicate_succ', ← List.append_assoc, tyAt_append, hty]
        simp [tyAt]
      have hvars' : VarsOK t A₀ (⟨U, k + 1⟩ :: anc) (⟨A, zoneOf m⟩ :: Γ) (.body :: c)
          (liftR ρ) s' := by
        intro x bnd hx hz hx0
        cases x with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          refine ⟨c, U, k, by simp [binder], htop, by simp [resolve, liftR], hU, ?_, ?_⟩
          · rw [tyAt_append, hty]
            simp [tyAt]
          · intro hg
            cases m with
            | true => simp [zoneOf] at hg
            | false => exact hroot rfl
        | succ y =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨b, V, l, hb, htb, hres, hV, htyb, hg⟩ := hvars y bnd hx hz hx0
          exact ⟨b, V, l, by simpa [binder] using hb, htb, resolve_grow hres, hV, htyb, hg⟩
      have h := ih m _ B (.body :: c) anc U (k + 1) D Din (liftR ρ) hbody hsub' htop' hreach'
        hmin' hU hty' hroot hvars'
      rw [Tm.lams_succ'] at h
      exact h
  | @neu x π args _ ih =>
    intro m Γ τ c anc U k D Din ρ hls hsub htop hreach hmin hU hty hroot hvars
    obtain ⟨C, hC, hargs⟩ := ls_apps args (.var x π) m Γ τ hls
    cases hC with
    | @var _ _ _ _ bnd hx hz =>
      have hxocc : occurrences x (Term.apps (.var x π) args) ≠ 0 := by
        have h := (occ_apps x args (.var x π)).1
        simp only [occurrences, ite_true] at h
        omega
      obtain ⟨b, V, l, hbind, htopb, hres, hV, htyb, hglob⟩ := hvars x bnd hx hz hxocc
      obtain ⟨hhead, hspine⟩ := spine args (.var x π) c hsub
      have hbh : binder (List.replicate args.length .fn ++ c) x = .inr b := by
        rw [binder_replicate_fn]
        exact hbind
      obtain ⟨E, ⟨n, hn⟩, hdown⟩ := htopb (pushPath Din π) (.p :: List.replicate args.length .q)
      have hquery : Reach t ⟨.down [], D, U ++ List.replicate k .q⟩
          ⟨.up b, pushPath Din π, .p :: List.replicate args.length .q⟩ := by
        have h1 := hreach []
        have h2 := hspine Din []
        have h3 := Reach.one (step_var hhead hbh Din (List.replicate args.length .q ++ []))
        simp only [List.append_nil] at h1 h2 h3
        exact h1.trans (h2.trans h3)
      obtain ⟨n', hn'⟩ := hquery.output hn
      rw [eraseK_apps ρ args (.var x π) (fun _ _ e => by cases e)]
      refine Reads.node (sem_root.mpr ⟨n', hn'⟩) hmin (parse_addr hV) hres (by simp) ?_
      intro i a hi
      rw [List.getElem?_map] at hi
      cases hu : args[i]? with
      | none => simp [hu] at hi
      | some u =>
        simp only [hu, Option.map_some, Option.some.injEq] at hi
        subst hi
        obtain ⟨τi, hτi, hlsu⟩ := hargs i u hu
        obtain ⟨pre, post, hsplit, hlen⟩ := getElem?_split args i u hu
        subst hsplit
        subst hlen
        have happ : Term.apps (.var x π) (pre ++ u :: post)
            = Term.apps (.app (Term.apps (.var x π) pre) u) post := by
          simp [Term.apps]
        rw [happ] at hsub
        have hnode := (spine post _ c hsub).1
        have hfn : t.sub (.fn :: (List.replicate post.length .fn ++ c))
            = some (Term.apps (.var x π) pre) := by
          rw [sub_cons, hnode]
          rfl
        have harg : t.sub (.arg :: (List.replicate post.length .fn ++ c)) = some u := by
          rw [sub_cons, hnode]
          rfl
        have hbc : binder (List.replicate post.length .fn ++ c) x = .inr b := by
          rw [binder_replicate_fn]
          exact hbind
        have hτ : tyAt A₀ (childAddr V l pre.length) = some τi := by
          have e : childAddr V l pre.length
              = (V ++ List.replicate l .q ++ [.p]) ++ (List.replicate pre.length .q ++ [.p]) := by
            simp [childAddr]
          rw [e, tyAt_append, htyb]
          exact hτi
        refine ih u (by simp) true (hide τi.order Γ) τi
          (.arg :: (List.replicate post.length .fn ++ c)) (⟨U, k⟩ :: anc)
          (childAddr V l pre.length) 0 E Din ρ hlsu harg ?_ ?_
          (fun k' hk => absurd hk (Nat.not_lt_zero _)) (by simp [childAddr, dropQ]) ?_
          (fun h => by cases h) ?_
        · have h := top_arg hcoh pre hfn hbc htopb
          have e : childAddr V l pre.length ++ List.replicate 0 .q
              = V ++ List.replicate l .q ++ .p :: (List.replicate pre.length .q ++ [.p]) := by
            simp [childAddr]
          rw [e]
          exact h
        · intro T
          have e : childAddr V l pre.length ++ List.replicate 0 .q ++ T
              = V ++ List.replicate l .q ++ .p :: (List.replicate pre.length .q ++ .p :: T) := by
            simp [childAddr]
          rw [e]
          exact (hdown _).trans (descend hcoh pre hfn hbc Din T)
        · simpa using hτ
        · intro x' bnd' hx' hz' hocc'
          rw [getElem?_hide] at hx'
          cases hx0 : Γ[x']? with
          | none => simp [hx0] at hx'
          | some bnd0 =>
            simp only [hx0, Option.map_some, Option.some.injEq] at hx'
            subst hx'
            obtain ⟨hkeep, hord⟩ := hideBind_visible hz'
            rw [hkeep] at hz' ⊢
            have hocc0 : occurrences x' (Term.apps (.var x π) (pre ++ u :: post)) ≠ 0 := by
              have h := (occ_apps x' (pre ++ u :: post) (.var x π)).2 u (by simp)
              omega
            obtain ⟨b', V', l', hbind', htop', hres', hV', hty', hglob'⟩ :=
              hvars x' bnd0 hx0 hz' hocc0
            refine ⟨b', V', l', ?_, htop', resolve_enter ?_ hres', hV', hty', hglob'⟩
            · simp only [binder]
              rw [binder_replicate_fn]
              exact hbind'
            · intro heq
              cases hzone : bnd0.zone with
              | hid => exact hz' hzone
              | glob =>
                rw [hglob' hzone] at heq
                simp [childAddr] at heq
              | loc =>
                rw [List.append_assoc, tyAt_append] at hty'
                cases hσ : tyAt A₀ V' with
                | none => simp [hσ] at hty'
                | some σ =>
                  rw [hσ] at hty'
                  have h1 := tyAt_order l' σ bnd0.ty hty'
                  rw [← heq, hτ] at hσ
                  cases hσ
                  have h2 := hord hzone
                  omega

/-- A closed, locally safe normal form with coherent paths reads back as itself, without the
arguments it keeps. -/
theorem nf_readsBack {t : Term} {A : Ty} (hsafe : LocallySafe t A) (hnf : Nf t)
    (hcoh : Coherent t) : ReadsBack t (eraseK id t) :=
  reads_nf (A₀ := A) hcoh hnf false [] A [] [] [] 0 Stacks.empty Stacks.empty id hsafe rfl
    (top_root t) (fun _ => .refl) (fun _ hk => absurd hk (Nat.not_lt_zero _)) rfl
    (by simp [tyAt]) (fun _ => rfl) (fun x bnd hx => by simp at hx)

/-- A closed, locally safe normal form with coherent paths reads back as itself. -/
theorem normal_readsBack {t : Term} {A : Ty} (hsafe : LocallySafe t A)
    (hnormal : ∀ t', ¬ Step t t') (hcoh : Coherent t) : ReadsBack t (erase t) := by
  have h := nf_readsBack hsafe (nf_of_normal t hnormal) hcoh
  rwa [eraseK_of_normal t id (fun _ => rfl) hnormal] at h

end LSL
