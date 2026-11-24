import Formalization.BetaSim

/-!
# The pointer machine under a beta step: the simulation

`Sim` relates a state of the machine on the reduct `t'` to a state of the machine on `t`.
`sim_next`: for every step on `t'`, the machine on `t` makes at least one step to a related
state. `sim_done` and `sim_starved` say the same for the end of a run and for a run that
stops with an empty tape. `beta_out`: if a run on `t'` from the root reaches the root again,
so does the run on `t` from the related tape, with a related tape.

An exit of `t'` and the exit of `t` that it stands for (`ExitSim`) differ in two ways: the
occurrence is the one in `t`, and the exit from a place in a copy of `N` to a lambda above
the redex has the entry for `N` among its saved entries (`withArg`).
-/

/-- Two lists are related entry by entry. -/
inductive List.Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : List.Forall₂ R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} : R a b → List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (a :: l₁) (b :: l₂)

namespace LSL

/-! ## Lists -/

section Lists

variable {α β : Type} {R : α → β → Prop}

theorem fa2_length : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [fa2_length h]

theorem fa2_take : ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    List.Forall₂ R (l₁.take n) (l₂.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h₁ h₂ => .cons h₁ (fa2_take n h₂)

theorem fa2_drop : ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    List.Forall₂ R (l₁.drop n) (l₂.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ h₂ => fa2_drop n h₂

theorem fa2_append : ∀ {l₁ : List α} {l₂ : List β} {l₃ : List α} {l₄ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h₁ h₂, h => .cons h₁ (fa2_append h₂ h)

theorem take_take_of_le : ∀ (j m : Nat) (L : List α), j ≤ m → (L.take m).take j = L.take j
  | 0, _, _, _ => rfl
  | j + 1, 0, _, h => by omega
  | j + 1, m + 1, [], _ => rfl
  | j + 1, m + 1, x :: L, h => by
    show x :: ((L.take m).take j) = x :: L.take j
    rw [take_take_of_le j m L (by omega)]

theorem drop_take_sub : ∀ (j m : Nat) (L : List α),
    (L.take m).drop j = (L.drop j).take (m - j)
  | 0, _, _ => rfl
  | j + 1, 0, L => by simp
  | j + 1, m + 1, [] => by simp
  | j + 1, m + 1, x :: L => by
    show (L.take m).drop j = (L.drop j).take (m + 1 - (j + 1))
    rw [Nat.add_sub_add_right]
    exact drop_take_sub j m L

end Lists

/-! ## The entry for the argument, in parts of a log -/

theorem withArg_take_le (r e : Addr) : ∀ (m k : Nat) (L : List Exit), m ≤ k → k ≤ L.length →
    (withArg r k e L).take m = L.take m
  | 0, _, _, _, _ => rfl
  | m + 1, 0, _, h, _ => by omega
  | m + 1, k + 1, [], _, h => by simp at h
  | m + 1, k + 1, x :: L, h₁, h₂ => by
    rw [withArg_cons]
    show x :: (withArg r k e L).take m = x :: L.take m
    rw [withArg_take_le r e m k L (by omega) (by simpa using h₂)]

theorem withArg_drop_le (r e : Addr) : ∀ (m k : Nat) (L : List Exit), m ≤ k → k ≤ L.length →
    (withArg r k e L).drop m = withArg r (k - m) e (L.drop m)
  | 0, _, _, _, _ => rfl
  | m + 1, 0, _, h, _ => by omega
  | m + 1, k + 1, [], _, h => by simp at h
  | m + 1, k + 1, x :: L, h₁, h₂ => by
    rw [withArg_cons]
    show (withArg r k e L).drop m = withArg r (k + 1 - (m + 1)) e (L.drop m)
    rw [Nat.add_sub_add_right]
    exact withArg_drop_le r e m k L (by omega) (by simpa using h₂)

theorem withArg_take_ge (r e : Addr) : ∀ (k m : Nat) (L : List Exit), k + argDepth e ≤ m →
    m ≤ L.length → (withArg r k e L).take (m - argDepth e + 1) = withArg r k e (L.take m)
  | 0, m, L, h₁, _ => by
    rw [withArg_zero, withArg_zero, take_take_of_le _ _ _ (by omega), drop_take_sub]
    rfl
  | k + 1, 0, _, h₁, _ => by omega
  | k + 1, m + 1, [], _, h₂ => by simp at h₂
  | k + 1, m + 1, x :: L, h₁, h₂ => by
    rw [withArg_cons, show m + 1 - argDepth e + 1 = (m - argDepth e + 1) + 1 by omega]
    show x :: (withArg r k e L).take (m - argDepth e + 1) = withArg r (k + 1) e (x :: L.take m)
    rw [withArg_cons, withArg_take_ge r e k m L (by omega) (by simpa using h₂)]

theorem withArg_drop_ge (r e : Addr) : ∀ (k m : Nat) (L : List Exit), k + argDepth e ≤ m →
    m ≤ L.length → (withArg r k e L).drop (m - argDepth e + 1) = L.drop m
  | 0, m, L, h₁, _ => by
    rw [withArg_zero]
    show (L.drop (argDepth e)).drop (m - argDepth e) = L.drop m
    rw [List.drop_drop]
    congr 1
    omega
  | k + 1, 0, _, h₁, _ => by omega
  | k + 1, m + 1, [], _, h₂ => by simp at h₂
  | k + 1, m + 1, x :: L, h₁, h₂ => by
    rw [withArg_cons, show m + 1 - argDepth e + 1 = (m - argDepth e + 1) + 1 by omega]
    show (withArg r k e L).drop (m - argDepth e + 1) = L.drop m
    exact withArg_drop_ge r e k m L (by omega) (by simpa using h₂)

theorem withArg_append_left (r e : Addr) (k : Nat) : ∀ (σ L : List Exit),
    σ ++ withArg r k e L = withArg r (σ.length + k) e (σ ++ L)
  | [], L => by simp
  | x :: σ, L => by
    rw [List.cons_append, List.cons_append, withArg_append_left r e k σ L, List.length_cons,
      show σ.length + 1 + k = (σ.length + k) + 1 by omega, withArg_cons]

theorem withArg_append_right (r e : Addr) : ∀ (k : Nat) (σ L : List Exit),
    k + argDepth e ≤ σ.length → withArg r k e σ ++ L = withArg r k e (σ ++ L)
  | 0, σ, L, h => by
    rw [withArg_zero, withArg_zero, List.cons_append,
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  | k + 1, [], L, h => by simp at h
  | k + 1, x :: σ, L, h => by
    rw [List.cons_append, withArg_cons, withArg_cons, List.cons_append,
      withArg_append_right r e k σ L (by simp at h; omega)]

/-! ## Kinds and binders -/

theorem kind_lam {s : Term} {A : Ty} (h : s.kind = .lam A) : ∃ b, s = .lam A b := by
  cases s with
  | var _ _ => simp [Term.kind] at h
  | lam B b =>
    simp only [Term.kind, Kind.lam.injEq] at h
    subst h
    exact ⟨b, rfl⟩
  | app _ _ => simp [Term.kind] at h

theorem kind_app {s : Term} (h : s.kind = .app) : ∃ f u, s = .app f u := by
  cases s with
  | var _ _ => simp [Term.kind] at h
  | lam _ _ => simp [Term.kind] at h
  | app f u => exact ⟨f, u, rfl⟩

theorem sub_app_of_child {t : Term} {d : Dir} {p : Addr} {s : Term} (hd : d ≠ .body)
    (h : t.sub (d :: p) = some s) : ∃ f u, t.sub p = some (.app f u) := by
  rw [sub_cons] at h
  cases h₀ : t.sub p with
  | none => simp [h₀] at h
  | some s₀ =>
    rw [h₀] at h
    cases s₀ with
    | var _ _ => cases d <;> simp [Term.child] at h
    | lam _ _ =>
      cases d with
      | body => exact absurd rfl hd
      | fn => simp [Term.child] at h
      | arg => simp [Term.child] at h
    | app f u => exact ⟨f, u, rfl⟩

theorem sub_var_nil {i : Nat} {π : Path} : ∀ (n : Addr) (s : Term),
    (Term.var i π).sub n = some s → n = []
  | [], _, _ => rfl
  | d :: n, s, h => by
    rw [sub_cons] at h
    cases h₀ : (Term.var i π).sub n with
    | none => simp [h₀] at h
    | some s₀ =>
      rw [h₀] at h
      have hn := sub_var_nil n s₀ h₀
      subst hn
      simp only [Term.sub, List.foldr_nil, Option.some.injEq] at h₀
      subst h₀
      cases d <;> simp [Term.child] at h

theorem binderOf_some {t : Term} {o b : Addr} (h : binderOf t o = some b) :
    ∃ i π, t.sub o = some (.var i π) ∧ binder o i = .inr b := by
  unfold binderOf at h
  cases hso : t.sub o with
  | none => simp [hso] at h
  | some u =>
    cases u with
    | var i π =>
      simp only [hso] at h
      cases hbi : binder o i with
      | inl k => simp [hbi] at h
      | inr b' =>
        simp only [hbi, Option.some.injEq] at h
        subst h
        exact ⟨i, π, rfl, hbi⟩
    | lam _ _ => simp [hso] at h
    | app _ _ => simp [hso] at h

theorem binder_append_inr {e a b : Addr} {i : Nat} (h : binder e i = .inr b) :
    binder (e ++ a) i = .inr (b ++ a) := by
  simp [binder_append, h]

theorem binder_append_ge {e : Addr} (a : Addr) {i : Nat} (h : bodies e ≤ i) :
    binder (e ++ a) i = binder a (i - bodies e) := by
  simp [binder_append, binder_ge e i h]

/-- The lambda of a variable lies above it. -/
theorem binder_above {o b : Addr} {i : Nat} (h : binder o i = .inr b) :
    argDepth b ≤ argDepth o ∧ b.length < o.length ∧ b <:+ o := by
  obtain ⟨e, rfl, _⟩ := binder_inr o i b h
  refine ⟨by simp [argDepth_append], ?_, ⟨e ++ [.body], by simp⟩⟩
  simp only [List.length_append, List.length_cons]
  omega

section

variable {t : Term} {r : Addr} {A : Ty} {M N : Term} {t' : Term}

theorem Loc.ins_le {a' a : Addr} {k : Nat} {e : Addr} (hloc : Loc t r M N a' a (some (k, e))) :
    k + argDepth e ≤ argDepth a' := by
  cases hloc with
  | copy hs hn =>
    simp only [argDepth_append]
    omega

/-- The subterms at a place of the reduct and at the place of `t` that it stands for. -/
theorem Loc.sub (h : Redex t r A M N t') {a' a : Addr} {ins : Option (Nat × Addr)}
    (hloc : Loc t r M N a' a ins) :
    ∃ s s', t.sub a = some s ∧ t'.sub a' = some s' ∧
      (∀ B, s'.kind = .lam B → s.kind = .lam B) ∧ (s'.kind = .app → s.kind = .app) := by
  cases hloc with
  | @out a₀ s hr hv =>
    have hk := h.kind_outside hr
    simp only [kindAt, hv, Option.map_some] at hk
    cases hs' : t'.sub a' with
    | none => simp [hs'] at hk
    | some s' =>
      simp only [hs', Option.map_some, Option.some.injEq] at hk
      exact ⟨s, s', hv, rfl, fun B e => by rw [← hk]; exact e, fun e => by rw [← hk]; exact e⟩
  | @body e s hs hk =>
    refine ⟨s, _, (h.sub_body e).trans hs, h.sub_body' hs, fun B hl => ?_, fun hl => ?_⟩
    · rw [kind_subst N _ _ hk] at hl
      cases s <;> simp_all [Term.kind]
    · rw [kind_subst N _ _ hk] at hl
      cases s <;> simp [Term.kind] at hl ⊢
  | @copy e π n s hs hn =>
    refine ⟨s, _, (h.sub_arg n).trans hn, by rw [h.sub_copy' hs n, hn]; rfl, fun B hl => ?_,
      fun hl => ?_⟩
    · rw [kind_graft, kind_shift] at hl
      cases s <;> simp_all [Term.kind]
    · rw [kind_graft, kind_shift] at hl
      cases s <;> simp [Term.kind] at hl ⊢

/-- An address of the reduct stands for one address of `t`. -/
theorem Loc.functional_aux {x y a₁ a₂ : Addr} {ins₁ ins₂ : Option (Nat × Addr)}
    (h₁ : Loc t r M N x a₁ ins₁) (h₂ : Loc t r M N y a₂ ins₂) (hxy : x = y) :
    a₁ = a₂ ∧ ins₁ = ins₂ := by
  cases h₁ with
  | out hr hv =>
    cases h₂ with
    | out _ _ => exact ⟨hxy, rfl⟩
    | @body e s hs hk =>
      rw [hxy] at hr
      exact absurd (List.suffix_append e r) hr
    | @copy e π n s hs hn =>
      rw [hxy] at hr
      exact absurd (List.suffix_append (n ++ e) r) hr
  | @body e s hs hk =>
    cases h₂ with
    | out hr _ =>
      rw [← hxy] at hr
      exact absurd (List.suffix_append e r) hr
    | @body e₂ s₂ hs₂ hk₂ =>
      have he : e = e₂ := List.append_cancel_right hxy
      subst he
      exact ⟨rfl, rfl⟩
    | @copy e₂ π n s₂ hs₂ hn =>
      have he : e = n ++ e₂ := List.append_cancel_right hxy
      subst he
      rw [sub_append, hs₂] at hs
      have hn0 := sub_var_nil n s hs
      subst hn0
      simp only [Option.bind_some, Term.sub, List.foldr_nil, Option.some.injEq] at hs
      subst hs
      exact absurd rfl hk
  | @copy e π n s hs hn =>
    cases h₂ with
    | out hr _ =>
      rw [← hxy] at hr
      exact absurd (List.suffix_append (n ++ e) r) hr
    | @body e₂ s₂ hs₂ hk₂ =>
      have he : n ++ e = e₂ := List.append_cancel_right hxy
      subst he
      rw [sub_append, hs] at hs₂
      have hn0 := sub_var_nil n s₂ hs₂
      subst hn0
      simp only [Option.bind_some, Term.sub, List.foldr_nil, Option.some.injEq] at hs₂
      subst hs₂
      exact absurd rfl hk₂
    | @copy e₂ π₂ n₂ s₂ hs₂ hn₂ =>
      have he : n ++ e = n₂ ++ e₂ := List.append_cancel_right hxy
      rcases List.append_eq_append_iff.mp he with ⟨c, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
      · rw [sub_append, hs₂] at hs
        have hc := sub_var_nil c _ hs
        subst hc
        simp
      · rw [sub_append, hs] at hs₂
        have hc := sub_var_nil c _ hs₂
        subst hc
        simp

theorem Loc.functional {a' a₁ a₂ : Addr} {ins₁ ins₂ : Option (Nat × Addr)}
    (h₁ : Loc t r M N a' a₁ ins₁) (h₂ : Loc t r M N a' a₂ ins₂) : a₁ = a₂ ∧ ins₁ = ins₂ :=
  Loc.functional_aux h₁ h₂ rfl

/-- How the place of a variable and the place of its lambda lie, in the reduct (`a'`, `b'`)
and in `t` (`a`, `b`): outside the copies of `N`; both in a copy; or the variable in a copy
and the lambda above the redex. -/
inductive BRel (r : Addr) (a' b' a b : Addr) : Option (Nat × Addr) → Option (Nat × Addr) → Prop
  | plain : argDepth a - argDepth b = argDepth a' - argDepth b' → BRel r a' b' a b none none
  | inner {k kb : Nat} {e : Addr} : (e ++ r) <:+ b' → kb ≤ k →
      argDepth a' - argDepth b' = k - kb → argDepth a - argDepth b = k - kb →
      BRel r a' b' a b (some (k, e)) (some (kb, e))
  | outer {k : Nat} {e : Addr} : ¬ (e ++ r) <:+ b' → k + argDepth e ≤ argDepth a' - argDepth b' →
      argDepth a - argDepth b + argDepth e = argDepth a' - argDepth b' + 1 →
      BRel r a' b' a b (some (k, e)) none

/-- A variable of the reduct stands for a variable of `t`, and its lambda for the lambda of
that variable. -/
theorem Loc.lambda (h : Redex t r A M N t') {a' a : Addr} {ins : Option (Nat × Addr)}
    (hloc : Loc t r M N a' a ins) {i' : Nat} {π' : Path} {b' : Addr}
    (hs' : t'.sub a' = some (.var i' π')) (hb' : binder a' i' = .inr b') :
    ∃ i π b insb, t.sub a = some (.var i π) ∧ binder a i = .inr b ∧ Loc t r M N b' b insb ∧
      BRel r a' b' a b ins insb := by
  cases hloc with
  | @out a₀ s hr hv =>
    have hk := h.kind_outside hr
    simp only [kindAt, hv, hs', Option.map_some, Option.some.injEq, Term.kind] at hk
    obtain ⟨π, rfl⟩ := kind_var hk.symm
    obtain ⟨_, _, hsuf⟩ := binder_above hb'
    obtain ⟨A₀, body, hlam, _⟩ := occ_mem hv hb'
    exact ⟨i', π, b', none, hv, hb', Loc.out (fun hrb => hr (hrb.trans hsuf)) hlam, .plain rfl⟩
  | @body e s hs hk =>
    rw [h.sub_body' hs] at hs'
    have hst := (h.sub_body e).trans hs
    cases s with
    | lam _ _ => simp [subst] at hs'
    | app _ _ => simp [subst] at hs'
    | var i π =>
      have hne : i ≠ bodies e := fun e' => hk (by rw [e']; rfl)
      by_cases hlt : i < bodies e
      · simp only [subst, hlt, ite_true, Option.some.injEq, Term.var.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        obtain ⟨b₀, hb₀⟩ := binder_lt e i hlt
        rw [binder_append_inr hb₀] at hb'
        cases hb'
        obtain ⟨A₀, body, hlam, _⟩ := occ_mem hs hb₀
        refine ⟨i, π, b₀ ++ .body :: .fn :: r, none, hst, binder_append_inr hb₀,
          Loc.body hlam (by simp [Term.kind]), .plain ?_⟩
        simp only [argDepth_append, argDepth_body, argDepth_fn]
      · simp only [subst, hlt, hne, ite_false, Option.some.injEq, Term.var.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        rw [binder_append_ge r (by omega)] at hb'
        have hbt : binder (e ++ .body :: .fn :: r) i = .inr b' := by
          rw [binder_append_ge _ (by omega), show i - bodies e = (i - 1 - bodies e) + 1 by omega]
          exact hb'
        obtain ⟨A₀, body, hlam, _⟩ := occ_mem hst hbt
        obtain ⟨_, hl, _⟩ := binder_above hb'
        refine ⟨i, π, b', none, hst, hbt, Loc.out (fun hrb => ?_) hlam, .plain ?_⟩
        · have := hrb.length_le
          omega
        · simp only [argDepth_append, argDepth_body, argDepth_fn]
  | @copy e π n s hs hn =>
    rw [h.sub_copy' hs n, hn] at hs'
    simp only [Option.map_some, Option.some.injEq] at hs'
    have hst := (h.sub_arg n).trans hn
    cases s with
    | lam _ _ => simp [shift, graft] at hs'
    | app _ _ => simp [shift, graft] at hs'
    | var i₀ π₀ =>
      by_cases hlt : i₀ < bodies n
      · simp only [shift, hlt, ite_true, graft, Term.var.injEq] at hs'
        obtain ⟨rfl, _⟩ := hs'
        obtain ⟨b₀, hb₀⟩ := binder_lt n i₀ hlt
        rw [List.append_assoc, binder_append_inr hb₀, ← List.append_assoc] at hb'
        cases hb'
        obtain ⟨A₀, body, hlam, _⟩ := occ_mem hn hb₀
        obtain ⟨hd, _, _⟩ := binder_above hb₀
        refine ⟨i₀, π₀, b₀ ++ .arg :: r, some (argDepth b₀, e), hst, binder_append_inr hb₀,
          Loc.copy hs hlam, .inner ⟨b₀, by simp⟩ hd ?_ ?_⟩
        · simp only [argDepth_append]
          omega
        · simp only [argDepth_append, argDepth_arg]
          omega
      · have h2 : ¬ i₀ + bodies e < bodies n := by omega
        simp only [shift, hlt, ite_false, graft, h2, Term.var.injEq] at hs'
        obtain ⟨rfl, _⟩ := hs'
        rw [List.append_assoc, binder_append_ge _ (by omega), binder_append_ge _ (by omega),
          show i₀ + bodies e - bodies n - bodies e = i₀ - bodies n by omega] at hb'
        have hbt : binder (n ++ .arg :: r) i₀ = .inr b' := by
          rw [binder_append_ge _ (by omega)]
          exact hb'
        obtain ⟨A₀, body, hlam, _⟩ := occ_mem hst hbt
        obtain ⟨hd, hl, _⟩ := binder_above hb'
        refine ⟨i₀, π₀, b', none, hst, hbt, Loc.out (fun hrb => ?_) hlam,
          .outer (fun hsuf => ?_) ?_ ?_⟩
        · have := hrb.length_le
          omega
        · have := hsuf.length_le
          simp only [List.length_append] at this
          omega
        · simp only [argDepth_append]
          omega
        · simp only [argDepth_append, argDepth_arg]
          omega

/-! ## The relation between states -/

/-- An exit of the reduct and the exit of `t` that it stands for. -/
inductive ExitSim (t t' : Term) (r : Addr) (M N : Term) : Exit → Exit → Prop
  | dummy : ExitSim t t' r M N .outside .outside
  | plain {o' o : Addr} {σ' σ : List Exit} {b' : Addr} : Loc t r M N o' o none →
      binderOf t' o' = some b' → σ'.length = argDepth o' - argDepth b' →
      List.Forall₂ (ExitSim t t' r M N) σ' σ → ExitSim t t' r M N (.mk o' σ') (.mk o σ)
  | inner {o' o : Addr} {k : Nat} {e : Addr} {σ' σ : List Exit} {b' : Addr} :
      Loc t r M N o' o (some (k, e)) → binderOf t' o' = some b' → (e ++ r) <:+ b' →
      σ'.length = argDepth o' - argDepth b' →
      List.Forall₂ (ExitSim t t' r M N) σ' σ → ExitSim t t' r M N (.mk o' σ') (.mk o σ)
  | outer {o' o : Addr} {k : Nat} {e : Addr} {σ' σ : List Exit} {b' : Addr} :
      Loc t r M N o' o (some (k, e)) → binderOf t' o' = some b' → ¬ (e ++ r) <:+ b' →
      σ'.length = argDepth o' - argDepth b' →
      List.Forall₂ (ExitSim t t' r M N) σ' σ →
      ExitSim t t' r M N (.mk o' σ') (.mk o (withArg r k e σ))

inductive ItemSim (t t' : Term) (r : Addr) (M N : Term) : Item → Item → Prop
  | q : ItemSim t t' r M N .q .q
  | p {e' e : Exit} : ExitSim t t' r M N e' e → ItemSim t t' r M N (.p e') (.p e)

def SimAt (t t' : Term) (r : Addr) (M N : Term) (a' a : Addr) (T' T : List Item)
    (L' L : List Exit) : Prop :=
  ∃ ins, Loc t r M N a' a ins ∧ List.Forall₂ (ItemSim t t' r M N) T' T ∧
    LogSim (List.Forall₂ (ExitSim t t' r M N)) r ins L' L ∧ L'.length = argDepth a'

/-- A state of the machine on the reduct, and the state of the machine on `t` that it stands
for. -/
inductive Sim (t t' : Term) (r : Addr) (M N : Term) : QState → QState → Prop
  | down {a' a : Addr} {T' T : List Item} {L' L : List Exit} :
      SimAt t t' r M N a' a T' T L' L → Sim t t' r M N ⟨.down a', T', L'⟩ ⟨.down a, T, L⟩
  | up {a' a : Addr} {T' T : List Item} {L' L : List Exit} :
      SimAt t t' r M N a' a T' T L' L → Sim t t' r M N ⟨.up a', T', L'⟩ ⟨.up a, T, L⟩

theorem insChild_fn (ins : Option (Nat × Addr)) : insChild ins .fn = ins := by
  cases ins <;> simp [insChild]

theorem insChild_body (ins : Option (Nat × Addr)) : insChild ins .body = ins := by
  cases ins <;> simp [insChild]

theorem logSim_cons {R : Exit → Exit → Prop} {ins : Option (Nat × Addr)} {E' E : Exit}
    {L' L : List Exit} (hE : R E' E) (hL : LogSim (List.Forall₂ R) r ins L' L) :
    LogSim (List.Forall₂ R) r (insChild ins .arg) (E' :: L') (E :: L) := by
  cases ins with
  | none => exact List.Forall₂.cons hE hL
  | some x =>
    obtain ⟨k, e⟩ := x
    obtain ⟨L₀, h₀, rfl⟩ := hL
    exact ⟨E :: L₀, .cons hE h₀, (withArg_cons r k e E L₀).symm⟩

theorem logSim_uncons {R : Exit → Exit → Prop} {ins : Option (Nat × Addr)} {E' : Exit}
    {L' L₁ : List Exit} (h : LogSim (List.Forall₂ R) r (insChild ins .arg) (E' :: L') L₁) :
    ∃ E L, L₁ = E :: L ∧ R E' E ∧ LogSim (List.Forall₂ R) r ins L' L := by
  cases ins with
  | none =>
    have h' : List.Forall₂ R (E' :: L') L₁ := h
    cases h' with
    | cons hE hL => exact ⟨_, _, rfl, hE, hL⟩
  | some x =>
    obtain ⟨k, e⟩ := x
    obtain ⟨L₀, h₀, rfl⟩ := h
    cases h₀ with
    | cons hE hL => exact ⟨_, _, withArg_cons r k e _ _, hE, _, hL, rfl⟩

/-- The step from a variable to its lambda. -/
theorem sim_exit (h : Redex t r A M N t') {a' a : Addr} {ins : Option (Nat × Addr)}
    {T' T : List Item} {L' L : List Exit} (hloc : Loc t r M N a' a ins)
    (hT : List.Forall₂ (ItemSim t t' r M N) T' T)
    (hL : LogSim (List.Forall₂ (ExitSim t t' r M N)) r ins L' L)
    (hlen : L'.length = argDepth a') {i' : Nat} {π' : Path} {b' : Addr}
    (hs' : t'.sub a' = some (.var i' π')) (hb' : binder a' i' = .inr b') :
    ∃ k s₂, 0 < k ∧ qiter t k ⟨.down a, T, L⟩ = some s₂ ∧
      Sim t t' r M N ⟨.up b', .p ⟨a', L'.take (argDepth a' - argDepth b')⟩ :: T',
        L'.drop (argDepth a' - argDepth b')⟩ s₂ := by
  obtain ⟨i, π, b, insb, hst, hbt, hlocb, hrel⟩ := hloc.lambda h hs' hb'
  have hbo' : binderOf t' a' = some b' := by simp [binderOf, hs', hb']
  obtain ⟨hdb, _, _⟩ := binder_above hb'
  have hstep : qiter t 1 ⟨.down a, T, L⟩ = some ⟨.up b,
      .p ⟨a, L.take (argDepth a - argDepth b)⟩ :: T, L.drop (argDepth a - argDepth b)⟩ := by
    simp [qiter, qstep, hst, hbt]
  have hlt : (L'.take (argDepth a' - argDepth b')).length = argDepth a' - argDepth b' := by
    rw [List.length_take]
    omega
  have hld : (L'.drop (argDepth a' - argDepth b')).length = argDepth b' := by
    rw [List.length_drop]
    omega
  cases hrel with
  | plain hm =>
    rw [hm] at hstep
    exact ⟨1, _, Nat.one_pos, hstep, .up ⟨none, hlocb,
      .cons (.p (.plain hloc hbo' hlt (fa2_take _ hL))) hT, fa2_drop _ hL, hld⟩⟩
  | @inner k kb e hsuf hkb hk1 hk2 =>
    obtain ⟨L₀, h₀, rfl⟩ := hL
    have hk := hloc.ins_le
    have hl0 : L₀.length = argDepth a' := by rw [← fa2_length h₀, hlen]
    rw [hk2, withArg_take_le r e _ k L₀ (by omega) (by omega),
      withArg_drop_le r e _ k L₀ (by omega) (by omega),
      show k - (k - kb) = kb by omega, ← hk1] at hstep
    exact ⟨1, _, Nat.one_pos, hstep, .up ⟨some (kb, e), hlocb,
      .cons (.p (.inner hloc hbo' hsuf hlt (fa2_take _ h₀))) hT,
      ⟨_, fa2_drop _ h₀, rfl⟩, hld⟩⟩
  | @outer k e hns hge heq =>
    obtain ⟨L₀, h₀, rfl⟩ := hL
    have hl0 : L₀.length = argDepth a' := by rw [← fa2_length h₀, hlen]
    rw [show argDepth a - argDepth b = argDepth a' - argDepth b' - argDepth e + 1 by omega,
      withArg_take_ge r e k _ L₀ hge (by omega), withArg_drop_ge r e k _ L₀ hge (by omega)]
      at hstep
    exact ⟨1, _, Nat.one_pos, hstep, .up ⟨none, hlocb,
      .cons (.p (.outer hloc hbo' hns hlt (fa2_take _ h₀))) hT, fa2_drop _ h₀, hld⟩⟩

/-- The step from a lambda back to a variable. -/
theorem sim_return (h : Redex t r A M N t') {a' a : Addr} {ins : Option (Nat × Addr)}
    {T' T : List Item} {L' L : List Exit} (hloc : Loc t r M N a' a ins)
    (hT : List.Forall₂ (ItemSim t t' r M N) T' T)
    (hL : LogSim (List.Forall₂ (ExitSim t t' r M N)) r ins L' L)
    (hlen : L'.length = argDepth a') {A₀ : Ty} {b₀ : Term} (hs : t.sub a = some (.lam A₀ b₀))
    {E' E : Exit} (hE : ExitSim t t' r M N E' E) (hbe : binderOf t' E'.occ = some a') :
    ∃ k s₂, 0 < k ∧ qiter t k ⟨.down a, .p E :: T, L⟩ = some s₂ ∧
      Sim t t' r M N ⟨.up E'.occ, T', E'.saved ++ L'⟩ s₂ := by
  have hret : ∀ {o : Addr} {σ : List Exit}, binderOf t o = some a →
      qiter t 1 ⟨.down a, .p ⟨o, σ⟩ :: T, L⟩ = some ⟨.up o, T, σ ++ L⟩ := by
    intro o σ ho
    simp [qiter, qstep, hs, Exit.occ, Exit.saved, ho]
  cases hE with
  | dummy =>
    rw [binderOf_outside] at hbe
    cases hbe
  | @plain o' o σ' σ b' hlo hbo hσl hσ =>
    obtain rfl : b' = a' := Option.some.inj (hbo.symm.trans hbe)
    obtain ⟨i', π', hs', hb'⟩ := binderOf_some hbo
    obtain ⟨i, π, b, insb, hst, hbt, hlocb, hrel⟩ := hlo.lambda h hs' hb'
    obtain ⟨hdb, _, _⟩ := binder_above hb'
    cases hrel with
    | plain hm =>
      obtain ⟨rfl, rfl⟩ := hlocb.functional hloc
      have hbo_t : binderOf t o = some b := by simp [binderOf, hst, hbt]
      exact ⟨1, _, Nat.one_pos, hret hbo_t, .up ⟨none, hlo, hT, fa2_append hσ hL, by
        simp only [Exit.saved, Exit.occ, List.length_append, hσl, hlen]
        omega⟩⟩
  | @inner o' o k e σ' σ b' hlo hbo hsuf hσl hσ =>
    obtain rfl : b' = a' := Option.some.inj (hbo.symm.trans hbe)
    obtain ⟨i', π', hs', hb'⟩ := binderOf_some hbo
    obtain ⟨i, π, b, insb, hst, hbt, hlocb, hrel⟩ := hlo.lambda h hs' hb'
    obtain ⟨hdb, _, _⟩ := binder_above hb'
    cases hrel with
    | inner _ hkb hk1 hk2 =>
      obtain ⟨rfl, rfl⟩ := hlocb.functional hloc
      obtain ⟨L₀, h₀, rfl⟩ := hL
      have hbo_t : binderOf t o = some b := by simp [binderOf, hst, hbt]
      have hσ' : σ.length = argDepth o' - argDepth b' := by rw [← fa2_length hσ, hσl]
      refine ⟨1, _, Nat.one_pos, hret hbo_t, .up ⟨some (k, e), hlo, hT,
        ⟨σ ++ L₀, fa2_append hσ h₀, ?_⟩, by
          simp only [Exit.saved, Exit.occ, List.length_append, hσl, hlen]
          omega⟩⟩
      rw [withArg_append_left, hσ', hk1, Nat.sub_add_cancel hkb]
    | outer hns _ _ => exact absurd hsuf hns
  | @outer o' o k e σ' σ b' hlo hbo hns hσl hσ =>
    obtain rfl : b' = a' := Option.some.inj (hbo.symm.trans hbe)
    obtain ⟨i', π', hs', hb'⟩ := binderOf_some hbo
    obtain ⟨i, π, b, insb, hst, hbt, hlocb, hrel⟩ := hlo.lambda h hs' hb'
    obtain ⟨hdb, _, _⟩ := binder_above hb'
    cases hrel with
    | inner hsuf _ _ _ => exact absurd hsuf hns
    | outer _ hge heq =>
      obtain ⟨rfl, rfl⟩ := hlocb.functional hloc
      have hbo_t : binderOf t o = some b := by simp [binderOf, hst, hbt]
      have hσ' : σ.length = argDepth o' - argDepth b' := by rw [← fa2_length hσ, hσl]
      refine ⟨1, _, Nat.one_pos, hret hbo_t, .up ⟨some (k, e), hlo, hT,
        ⟨σ ++ L, fa2_append hσ hL, withArg_append_right r e k σ L (by omega)⟩, by
          simp only [Exit.saved, Exit.occ, List.length_append, hσl, hlen]
          omega⟩⟩

/-- For every step on the reduct, the machine on `t` makes at least one step. -/
theorem sim_next (h : Redex t r A M N t') {s' s s'' : QState} (hsim : Sim t t' r M N s' s)
    (hstep : qstep t' s' = .next s'') :
    ∃ k s₂, 0 < k ∧ qiter t k s = some s₂ ∧ Sim t t' r M N s'' s₂ := by
  cases hsim with
  | @down a' a T' T L' L hat =>
    obtain ⟨ins, hloc, hT, hL, hlen⟩ := hat
    obtain ⟨s₀, s₀', hs, hs', hlam, happ⟩ := hloc.sub h
    cases s₀' with
    | var i' π' =>
      cases hb' : binder a' i' with
      | inl j => simp [qstep, hs', hb'] at hstep
      | inr b' =>
        simp only [qstep, hs', hb', QResult.next.injEq] at hstep
        subst hstep
        exact sim_exit h hloc hT hL hlen hs' hb'
    | lam A' body' =>
      obtain ⟨b₀, rfl⟩ := kind_lam (hlam A' rfl)
      cases hT with
      | nil => simp [qstep, hs'] at hstep
      | @cons x' x T'' T₀ hx hT₀ =>
        cases hx with
        | q =>
          simp only [qstep, hs', QResult.next.injEq] at hstep
          subst hstep
          have hc : t.sub (.body :: a) = some b₀ := by
            rw [sub_cons, hs]
            rfl
          obtain ⟨k, a₂, ins₂, L₂, hk, hloc₂, hL₂⟩ :=
            arrive h hloc .body hc T₀ (by rw [insChild_body]; exact hL)
          exact ⟨1 + k, _, by omega,
            qiter_add t 1 k _ _ _ (by simp [qiter, qstep, hs]) hk,
            .down ⟨ins₂, hloc₂, hT₀, hL₂, by simpa using hlen⟩⟩
        | @p E' E hE =>
          by_cases hbe : binderOf t' E'.occ = some a'
          · simp only [qstep, hs', hbe, ite_true, QResult.next.injEq] at hstep
            subst hstep
            exact sim_return h hloc hT₀ hL hlen hs hE hbe
          · simp [qstep, hs', hbe] at hstep
    | app f' u' =>
      simp only [qstep, hs', QResult.next.injEq] at hstep
      subst hstep
      obtain ⟨f, u, rfl⟩ := kind_app (happ rfl)
      have hc : t.sub (.fn :: a) = some f := by
        rw [sub_cons, hs]
        rfl
      obtain ⟨k, a₂, ins₂, L₂, hk, hloc₂, hL₂⟩ :=
        arrive h hloc .fn hc (.q :: T) (by rw [insChild_fn]; exact hL)
      exact ⟨1 + k, _, by omega, qiter_add t 1 k _ _ _ (by simp [qiter, qstep, hs]) hk,
        .down ⟨ins₂, hloc₂, .cons .q hT, hL₂, by simpa using hlen⟩⟩
  | @up a' a T' T L' L hat =>
    obtain ⟨ins, hloc, hT, hL, hlen⟩ := hat
    obtain ⟨s₀, s₀', hs, hs', _, _⟩ := hloc.sub h
    obtain ⟨k₀, a₁, L₁, hk₀, _, hpar⟩ := depart h hloc T hL
    cases a' with
    | nil => simp [qstep] at hstep
    | cons d p' =>
      obtain ⟨p, insp, rfl, hlocp, hLp⟩ := hpar d p' rfl
      obtain ⟨sp, sp', hsp, hsp', _, happp⟩ := hlocp.sub h
      cases d with
      | body =>
        simp only [qstep, QResult.next.injEq] at hstep
        subst hstep
        rw [insChild_body] at hLp
        have hq : qiter t 1 ⟨.up (.body :: p), T, L₁⟩ = some ⟨.up p, .q :: T, L₁⟩ := by
          simp [qiter, qstep]
        exact ⟨k₀ + 1, _, by omega, qiter_add t k₀ 1 _ _ _ hk₀ hq,
          .up ⟨insp, hlocp, .cons .q hT, hLp, by simpa using hlen⟩⟩
      | fn =>
        obtain ⟨f', u', hp'⟩ := sub_app_of_child (by decide) hs'
        rw [hsp'] at hp'
        cases hp'
        obtain ⟨f, u, rfl⟩ := kind_app (happp rfl)
        cases hT with
        | nil => simp [qstep] at hstep
        | @cons x' x T'' T₀ hx hT₀ =>
          cases hx with
          | q =>
            simp only [qstep, QResult.next.injEq] at hstep
            subst hstep
            rw [insChild_fn] at hLp
            have hq : qiter t 1 ⟨.up (.fn :: p), .q :: T₀, L₁⟩ = some ⟨.up p, T₀, L₁⟩ := by
              simp [qiter, qstep]
            exact ⟨k₀ + 1, _, by omega, qiter_add t k₀ 1 _ _ _ hk₀ hq,
              .up ⟨insp, hlocp, hT₀, hLp, by simpa using hlen⟩⟩
          | @p E' E hE =>
            simp only [qstep, QResult.next.injEq] at hstep
            subst hstep
            rw [insChild_fn] at hLp
            have hc : t.sub (.arg :: p) = some u := by
              rw [sub_cons, hsp]
              rfl
            obtain ⟨k, a₂, ins₂, L₂, hk, hloc₂, hL₂⟩ :=
              arrive h hlocp .arg hc T₀ (logSim_cons hE hLp)
            exact ⟨k₀ + 1 + k, _, by omega,
              qiter_add t (k₀ + 1) k _ _ _
                (qiter_add t k₀ 1 _ _ _ hk₀ (by simp [qiter, qstep])) hk,
              .down ⟨ins₂, hloc₂, hT₀, hL₂, by simpa using hlen⟩⟩
      | arg =>
        obtain ⟨f', u', hp'⟩ := sub_app_of_child (by decide) hs'
        rw [hsp'] at hp'
        cases hp'
        obtain ⟨f, u, rfl⟩ := kind_app (happp rfl)
        cases L' with
        | nil => simp [qstep] at hstep
        | cons E' Lr' =>
          simp only [qstep, QResult.next.injEq] at hstep
          subst hstep
          obtain ⟨E, Lr, rfl, hE, hLr⟩ := logSim_uncons hLp
          have hc : t.sub (.fn :: p) = some f := by
            rw [sub_cons, hsp]
            rfl
          obtain ⟨k, a₂, ins₂, L₂, hk, hloc₂, hL₂⟩ :=
            arrive h hlocp .fn hc (.p E :: T) (by rw [insChild_fn]; exact hLr)
          exact ⟨k₀ + 1 + k, _, by omega,
            qiter_add t (k₀ + 1) k _ _ _
              (qiter_add t k₀ 1 _ _ _ hk₀ (by simp [qiter, qstep])) hk,
            .down ⟨ins₂, hloc₂, .cons (.p hE) hT, hL₂, by simpa using hlen⟩⟩

theorem qstep_done {t : Term} {s : QState} {T : List Item} (h : qstep t s = .done T) :
    s.pos = .up [] ∧ s.tape = T := by
  obtain ⟨pos, tape, log⟩ := s
  cases pos with
  | down a =>
    cases hsub : t.sub a with
    | none => simp [qstep, hsub] at h
    | some u =>
      cases u with
      | var i π => cases hb : binder a i <;> simp [qstep, hsub, hb] at h
      | lam A body =>
        cases tape with
        | nil => simp [qstep, hsub] at h
        | cons x T' =>
          cases x with
          | q => simp [qstep, hsub] at h
          | p e => by_cases hbe : binderOf t e.occ = some a <;> simp [qstep, hsub, hbe] at h
      | app f u => simp [qstep, hsub] at h
  | up a =>
    cases a with
    | nil =>
      simp only [qstep, QResult.done.injEq] at h
      exact ⟨rfl, h⟩
    | cons d a =>
      cases d with
      | body => simp [qstep] at h
      | fn =>
        cases tape with
        | nil => simp [qstep] at h
        | cons x T' => cases x <;> simp [qstep] at h
      | arg => cases log <;> simp [qstep] at h

/-- Where the run on the reduct ends at the root, the run on `t` ends there too. -/
theorem sim_done (h : Redex t r A M N t') {s' s : QState} {T' : List Item}
    (hsim : Sim t t' r M N s' s) (hstep : qstep t' s' = .done T') :
    ∃ k s₁ T, qiter t k s = some s₁ ∧ qstep t s₁ = .done T ∧
      List.Forall₂ (ItemSim t t' r M N) T' T := by
  obtain ⟨hpos, htape⟩ := qstep_done hstep
  cases hsim with
  | down hat => cases hpos
  | @up a' a T₁' T L' L hat =>
    cases hpos
    obtain ⟨ins, hloc, hT, hL, hlen⟩ := hat
    obtain ⟨k₀, a₁, L₁, hk₀, hroot, _⟩ := depart h hloc T hL
    obtain rfl := hroot rfl
    cases htape
    exact ⟨k₀, _, T, hk₀, by simp [qstep], hT⟩

/-- The machine has stopped with an empty tape: at a lambda, or on the way up from a
function. -/
inductive Starved (t : Term) : QState → Prop
  | lam {a : Addr} {A : Ty} {b : Term} {L : List Exit} : t.sub a = some (.lam A b) →
      Starved t ⟨.down a, [], L⟩
  | fn {a : Addr} {L : List Exit} : Starved t ⟨.up (.fn :: a), [], L⟩

/-- Where the run on the reduct stops with an empty tape, so does the run on `t`. -/
theorem sim_starved (h : Redex t r A M N t') {s' s : QState} (hsim : Sim t t' r M N s' s)
    (hst : Starved t' s') : ∃ k s₁, qiter t k s = some s₁ ∧ Starved t s₁ := by
  cases hst with
  | @lam a' A' b' L' hs'' =>
    cases hsim with
    | @down _ a _ T _ L hat =>
      obtain ⟨ins, hloc, hT, hL, hlen⟩ := hat
      obtain ⟨s₀, s₀', hs, hs', hlam, _⟩ := hloc.sub h
      rw [hs''] at hs'
      cases hs'
      obtain ⟨b₀, rfl⟩ := kind_lam (hlam A' rfl)
      cases hT
      exact ⟨0, _, rfl, .lam hs⟩
  | @fn p' L' =>
    cases hsim with
    | @up _ a _ T _ L hat =>
      obtain ⟨ins, hloc, hT, hL, hlen⟩ := hat
      obtain ⟨k₀, a₁, L₁, hk₀, _, hpar⟩ := depart h hloc T hL
      obtain ⟨p, insp, rfl, _, _⟩ := hpar .fn p' rfl
      cases hT
      exact ⟨k₀, _, hk₀, .fn⟩

/-! ## Runs -/

theorem qeval_of_qiter (t : Term) : ∀ (k m : Nat) (s s₁ : QState) (S : List Item),
    qiter t k s = some s₁ → qeval m t s₁ = some (some S) → qeval (k + m) t s = some (some S)
  | 0, m, s, s₁, S, h₁, h₂ => by
    simp only [qiter, Option.some.injEq] at h₁
    subst h₁
    simpa using h₂
  | k + 1, m, s, s₁, S, h₁, h₂ => by
    rw [show k + 1 + m = (k + m) + 1 by omega]
    simp only [qiter] at h₁
    simp only [qeval]
    cases hs : qstep t s with
    | next s' =>
      simp only [hs] at h₁ ⊢
      exact qeval_of_qiter t k m s' s₁ S h₁ h₂
    | done T => simp [hs] at h₁
    | stuck => simp [hs] at h₁

/-- A run on the reduct that reaches the root is followed by the run on `t`. -/
theorem sim_out (h : Redex t r A M N t') : ∀ (n : Nat) {s' s : QState} {S' : List Item},
    Sim t t' r M N s' s → qeval n t' s' = some (some S') →
      ∃ S, QOut t s S ∧ List.Forall₂ (ItemSim t t' r M N) S' S
  | 0, _, _, _, _, hq => by simp [qeval] at hq
  | n + 1, s', s, S', hsim, hq => by
    simp only [qeval] at hq
    cases hstep : qstep t' s' with
    | next s'' =>
      simp only [hstep] at hq
      obtain ⟨k, s₂, _, hk, hsim₂⟩ := sim_next h hsim hstep
      obtain ⟨S, ⟨m, hm⟩, hS⟩ := sim_out h n hsim₂ hq
      exact ⟨S, ⟨k + m, qeval_of_qiter t k m s s₂ S hk hm⟩, hS⟩
    | done T' =>
      simp only [hstep, Option.some.injEq] at hq
      subst hq
      obtain ⟨k, s₁, T, hk, hd, hT⟩ := sim_done h hsim hstep
      exact ⟨T, ⟨k + 1, qeval_of_qiter t k 1 s s₁ T hk (by simp [qeval, hd])⟩, hT⟩
    | stuck => simp [hstep] at hq

/-- From the root of `t`, the machine gets to the state that the root of the reduct stands
for. -/
theorem sim_root (h : Redex t r A M N t') {T' T : List Item}
    (hT : List.Forall₂ (ItemSim t t' r M N) T' T) :
    ∃ k s, qiter t k ⟨.down [], T, []⟩ = some s ∧ Sim t t' r M N ⟨.down [], T', []⟩ s := by
  by_cases hr : r = []
  · subst hr
    have h2 := enter_body h T []
    by_cases hk : M.kind = .var 0
    · obtain ⟨π, rfl⟩ := kind_var hk
      have hs : (Term.var 0 π).sub [] = some (.var (bodies []) π) := rfl
      have h3 := enter_copy h hs T []
      exact ⟨4, _, qiter_add t 2 2 _ _ _ h2 h3,
        .down ⟨_, Loc.copy (n := []) hs rfl, hT, ⟨[], .nil, rfl⟩, rfl⟩⟩
    · exact ⟨2, _, h2, .down ⟨_, Loc.body (e := []) rfl (by simpa using hk), hT, .nil, rfl⟩⟩
  · refine ⟨0, _, rfl, .down ⟨none, Loc.out (fun hs => hr (List.suffix_nil.mp hs)) rfl, hT,
      .nil, rfl⟩⟩

/-- The simulation for runs from the root: if the machine on the reduct reaches the root
again, so does the machine on `t`, and the tapes at the end are related. -/
theorem beta_out (h : Redex t r A M N t') {T' T S' : List Item}
    (hT : List.Forall₂ (ItemSim t t' r M N) T' T) (hq : QOut t' ⟨.down [], T', []⟩ S') :
    ∃ S, QOut t ⟨.down [], T, []⟩ S ∧ List.Forall₂ (ItemSim t t' r M N) S' S := by
  obtain ⟨n, hn⟩ := hq
  obtain ⟨k, s, hk, hsim⟩ := sim_root h hT
  obtain ⟨S, ⟨m, hm⟩, hS⟩ := sim_out h n hsim hn
  exact ⟨S, ⟨k + m, qeval_of_qiter t k m _ s S hk hm⟩, hS⟩

/-- The run stops with an empty tape. -/
def QStarved (t : Term) (s : QState) : Prop :=
  ∃ k s₁, qiter t k s = some s₁ ∧ Starved t s₁

theorem sim_starved_run (h : Redex t r A M N t') : ∀ (k : Nat) {s' s s₁' : QState},
    Sim t t' r M N s' s → qiter t' k s' = some s₁' → Starved t' s₁' → QStarved t s
  | 0, s', s, s₁', hsim, hk, hst => by
    simp only [qiter, Option.some.injEq] at hk
    subst hk
    exact sim_starved h hsim hst
  | k + 1, s', s, s₁', hsim, hk, hst => by
    simp only [qiter] at hk
    cases hstep : qstep t' s' with
    | next s'' =>
      simp only [hstep] at hk
      obtain ⟨j, s₂, _, hj, hsim₂⟩ := sim_next h hsim hstep
      obtain ⟨m, s₃, hm, hst₃⟩ := sim_starved_run h k hsim₂ hk hst
      exact ⟨j + m, s₃, qiter_add t j m _ _ _ hj hm, hst₃⟩
    | done T => simp [hstep] at hk
    | stuck => simp [hstep] at hk

/-- If the run on the reduct from the root stops with an empty tape, so does the run on
`t` from the related tape. -/
theorem beta_starved (h : Redex t r A M N t') {T' T : List Item}
    (hT : List.Forall₂ (ItemSim t t' r M N) T' T) (hq : QStarved t' ⟨.down [], T', []⟩) :
    QStarved t ⟨.down [], T, []⟩ := by
  obtain ⟨n, s₁', hn, hst⟩ := hq
  obtain ⟨k, s, hk, hsim⟩ := sim_root h hT
  obtain ⟨m, s₃, hm, hst₃⟩ := sim_starved_run h n hsim hn hst
  exact ⟨k + m, s₃, qiter_add t k m _ _ _ hk hm, hst₃⟩

theorem itemSim_side {x' x : Item} (hx : ItemSim t t' r M N x' x) : x'.side = x.side := by
  cases hx <;> rfl

/-- Related tapes have the same sides. -/
theorem sides_eq : ∀ {T' T : List Item}, List.Forall₂ (ItemSim t t' r M N) T' T →
    T'.map Item.side = T.map Item.side
  | _, _, .nil => rfl
  | _, _, .cons hx hT => by simp [itemSim_side hx, sides_eq hT]

theorem itemSim_qs (n : Nat) :
    List.Forall₂ (ItemSim t t' r M N) (List.replicate n .q) (List.replicate n .q) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons .q ih

/-- The first run: if it reaches the root on the reduct, it does on `t`, with the same
sides on the tape. -/
theorem beta_first (h : Redex t r A M N t') {n : Nat} {S' : List Item}
    (hq : QOut t' ⟨.down [], List.replicate n .q, []⟩ S') :
    ∃ S, QOut t ⟨.down [], List.replicate n .q, []⟩ S ∧
      S'.map Item.side = S.map Item.side := by
  obtain ⟨S, hS, hrel⟩ := beta_out h (itemSim_qs n) hq
  exact ⟨S, hS, sides_eq hrel⟩

end

end LSL
