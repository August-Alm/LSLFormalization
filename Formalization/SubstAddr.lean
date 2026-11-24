import Formalization.PointerReadback

/-!
# Addresses in a reduct

For the redex `(λ M) N` at the address `r` of `t` and its reduct `t'` (`Redex`), the subterm
of `t'` at an address is given in terms of `t`:

* outside the redex, it is of the same kind as in `t` (`Redex.kind_outside`);
* at the address `e` of `M`, it is the subterm of `M` with `N` substituted (`Redex.sub_body'`);
* at the address `n` in the copy of `N` at the occurrence `e` of the variable, it is the
  subterm of `N`, shifted (`Redex.sub_copy'`).

This is the first part of the proof that the pointer machine on `t` follows the machine on
`t'`. The simulation itself is not proved yet; it is tested by `checkRun`.
-/

namespace LSL

/-- The number of lambdas on the way to the address. -/
def bodies (e : Addr) : Nat := e.count .body

@[simp] theorem bodies_nil : bodies [] = 0 := rfl

@[simp] theorem bodies_body (e : Addr) : bodies (.body :: e) = bodies e + 1 := by
  simp [bodies]

@[simp] theorem bodies_fn (e : Addr) : bodies (.fn :: e) = bodies e := by
  simp [bodies]

@[simp] theorem bodies_arg (e : Addr) : bodies (.arg :: e) = bodies e := by
  simp [bodies]

theorem bodies_append (e a : Addr) : bodies (e ++ a) = bodies e + bodies a := by
  simp [bodies]

/-- A variable whose index is at least the number of lambdas on the way is free there. -/
theorem binder_ge : ∀ (e : Addr) (i : Nat), bodies e ≤ i → binder e i = .inl (i - bodies e)
  | [], i, _ => by simp [binder]
  | .body :: e, 0, h => by simp at h
  | .body :: e, i + 1, h => by
    simp only [binder, bodies_body] at h ⊢
    rw [binder_ge e i (by omega)]
    congr 1
    omega
  | .fn :: e, i, h => by simpa [binder] using binder_ge e i (by simpa using h)
  | .arg :: e, i, h => by simpa [binder] using binder_ge e i (by simpa using h)

theorem binder_lt : ∀ (e : Addr) (i : Nat), i < bodies e → ∃ b, binder e i = .inr b
  | [], i, h => by simp at h
  | .body :: e, 0, _ => ⟨e, rfl⟩
  | .body :: e, i + 1, h => by simpa [binder] using binder_lt e i (by simpa using h)
  | .fn :: e, i, h => by simpa [binder] using binder_lt e i (by simpa using h)
  | .arg :: e, i, h => by simpa [binder] using binder_lt e i (by simpa using h)

/-! ## Subterms of shifted, grafted and substituted terms -/

theorem child_shift (d c : Nat) (dir : Dir) : ∀ s : Term,
    (shift d c s).child dir = (s.child dir).map (shift d (c + if dir = .body then 1 else 0))
  | .var i π => by
    simp only [shift]
    split <;> cases dir <;> simp [Term.child]
  | .lam A b => by cases dir <;> simp [shift, Term.child]
  | .app f u => by cases dir <;> simp [shift, Term.child]

theorem sub_shift (d : Nat) : ∀ (n : Addr) (c : Nat) (s : Term),
    (shift d c s).sub n = (s.sub n).map (shift d (c + bodies n))
  | [], c, s => by simp [Term.sub]
  | dir :: n, c, s => by
    rw [sub_cons, sub_cons, sub_shift d n c s]
    cases h : s.sub n with
    | none => simp
    | some s₀ =>
      simp only [Option.map_some, Option.bind_some, child_shift]
      cases dir <;> simp [Nat.add_assoc]

theorem child_graft (π : Path) (c : Nat) (dir : Dir) : ∀ s : Term,
    (graft π c s).child dir = (s.child dir).map (graft π (c + if dir = .body then 1 else 0))
  | .var i ρ => by
    simp only [graft]
    split <;> cases dir <;> simp [Term.child]
  | .lam A b => by cases dir <;> simp [graft, Term.child]
  | .app f u => by cases dir <;> simp [graft, Term.child]

theorem sub_graft (π : Path) : ∀ (n : Addr) (c : Nat) (s : Term),
    (graft π c s).sub n = (s.sub n).map (graft π (c + bodies n))
  | [], c, s => by simp [Term.sub]
  | dir :: n, c, s => by
    rw [sub_cons, sub_cons, sub_graft π n c s]
    cases h : s.sub n with
    | none => simp
    | some s₀ =>
      simp only [Option.map_some, Option.bind_some, child_graft]
      cases dir <;> simp [Nat.add_assoc]

/-- Above the occurrences of the variable, substitution acts on the subterms. -/
theorem sub_subst (N : Term) : ∀ (e : Addr) (M : Term) (j : Nat) (s : Term), M.sub e = some s →
    (subst j N M).sub e = some (subst (j + bodies e) N s)
  | [], M, j, s, h => by
    simp only [Term.sub, List.foldr_nil, Option.some.injEq] at h
    subst h
    simp [Term.sub]
  | dir :: e, M, j, s, h => by
    rw [sub_cons] at h ⊢
    cases h₀ : M.sub e with
    | none => simp [h₀] at h
    | some s₀ =>
      rw [h₀] at h
      rw [sub_subst N e M j s₀ h₀]
      cases s₀ with
      | var i π => cases dir <;> simp [Term.child] at h
      | lam A b =>
        cases dir with
        | body =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at h
          subst h
          simp [subst, Term.child, Nat.add_assoc]
        | fn => simp [Term.child] at h
        | arg => simp [Term.child] at h
      | app f u =>
        cases dir with
        | body => simp [Term.child] at h
        | fn =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at h
          subst h
          simp [subst, Term.child]
        | arg =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at h
          subst h
          simp [subst, Term.child]

/-! ## The kind of a subterm -/

inductive Kind where
  | var (i : Nat)
  | lam (A : Ty)
  | app
  deriving DecidableEq

def Term.kind : Term → Kind
  | .var i _ => .var i
  | .lam A _ => .lam A
  | .app _ _ => .app

/-- What the machine sees of the term at an address. -/
def kindAt (t : Term) (a : Addr) : Option Kind := (t.sub a).map Term.kind

theorem kind_graft (π : Path) (c : Nat) : ∀ s : Term, (graft π c s).kind = s.kind
  | .var i ρ => by
    simp only [graft]
    split <;> rfl
  | .lam _ _ => rfl
  | .app _ _ => rfl

theorem kind_shift (d c : Nat) : ∀ s : Term, (shift d c s).kind =
    match s.kind with
    | .var i => .var (if i < c then i else i + d)
    | k => k
  | .var i π => by by_cases h : i < c <;> simp [shift, Term.kind, h]
  | .lam _ _ => rfl
  | .app _ _ => rfl

/-- Substitution keeps the kind of a term that is not the variable. -/
theorem kind_subst (N : Term) (k : Nat) : ∀ s : Term, s.kind ≠ .var k → (subst k N s).kind =
    match s.kind with
    | .var i => .var (if i < k then i else i - 1)
    | x => x
  | .var i π, h => by
    have hik : i ≠ k := fun e => h (by rw [e]; rfl)
    by_cases hlt : i < k
    · simp [subst, Term.kind, hlt]
    · simp [subst, Term.kind, hlt, hik]
  | .lam _ _, _ => rfl
  | .app _ _, _ => rfl

/-! ## Contracting a redex -/

theorem contractAt_sub : ∀ (ρ : List Dir) (t t' : Term) {A : Ty} {M N : Term},
    contractAt t ρ = some t' → t.sub ρ.reverse = some (.app (.lam A M) N) →
      ∀ e : Addr, t'.sub (e ++ ρ.reverse) = (subst 0 N M).sub e
  | [], t, t', A, M, N, hc, hs, e => by
    simp only [List.reverse_nil, Term.sub, List.foldr_nil, Option.some.injEq] at hs
    subst hs
    simp only [contractAt, Option.some.injEq] at hc
    subst hc
    simp
  | d :: ρ, t, t', A, M, N, hc, hs, e => by
    rw [List.reverse_cons, sub_append] at hs
    rw [List.reverse_cons, ← List.append_assoc, sub_append]
    cases t with
    | var i π => simp [contractAt] at hc
    | lam B b =>
      cases d with
      | body =>
        cases hb : contractAt b ρ with
        | none => simp [contractAt, hb] at hc
        | some b' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          have hs' : b.sub ρ.reverse = some (.app (.lam A M) N) := by
            simpa [Term.sub, Term.child] using hs
          have := contractAt_sub ρ b b' hb hs' e
          simpa [Term.sub, Term.child] using this
      | fn => simp [contractAt] at hc
      | arg => simp [contractAt] at hc
    | app f u =>
      cases d with
      | body => simp [contractAt] at hc
      | fn =>
        cases hb : contractAt f ρ with
        | none => simp [contractAt, hb] at hc
        | some f' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          have hs' : f.sub ρ.reverse = some (.app (.lam A M) N) := by
            simpa [Term.sub, Term.child] using hs
          have := contractAt_sub ρ f f' hb hs' e
          simpa [Term.sub, Term.child] using this
      | arg =>
        cases hb : contractAt u ρ with
        | none => simp [contractAt, hb] at hc
        | some u' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          have hs' : u.sub ρ.reverse = some (.app (.lam A M) N) := by
            simpa [Term.sub, Term.child] using hs
          have := contractAt_sub ρ u u' hb hs' e
          simpa [Term.sub, Term.child] using this

/-- Away from the redex, the reduct has subterms of the same kinds. -/
theorem contractAt_kind : ∀ (ρ α : List Dir) (t t' : Term), contractAt t ρ = some t' →
    ¬ ρ <+: α → (t'.sub α.reverse).map Term.kind = (t.sub α.reverse).map Term.kind
  | [], α, _, _, _, h => absurd (List.nil_prefix) h
  | d :: ρ, [], t, t', hc, _ => by
    cases t with
    | var i π => simp [contractAt] at hc
    | lam B b =>
      cases d with
      | body =>
        cases hb : contractAt b ρ with
        | none => simp [contractAt, hb] at hc
        | some b' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          simp [Term.sub, Term.kind]
      | fn => simp [contractAt] at hc
      | arg => simp [contractAt] at hc
    | app f u =>
      cases d with
      | body => simp [contractAt] at hc
      | fn =>
        cases hb : contractAt f ρ with
        | none => simp [contractAt, hb] at hc
        | some f' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          simp [Term.sub, Term.kind]
      | arg =>
        cases hb : contractAt u ρ with
        | none => simp [contractAt, hb] at hc
        | some u' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          simp [Term.sub, Term.kind]
  | d :: ρ, d' :: α, t, t', hc, h => by
    have hpre : d = d' → ¬ ρ <+: α := fun e hp => h (by rw [e]; exact List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
    rw [List.reverse_cons, sub_append, sub_append]
    cases t with
    | var i π => simp [contractAt] at hc
    | lam B b =>
      cases d with
      | body =>
        cases hb : contractAt b ρ with
        | none => simp [contractAt, hb] at hc
        | some b' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          cases d' with
          | body => simpa [Term.sub, Term.child] using contractAt_kind ρ α b b' hb (hpre rfl)
          | fn => simp [Term.sub, Term.child]
          | arg => simp [Term.sub, Term.child]
      | fn => simp [contractAt] at hc
      | arg => simp [contractAt] at hc
    | app f u =>
      cases d with
      | body => simp [contractAt] at hc
      | fn =>
        cases hb : contractAt f ρ with
        | none => simp [contractAt, hb] at hc
        | some f' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          cases d' with
          | body => simp [Term.sub, Term.child]
          | fn => simpa [Term.sub, Term.child] using contractAt_kind ρ α f f' hb (hpre rfl)
          | arg => simp [Term.sub, Term.child]
      | arg =>
        cases hb : contractAt u ρ with
        | none => simp [contractAt, hb] at hc
        | some u' =>
          simp only [contractAt, hb, Option.map_some, Option.some.injEq] at hc
          subst hc
          cases d' with
          | body => simp [Term.sub, Term.child]
          | fn => simp [Term.sub, Term.child]
          | arg => simpa [Term.sub, Term.child] using contractAt_kind ρ α u u' hb (hpre rfl)

/-- The redex `(λ M) N` at the address `r` of `t`, and its reduct `t'`. -/
structure Redex (t : Term) (r : Addr) (A : Ty) (M N : Term) (t' : Term) : Prop where
  sub : t.sub r = some (.app (.lam A M) N)
  con : contractAt t r.reverse = some t'

namespace Redex

variable {t : Term} {r : Addr} {A : Ty} {M N : Term} {t' : Term}

theorem sub_body (h : Redex t r A M N t') (e : Addr) :
    t.sub (e ++ .body :: .fn :: r) = M.sub e := by
  rw [sub_append, sub_cons, sub_cons, h.sub]
  rfl

theorem sub_arg (h : Redex t r A M N t') (n : Addr) : t.sub (n ++ .arg :: r) = N.sub n := by
  rw [sub_append, sub_cons, h.sub]
  rfl

theorem sub_reduct (h : Redex t r A M N t') (e : Addr) :
    t'.sub (e ++ r) = (subst 0 N M).sub e := by
  have := contractAt_sub r.reverse t t' h.con (by rw [List.reverse_reverse]; exact h.sub) e
  rwa [List.reverse_reverse] at this

/-- Outside the redex, the reduct looks like the term. -/
theorem kind_outside (h : Redex t r A M N t') {a : Addr} (ha : ¬ r <:+ a) :
    kindAt t' a = kindAt t a := by
  have := contractAt_kind r.reverse a.reverse t t' h.con (by rwa [List.reverse_prefix])
  rwa [List.reverse_reverse] at this

/-- In the reduct, a place of `M` has `N` substituted. -/
theorem sub_body' (h : Redex t r A M N t') {e : Addr} {s : Term} (hs : M.sub e = some s) :
    t'.sub (e ++ r) = some (subst (bodies e) N s) := by
  rw [h.sub_reduct, sub_subst N e M 0 s hs, Nat.zero_add]

/-- In the reduct, a place of the copy of `N` at an occurrence of the variable has the
subterm of `N`, shifted by the lambdas of `M` around the occurrence. -/
theorem sub_copy' (h : Redex t r A M N t') {e : Addr} {π : Path}
    (hs : M.sub e = some (.var (bodies e) π)) (n : Addr) :
    t'.sub (n ++ e ++ r) =
      (N.sub n).map fun s => graft π (bodies n) (shift (bodies e) (bodies n) s) := by
  rw [h.sub_reduct, sub_append, sub_subst N e M 0 _ hs, Nat.zero_add]
  simp only [Option.bind_some, subst, Nat.lt_irrefl, ite_false, ite_true, sub_graft, sub_shift,
    Nat.zero_add, Option.map_map]
  rfl

end Redex

end LSL
