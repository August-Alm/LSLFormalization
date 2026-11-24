import Formalization.BetaStep

/-!
# Readback with the pointer machine, along a reduction

`QReads` is readback with the pointer machine, stated so that it can be carried backwards
along a beta step with the simulation of `BetaStep.lean`:

* a variable is resolved by the sides of the tape, as in `Reads`, because two exits of the
  reduct can stand for the same exit of the term;
* for a smaller number of lambdas the machine must stop with an empty tape, because that is
  the only way of stopping that the simulation carries over;
* the head variable has a type with at least as many arguments as the head is applied to.

`qreads_steps`: what a reduct reads back as, the term reads back as.
-/

namespace LSL

/-- The machine gets from `s` to `s'`. -/
def QR (t : Term) (s s' : QState) : Prop := ∃ k, qiter t k s = some s'

theorem QR.refl (t : Term) (s : QState) : QR t s s := ⟨0, rfl⟩

theorem QR.trans {t : Term} {s₁ s₂ s₃ : QState} (h₁ : QR t s₁ s₂) (h₂ : QR t s₂ s₃) :
    QR t s₁ s₃ := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  exact ⟨j + k, qiter_add t j k _ _ _ hj hk⟩

theorem QR.one {t : Term} {s s' : QState} (h : qstep t s = .next s') : QR t s s' :=
  ⟨1, by simp [qiter, h]⟩

theorem QR.out {t : Term} {s s' : QState} {S : List Item} (h : QR t s s')
    (hd : qstep t s' = .done S) : QOut t s S := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, qeval_of_qiter t k 1 s s' S hk (by simp [qeval, hd])⟩

theorem QR.starved {t : Term} {s s' : QState} (h : QR t s s') (hs : Starved t s') :
    QStarved t s := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, s', hk, hs⟩

/-- `QReads t anc U u`: the point with tape `U` of `t`, inside the points `anc` (innermost
first), reads back as `u` with the pointer machine. -/
inductive QReads (t : Term) : List Frame → List Item → Tm → Prop
  | node {anc : List Frame} {U V : List Item} {n l m x : Nat} {e : Exit} {A : Ty}
      {args : List Tm} :
      QOut t ⟨.down [], U ++ List.replicate n .q, []⟩
        (V ++ List.replicate l .q ++ .p e :: List.replicate m .q) →
      (∀ k, k < n → QStarved t ⟨.down [], U ++ List.replicate k .q, []⟩) →
      dropQ (V.map Item.side).reverse = (0, (V.map Item.side).reverse) →
      resolve (⟨U.map Item.side, n⟩ :: anc) (V.map Item.side) l = some x →
      varTy t e.occ = some A → m ≤ A.arity →
      args.length = m →
      (∀ (i : Nat) (a : Tm), args[i]? = some a →
        QReads t (⟨U.map Item.side, n⟩ :: anc) (childTape V l e i) a) →
      QReads t anc U (Tm.lams n (Tm.apps (.var x) args))

theorem childTape_sides (V : List Item) (l : Nat) (e : Exit) (i : Nat) :
    (childTape V l e i).map Item.side = childAddr (V.map Item.side) l i := by
  simp [childTape, childAddr, Item.side]

/-! ## A beta step -/

theorem fa2_split {α β : Type} {R : α → β → Prop} : ∀ {l₁ l₃ : List α} {l : List β},
    List.Forall₂ R (l₁ ++ l₃) l →
      ∃ l₂ l₄, l = l₂ ++ l₄ ∧ List.Forall₂ R l₁ l₂ ∧ List.Forall₂ R l₃ l₄
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | a :: l₁, l₃, _, h => by
    rw [List.cons_append] at h
    cases h with
    | cons h₁ h₂ =>
      obtain ⟨l₂, l₄, rfl, h₃, h₄⟩ := fa2_split h₂
      exact ⟨_ :: l₂, l₄, rfl, .cons h₁ h₃, h₄⟩

section

variable {t : Term} {r : Addr} {A : Ty} {M N : Term} {t' : Term}

theorem itemSim_qs_eq : ∀ {n : Nat} {Q : List Item},
    List.Forall₂ (ItemSim t t' r M N) (List.replicate n .q) Q → Q = List.replicate n .q
  | 0, _, h => by
    rw [List.replicate_zero] at h
    cases h
    rfl
  | n + 1, _, h => by
    rw [List.replicate_succ] at h
    cases h with
    | cons hx hT =>
      cases hx
      rw [itemSim_qs_eq hT, List.replicate_succ]

/-- A variable of the reduct has the type of the variable of `t` that it stands for. -/
theorem loc_varTy (h : Redex t r A M N t') {o' o : Addr} {ins : Option (Nat × Addr)}
    (hlo : Loc t r M N o' o ins) {B : Ty} (hv : varTy t' o' = some B) : varTy t o = some B := by
  cases hbo : binderOf t' o' with
  | none => simp [varTy, hbo] at hv
  | some b' =>
    obtain ⟨i', π', hs', hb'⟩ := binderOf_some hbo
    obtain ⟨i, π, b, insb, hst, hbt, hlocb, _⟩ := hlo.lambda h hs' hb'
    obtain ⟨s, s', hs, hs'', hlam, _⟩ := hlocb.sub h
    simp only [varTy, hbo, Option.bind_some, hs''] at hv
    cases s' with
    | var _ _ => simp at hv
    | lam A₁ x =>
      simp only [Option.some.injEq] at hv
      subst hv
      obtain ⟨y, rfl⟩ := kind_lam (hlam _ rfl)
      simp [varTy, binderOf, hst, hbt, hs]
    | app _ _ => simp at hv

theorem exitSim_varTy (h : Redex t r A M N t') {e' e : Exit} (he : ExitSim t t' r M N e' e)
    {B : Ty} (hv : varTy t' e'.occ = some B) : varTy t e.occ = some B := by
  cases he with
  | dummy =>
    rw [varTy_outside] at hv
    cases hv
  | plain hlo _ _ _ => exact loc_varTy h hlo hv
  | inner hlo _ _ _ _ => exact loc_varTy h hlo hv
  | outer hlo _ _ _ _ => exact loc_varTy h hlo hv

/-- What a point of the reduct reads back as, the point of `t` with the tape that it stands
for reads back as. -/
theorem qreads_beta (h : Redex t r A M N t') {anc : List Frame} {U' : List Item} {u : Tm}
    (hq : QReads t' anc U' u) :
    ∀ U : List Item, List.Forall₂ (ItemSim t t' r M N) U' U → QReads t anc U u := by
  induction hq with
  | @node anc U' V' n l m x e' B args hout hmin hV hres hvt har hlen _ ih =>
    intro U hU
    obtain ⟨S, hS, hrel⟩ := beta_out h (fa2_append hU (itemSim_qs n)) hout
    obtain ⟨W, X, rfl, hW, hX⟩ := fa2_split hrel
    obtain ⟨V, Q, rfl, hVV, hQ⟩ := fa2_split hW
    obtain rfl := itemSim_qs_eq hQ
    cases hX with
    | cons hx hX' =>
      cases hx with
      | p he =>
        obtain rfl := itemSim_qs_eq hX'
        have hsU := sides_eq hU
        have hsV := sides_eq hVV
        refine QReads.node hS
          (fun k hk => beta_starved h (fa2_append hU (itemSim_qs k)) (hmin k hk))
          (by rw [← hsV]; exact hV) (by rw [← hsU, ← hsV]; exact hres)
          (exitSim_varTy h he hvt) har hlen fun i a hi => ?_
        rw [← hsU]
        exact ih i a hi _ (fa2_append (fa2_append hVV (itemSim_qs l))
          (.cons (.p he) (fa2_append (itemSim_qs i) (.cons (.p .dummy) .nil))))

end

/-! ## A reduction -/

/-- A step contracts a redex at some address. -/
theorem redex_of_step {t t' : Term} (h : Step t t') : ∃ r A M N, Redex t r A M N t' := by
  induction h with
  | @beta A b u => exact ⟨[], A, b, u, ⟨rfl, by simp [contractAt]⟩⟩
  | @lam B s s' _ ih =>
    obtain ⟨r, A, M, N, hsub, hcon⟩ := ih
    refine ⟨r ++ [.body], A, M, N, ⟨?_, ?_⟩⟩
    · rw [sub_append]
      simpa [Term.sub, Term.child] using hsub
    · simp [contractAt, hcon]
  | @appL s s' u _ ih =>
    obtain ⟨r, A, M, N, hsub, hcon⟩ := ih
    refine ⟨r ++ [.fn], A, M, N, ⟨?_, ?_⟩⟩
    · rw [sub_append]
      simpa [Term.sub, Term.child] using hsub
    · simp [contractAt, hcon]
  | @appR s u u' _ ih =>
    obtain ⟨r, A, M, N, hsub, hcon⟩ := ih
    refine ⟨r ++ [.arg], A, M, N, ⟨?_, ?_⟩⟩
    · rw [sub_append]
      simpa [Term.sub, Term.child] using hsub
    · simp [contractAt, hcon]

/-- What a reduct reads back as, the term reads back as. -/
theorem qreads_steps {t v : Term} (hs : Steps t v) {u : Tm} (hq : QReads v [] [] u) :
    QReads t [] [] u := by
  induction hs with
  | refl => exact hq
  | tail _ hst ih =>
    obtain ⟨r, A, M, N, hr⟩ := redex_of_step hst
    exact ih (qreads_beta hr hq [] .nil)

end LSL
