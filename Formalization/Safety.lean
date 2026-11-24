import Formalization.Sharing

/-!
# Local safety is preserved by beta reduction

`Step.safe` is subject reduction for `LS`. Outside all arguments it needs a context without
local variables: with `y : o` local and `f` global, `(λx. f (λz. x)) y` is safe outside an
argument, but its reduct `f (λz. y)` is not.
-/

namespace LSL

/-! ## Comparing contexts -/

def hideBind (n : Nat) (b : Bind) : Bind :=
  if b.zone = .loc ∧ b.ty.order < n then { b with zone := .hid } else b

theorem hide_eq (n : Nat) (Γ : List Bind) : hide n Γ = Γ.map (hideBind n) := rfl

theorem getElem?_hide (n : Nat) (Γ : List Bind) (i : Nat) :
    (hide n Γ)[i]? = (Γ[i]?).map (hideBind n) := by
  rw [hide_eq, List.getElem?_map]

theorem hideBind_visible {n : Nat} {b : Bind} (h : (hideBind n b).zone ≠ .hid) :
    hideBind n b = b ∧ (b.zone = .loc → n ≤ b.ty.order) := by
  unfold hideBind at h ⊢
  split
  · rename_i hc
    simp [hc] at h
  · rename_i hc
    exact ⟨rfl, fun hl => Nat.le_of_not_lt fun hlt => hc ⟨hl, hlt⟩⟩

theorem hideBind_keep {n : Nat} {b : Bind} (h : b.zone = .loc → n ≤ b.ty.order) :
    hideBind n b = b := by
  unfold hideBind
  split
  · rename_i hc
    exact absurd hc.2 (Nat.not_lt.mpr (h hc.1))
  · rfl

/-- `b'` can be used wherever `b` can. -/
def Bind.le (b b' : Bind) : Prop :=
  b.zone = .hid ∨ (b'.ty = b.ty ∧ (b'.zone = b.zone ∨ b'.zone = .glob))

theorem Bind.le_refl (b : Bind) : b.le b := .inr ⟨rfl, .inl rfl⟩

theorem le_hideBind {n : Nat} {b b' : Bind} (h : b.le b')
    (hord : b.zone = .loc → n ≤ b.ty.order) : b.le (hideBind n b') := by
  rcases h with h | ⟨hty, hz⟩
  · exact .inl h
  · have hkeep : hideBind n b' = b' := by
      apply hideBind_keep
      intro hl
      rcases hz with hz | hz
      · rw [hty]
        exact hord (hz ▸ hl)
      · rw [hz] at hl
        cases hl
    rw [hkeep]
    exact .inr ⟨hty, hz⟩

theorem hideBind_le (n : Nat) (b : Bind) : (hideBind n b).le b := by
  by_cases hv : (hideBind n b).zone = .hid
  · exact .inl hv
  · rw [(hideBind_visible hv).1]
    exact Bind.le_refl b

theorem hideBind_mono {n : Nat} {b b' : Bind} (h : b.le b') :
    (hideBind n b).le (hideBind n b') := by
  by_cases hv : (hideBind n b).zone = .hid
  · exact .inl hv
  · obtain ⟨he, hord⟩ := hideBind_visible hv
    rw [he]
    exact le_hideBind h hord

/-! ## Shifting and grafting -/

/-- Shifting keeps a term safe, also when it moves out of an argument. -/
theorem shift_safe {m : Bool} {Γ : List Bind} {t : Term} {A : Ty} (h : LS m Γ t A) :
    ∀ (m' : Bool) (Γ' : List Bind) (d c : Nat), (m = false → m' = false) →
      (∀ i b, Γ[i]? = some b → ∃ b', Γ'[if i < c then i else i + d]? = some b' ∧ b.le b') →
      LS m' Γ' (shift d c t) A := by
  induction h with
  | @var m Γ i π b hb hz =>
    intro m' Γ' d c _ hΓ
    obtain ⟨b', hb', hle⟩ := hΓ i b hb
    rcases hle with hle | ⟨hty, hzone⟩
    · exact absurd hle hz
    · have hz' : b'.zone ≠ .hid := by
        rcases hzone with h | h
        · rw [h]
          exact hz
        · rw [h]
          decide
      rw [← hty]
      by_cases hic : i < c
      · simp only [shift, hic, ite_true] at hb' ⊢
        exact LS.var hb' hz'
      · simp only [shift, hic, ite_false] at hb' ⊢
        exact LS.var hb' hz'
  | @lam m Γ A B t _ ih =>
    intro m' Γ' d c hm hΓ
    simp only [shift]
    refine LS.lam (ih m' _ d (c + 1) hm ?_)
    intro i b hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      refine ⟨⟨A, zoneOf m'⟩, by simp, ?_⟩
      cases m with
      | true =>
        cases m' with
        | true => exact Bind.le_refl _
        | false => exact .inr ⟨rfl, .inr rfl⟩
      | false =>
        rw [hm rfl]
        exact Bind.le_refl _
    | succ k =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨b', hb', hle⟩ := hΓ k b hb
      refine ⟨b', ?_, hle⟩
      by_cases hk : k < c
      · simp only [hk, ite_true] at hb'
        simp only [Nat.add_lt_add_iff_right, hk, ite_true, List.getElem?_cons_succ]
        exact hb'
      · simp only [hk, ite_false] at hb'
        simp only [Nat.add_lt_add_iff_right, hk, ite_false]
        rw [show k + 1 + d = (k + d) + 1 by omega, List.getElem?_cons_succ]
        exact hb'
  | @app m Γ A B t u _ _ iht ihu =>
    intro m' Γ' d c hm hΓ
    simp only [shift]
    refine LS.app (iht m' Γ' d c hm hΓ) (ihu true _ d c (fun h => h) ?_)
    intro i b hb
    rw [getElem?_hide] at hb
    cases hb0 : Γ[i]? with
    | none => simp [hb0] at hb
    | some b0 =>
      simp only [hb0, Option.map_some, Option.some.injEq] at hb
      subst hb
      obtain ⟨b', hb', hle⟩ := hΓ i b0 hb0
      exact ⟨hideBind A.order b', by rw [getElem?_hide, hb']; rfl, hideBind_mono hle⟩

theorem graft_safe {m : Bool} {Γ : List Bind} {t : Term} {A : Ty} (π : Path)
    (h : LS m Γ t A) : ∀ c : Nat, LS m Γ (graft π c t) A := by
  induction h with
  | var hb hz =>
    intro c
    simp only [graft]
    split <;> exact LS.var hb hz
  | lam _ ih =>
    intro c
    simp only [graft]
    exact LS.lam (ih (c + 1))
  | app _ _ iht ihu =>
    intro c
    simp only [graft]
    exact LS.app (iht c) (ihu c)

/-! ## Substitution -/

/-- `Γ'` is `Γ` without entry `j`, and a term that is safe in `Γu` can stand in `Γ'` for
variable `j` wherever that variable is visible. -/
structure SubstCtx (Γu : List Bind) (A : Ty) (j : Nat) (Γ Γ' : List Bind) : Prop where
  below : ∀ i, i < j → Γ'[i]? = Γ[i]?
  above : ∀ i, j ≤ i → Γ'[i]? = Γ[i + 1]?
  here : ∀ b, Γ[j]? = some b → b.zone ≠ .hid →
    b.ty = A ∧ (∀ (i : Nat) (c : Bind), Γu[i]? = some c → ∃ c', Γ'[i + j]? = some c' ∧ c.le c') ∧
      (∀ (i : Nat) (c : Bind), Γu[i]? = some c → c.zone = .loc →
        b.zone = .loc ∧ A.order ≤ c.ty.order)

theorem SubstCtx.under_lam {Γu : List Bind} {A : Ty} {j : Nat} {Γ Γ' : List Bind}
    (x : Bind) (h : SubstCtx Γu A j Γ Γ') : SubstCtx Γu A (j + 1) (x :: Γ) (x :: Γ') where
  below := fun i hi => by
    cases i with
    | zero => rfl
    | succ k =>
      simp only [List.getElem?_cons_succ]
      exact h.below k (by omega)
  above := fun i hi => by
    cases i with
    | zero => omega
    | succ k =>
      simp only [List.getElem?_cons_succ]
      exact h.above k (by omega)
  here := fun b hb hz => by
    simp only [List.getElem?_cons_succ] at hb
    obtain ⟨hty, hu, hloc⟩ := h.here b hb hz
    refine ⟨hty, fun i c hc => ?_, hloc⟩
    obtain ⟨c', hc', hle⟩ := hu i c hc
    refine ⟨c', ?_, hle⟩
    rw [show i + (j + 1) = (i + j) + 1 by omega, List.getElem?_cons_succ]
    exact hc'

theorem SubstCtx.under_arg {Γu : List Bind} {A : Ty} {j : Nat} {Γ Γ' : List Bind}
    (n : Nat) (h : SubstCtx Γu A j Γ Γ') : SubstCtx Γu A j (hide n Γ) (hide n Γ') where
  below := fun i hi => by rw [getElem?_hide, getElem?_hide, h.below i hi]
  above := fun i hi => by rw [getElem?_hide, getElem?_hide, h.above i hi]
  here := fun b hb hz => by
    rw [getElem?_hide] at hb
    cases hb0 : Γ[j]? with
    | none => simp [hb0] at hb
    | some b0 =>
      simp only [hb0, Option.map_some, Option.some.injEq] at hb
      subst hb
      obtain ⟨he, hord⟩ := hideBind_visible hz
      rw [he] at hz ⊢
      obtain ⟨hty, hu, hloc⟩ := h.here b0 hb0 hz
      refine ⟨hty, fun i c hc => ?_, hloc⟩
      obtain ⟨c', hc', hle⟩ := hu i c hc
      refine ⟨hideBind n c', by rw [getElem?_hide, hc']; rfl, le_hideBind hle fun hl => ?_⟩
      obtain ⟨hbl, hAc⟩ := hloc i c hc hl
      have hn := hord hbl
      rw [hty] at hn
      omega

theorem subst_safe {Γu : List Bind} {u : Term} {A : Ty} (hu : LS true Γu u A)
    {m : Bool} {Γ : List Bind} {t : Term} {B : Ty} (h : LS m Γ t B) :
    ∀ (j : Nat) (Γ' : List Bind), SubstCtx Γu A j Γ Γ' → LS m Γ' (subst j u t) B := by
  induction h with
  | @var m Γ i π b hb hz =>
    intro j Γ' hctx
    by_cases hij : i < j
    · simp only [subst, hij, ite_true]
      exact LS.var (by rw [hctx.below i hij]; exact hb) hz
    · by_cases heq : i = j
      · subst heq
        simp only [subst, hij, ite_false, ite_true]
        obtain ⟨hty, hΓu, _⟩ := hctx.here b hb hz
        rw [hty]
        refine graft_safe π (shift_safe hu m Γ' i 0 (fun h => by cases h) ?_) 0
        intro k c hc
        simpa using hΓu k c hc
      · simp only [subst, hij, heq, ite_false]
        have hb' : Γ'[i - 1]? = some b := by
          rw [hctx.above (i - 1) (by omega), show i - 1 + 1 = i by omega]
          exact hb
        exact LS.var hb' hz
  | lam _ ih =>
    intro j Γ' hctx
    simp only [subst]
    exact LS.lam (ih (j + 1) _ (hctx.under_lam _))
  | app _ _ iht ihv =>
    intro j Γ' hctx
    simp only [subst]
    exact LS.app (iht j Γ' hctx) (ihv j _ (hctx.under_arg _))

/-! ## Subject reduction -/

/-- A step keeps a term safe. A context outside all arguments must not have local variables. -/
theorem Step.safe {t t' : Term} (st : Step t t') :
    ∀ (m : Bool) (Γ : List Bind) (A : Ty),
      (m = false → ∀ (i : Nat) (b : Bind), Γ[i]? = some b → b.zone ≠ .loc) →
      LS m Γ t A → LS m Γ t' A := by
  induction st with
  | @beta A t u =>
    intro m Γ B hΓ h
    cases h with
    | app hf hu =>
      cases hf with
      | lam ht =>
        refine subst_safe hu ht 0 Γ
          ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i _ => rfl, ?_⟩
        intro b hb hz
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        refine ⟨rfl, fun i c hc => ?_, fun i c hc hl => ?_⟩
        · rw [getElem?_hide] at hc
          cases hc0 : Γ[i]? with
          | none => simp [hc0] at hc
          | some c0 =>
            simp only [hc0, Option.map_some, Option.some.injEq] at hc
            subst hc
            exact ⟨c0, rfl, hideBind_le _ _⟩
        · rw [getElem?_hide] at hc
          cases hc0 : Γ[i]? with
          | none => simp [hc0] at hc
          | some c0 =>
            simp only [hc0, Option.map_some, Option.some.injEq] at hc
            subst hc
            have hv : (hideBind A.order c0).zone ≠ .hid := by
              rw [hl]
              decide
            obtain ⟨he, hord⟩ := hideBind_visible hv
            rw [he] at hl ⊢
            refine ⟨?_, hord hl⟩
            cases m with
            | true => rfl
            | false => exact absurd hl (hΓ rfl i c0 hc0)
  | lam _ ih =>
    intro m Γ B hΓ h
    cases h with
    | lam ht =>
      refine LS.lam (ih m _ _ ?_ ht)
      intro hm i b hb
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        subst hm
        show Zone.glob ≠ Zone.loc
        decide
      | succ k =>
        simp only [List.getElem?_cons_succ] at hb
        exact hΓ hm k b hb
  | appL _ ih =>
    intro m Γ B hΓ h
    cases h with
    | app hf hu => exact LS.app (ih m Γ _ hΓ hf) hu
  | appR _ ih =>
    intro m Γ B hΓ h
    cases h with
    | app hf hu => exact LS.app hf (ih true _ _ (fun h => by cases h) hu)

theorem Steps.safe {t t' : Term} (st : Steps t t') :
    ∀ A : Ty, LocallySafe t A → LocallySafe t' A := by
  induction st with
  | refl => exact fun _ h => h
  | tail _ s ih =>
    exact fun A h => s.safe false [] A (fun _ i b hb => by simp at hb) (ih A h)

/-! ## Sharing -/

theorem shareAux_safe : ∀ (t : Term) (env : List (Nat × Nat)) (seen : List Nat) (next : Nat)
    (m : Bool) (Γ : List Bind) (A : Ty), LS m Γ t A → LS m Γ (shareAux t env seen next).1 A
  | .var i π, env, seen, next, m, Γ, A, h => by
    cases h with
    | var hb hz =>
      simp only [shareAux]
      split <;> exact LS.var hb hz
  | .lam B t, env, seen, next, m, Γ, A, h => by
    cases h with
    | lam ht => exact LS.lam (shareAux_safe t _ _ _ _ _ _ ht)
  | .app t u, env, seen, next, m, Γ, A, h => by
    cases h with
    | app ht hu => exact LS.app (shareAux_safe t _ _ _ _ _ _ ht) (shareAux_safe u _ _ _ _ _ _ hu)

theorem share_safe {t : Term} {A : Ty} (h : LocallySafe t A) : LocallySafe (share t) A :=
  shareAux_safe t [] [] 0 false [] A h

/-- Every term along the reduction of a locally safe term with its initial sharing is
locally safe. -/
theorem reduct_safe {t₀ t : Term} {A : Ty} (h : LocallySafe t₀ A) (hs : Steps (share t₀) t) :
    LocallySafe t A :=
  hs.safe A (share_safe h)

end LSL
