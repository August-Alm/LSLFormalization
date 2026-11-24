import Formalization.Pointer

/-!
# Types at addresses

`At t a Δ m Γ s A`: the subterm of the locally safe term `t` at the address `a` is `s`; it is
checked in mode `m` and context `Γ` at type `A`, and `Δ` lists the types of the arguments
around it, innermost first.

The main fact is `At.var`: a variable has the type that its lambda gives it, and if that
lambda lies inside an argument, the variable has at least the order of every argument between
itself and the lambda. This is what local safety says in terms of addresses.
-/

namespace LSL

theorem LS.unique {m : Bool} {Γ : List Bind} {s : Term} {A A' : Ty} (h : LS m Γ s A)
    (h' : LS m Γ s A') : A = A' := by
  induction h generalizing A' with
  | var hb _ =>
    cases h' with
    | var hb' _ =>
      rw [hb] at hb'
      cases hb'
      rfl
  | lam _ ih =>
    cases h' with
    | lam hbody => rw [ih hbody]
  | app _ _ ihf _ =>
    cases h' with
    | app hf _ =>
      cases ihf hf
      rfl

inductive At (t : Term) : Addr → List Ty → Bool → List Bind → Term → Ty → Prop
  | root {A : Ty} : LS false [] t A → At t [] [] false [] t A
  | body {a : Addr} {Δ : List Ty} {m : Bool} {Γ : List Bind} {A B : Ty} {s : Term} :
      At t a Δ m Γ (.lam A s) (.arr A B) → At t (.body :: a) Δ m (⟨A, zoneOf m⟩ :: Γ) s B
  | fn {a : Addr} {Δ : List Ty} {m : Bool} {Γ : List Bind} {f u : Term} {A B : Ty} :
      At t a Δ m Γ (.app f u) B → LS m Γ f (.arr A B) → At t (.fn :: a) Δ m Γ f (.arr A B)
  | arg {a : Addr} {Δ : List Ty} {m : Bool} {Γ : List Bind} {f u : Term} {A B : Ty} :
      At t a Δ m Γ (.app f u) B → LS m Γ f (.arr A B) → LS true (hide A.order Γ) u A →
        At t (.arg :: a) (A :: Δ) true (hide A.order Γ) u A

@[simp] theorem argDepth_nil : argDepth [] = 0 := rfl

@[simp] theorem argDepth_body (a : Addr) : argDepth (.body :: a) = argDepth a := by
  simp [argDepth]

@[simp] theorem argDepth_fn (a : Addr) : argDepth (.fn :: a) = argDepth a := by
  simp [argDepth]

@[simp] theorem argDepth_arg (a : Addr) : argDepth (.arg :: a) = argDepth a + 1 := by
  simp [argDepth]

theorem hideBind_ty (n : Nat) (b : Bind) : (hideBind n b).ty = b.ty := by
  unfold hideBind
  split <;> rfl

namespace At

variable {t : Term} {a : Addr} {Δ : List Ty} {m : Bool} {Γ : List Bind} {s : Term} {A : Ty}

theorem ls (h : At t a Δ m Γ s A) : LS m Γ s A := by
  induction h with
  | root h => exact h
  | body _ ih =>
    cases ih with
    | lam hb => exact hb
  | fn _ hf _ => exact hf
  | arg _ _ hu _ => exact hu

theorem sub (h : At t a Δ m Γ s A) : t.sub a = some s := by
  induction h with
  | root _ => rfl
  | body _ ih =>
    rw [sub_cons, ih]
    rfl
  | fn _ _ ih =>
    rw [sub_cons, ih]
    rfl
  | arg _ _ _ ih =>
    rw [sub_cons, ih]
    rfl

theorem depth (h : At t a Δ m Γ s A) : Δ.length = argDepth a := by
  induction h with
  | root _ => rfl
  | body _ ih => simpa using ih
  | fn _ _ ih => simpa using ih
  | arg _ _ _ ih => simp [ih]

theorem mode (h : At t a Δ m Γ s A) : m = true ↔ 0 < argDepth a := by
  induction h with
  | root _ => simp
  | body _ ih => simpa using ih
  | fn _ _ ih => simpa using ih
  | arg _ _ _ _ => simp

theorem unique (h : At t a Δ m Γ s A) : ∀ {Δ' : List Ty} {m' : Bool} {Γ' : List Bind}
    {s' : Term} {A' : Ty}, At t a Δ' m' Γ' s' A' →
      Δ = Δ' ∧ m = m' ∧ Γ = Γ' ∧ s = s' ∧ A = A' := by
  induction h with
  | root h =>
    intro Δ' m' Γ' s' A' h'
    cases h' with
    | root h' => exact ⟨rfl, rfl, rfl, rfl, LS.unique h h'⟩
  | body _ ih =>
    intro Δ' m' Γ' s' A' h'
    cases h' with
    | body h' =>
      obtain ⟨rfl, rfl, rfl, hs, hA⟩ := ih h'
      cases hs
      cases hA
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | fn _ hf ih =>
    intro Δ' m' Γ' s' A' h'
    cases h' with
    | fn h' hf' =>
      obtain ⟨rfl, rfl, rfl, hs, rfl⟩ := ih h'
      cases hs
      exact ⟨rfl, rfl, rfl, rfl, LS.unique hf hf'⟩
  | arg _ hf _ ih =>
    intro Δ' m' Γ' s' A' h'
    cases h' with
    | arg h' hf' _ =>
      obtain ⟨rfl, rfl, rfl, hs, rfl⟩ := ih h'
      cases hs
      cases LS.unique hf hf'
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The lambda that binds a variable of the context, and what the zone of the variable says
about it. -/
theorem lookup (h : At t a Δ m Γ s A) : ∀ (i : Nat) (bind : Bind), Γ[i]? = some bind →
    ∃ b Δb mb Γb body B, binder a i = .inr b ∧
      At t b Δb mb Γb (.lam bind.ty body) (.arr bind.ty B) ∧
      Δb = Δ.drop (argDepth a - argDepth b) ∧ argDepth b ≤ argDepth a ∧
      (bind.zone = .glob → argDepth b = 0) ∧
      (bind.zone = .loc → 0 < argDepth b ∧ ∀ k C, k < argDepth a - argDepth b →
        Δ[k]? = some C → C.order ≤ bind.ty.order) := by
  induction h with
  | root _ =>
    intro i bind hi
    simp at hi
  | @body a Δ m Γ A B s h ih =>
    intro i bind hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      refine ⟨a, Δ, m, Γ, s, B, by simp [binder], h, by simp, by simp, ?_, ?_⟩
      · intro hz
        cases m with
        | false =>
          exact Nat.eq_zero_of_not_pos fun hp => by
            have := h.mode.mpr hp
            cases this
        | true => simp [zoneOf] at hz
      · intro hz
        cases m with
        | false => simp [zoneOf] at hz
        | true => exact ⟨by simpa using h.mode.mp rfl, fun k C hk => by simp at hk⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simpa [binder] using ih i bind hi
  | fn _ _ ih =>
    intro i bind hi
    simpa [binder] using ih i bind hi
  | @arg a Δ m Γ f u A B h hf hu ih =>
    intro i bind hi
    rw [getElem?_hide] at hi
    cases hΓ : Γ[i]? with
    | none => simp [hΓ] at hi
    | some bind₀ =>
      simp only [hΓ, Option.map_some, Option.some.injEq] at hi
      subst hi
      obtain ⟨b, Δb, mb, Γb, body, B', hb, hat, hΔ, hle, hg, hl⟩ := ih i bind₀ hΓ
      have hty : (hideBind A.order bind₀).ty = bind₀.ty := hideBind_ty _ _
      refine ⟨b, Δb, mb, Γb, body, B', by simpa [binder] using hb, by rw [hty]; exact hat, ?_,
        by simp; omega, ?_, ?_⟩
      · rw [hΔ, argDepth_arg, show argDepth a + 1 - argDepth b = (argDepth a - argDepth b) + 1 by
          omega]
        rfl
      · intro hz
        by_cases hid : (hideBind A.order bind₀).zone = .hid
        · rw [hid] at hz
          cases hz
        · rw [(hideBind_visible hid).1] at hz
          exact hg hz
      · intro hz
        have hv := hideBind_visible (n := A.order) (b := bind₀) (by rw [hz]; decide)
        rw [hv.1] at hz
        obtain ⟨hpos, hord⟩ := hl hz
        refine ⟨hpos, fun k C hk hC => ?_⟩
        rw [hty]
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
          subst hC
          exact hv.2 hz
        | succ k =>
          exact hord k C (by simp only [argDepth_arg] at hk; omega) (by simpa using hC)

end At

/-- The type of the bound variable at `o`: the one that its lambda gives it. -/
def varTy (t : Term) (o : Addr) : Option Ty :=
  (binderOf t o).bind fun b =>
    match t.sub b with
    | some (.lam A _) => some A
    | _ => none

/-- What is known about a variable occurrence of a locally safe term. -/
theorem At.var {t : Term} {o : Addr} {Δ : List Ty} {m : Bool} {Γ : List Bind} {i : Nat}
    {π : Path} {A : Ty} (h : At t o Δ m Γ (.var i π) A) :
    ∃ b Δb mb Γb body B, binder o i = .inr b ∧ binderOf t o = some b ∧ varTy t o = some A ∧
      At t b Δb mb Γb (.lam A body) (.arr A B) ∧
      Δb = Δ.drop (argDepth o - argDepth b) ∧ argDepth b ≤ argDepth o ∧
      (0 < argDepth b → ∀ k C, k < argDepth o - argDepth b → Δ[k]? = some C →
        C.order ≤ A.order) := by
  have hls := h.ls
  cases hls with
  | var hb hz =>
    rename_i bind
    obtain ⟨b, Δb, mb, Γb, body, B, hbi, hat, hΔ, hle, hg, hl⟩ := h.lookup i bind hb
    have hbo : binderOf t o = some b := by simp [binderOf, h.sub, hbi]
    refine ⟨b, Δb, mb, Γb, body, B, hbi, hbo, by simp [varTy, hbo, hat.sub], hat, hΔ, hle, ?_⟩
    intro hpos
    cases hzone : bind.zone with
    | glob =>
      have := hg hzone
      omega
    | loc => exact (hl hzone).2
    | hid => exact absurd hzone hz

end LSL
