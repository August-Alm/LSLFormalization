/-!
# LSL: the simply typed, locally safe lambda calculus

Terms are de Bruijn terms with a type on every binder. Each variable occurrence also carries
its *sharing path*: the fans that lie between the occurrence and its binder. A plain lambda
term has empty paths everywhere; `share` (in `Sharing.lean`) fills them in.
-/

namespace LSL

inductive Ty where
  | o : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

def order : Ty → Nat
  | o => 0
  | arr a b => max (order a + 1) (order b)

end Ty

/-- One of the two auxiliary ports of a fan. -/
inductive Side where
  | p
  | q
  deriving DecidableEq, Repr

abbrev Label := Nat

/-- The fans between a variable occurrence and its binder, nearest the occurrence first. -/
abbrev Path := List (Label × Side)

inductive Term where
  | var (i : Nat) (path : Path)
  | lam (A : Ty) (body : Term)
  | app (fn arg : Term)
  deriving DecidableEq, Repr

/-! ## Simple typing -/

inductive HasType : List Ty → Term → Ty → Prop
  | var {Γ : List Ty} {i : Nat} {π : Path} {A : Ty} :
      Γ[i]? = some A → HasType Γ (.var i π) A
  | lam {Γ : List Ty} {A B : Ty} {t : Term} :
      HasType (A :: Γ) t B → HasType Γ (.lam A t) (.arr A B)
  | app {Γ : List Ty} {A B : Ty} {t u : Term} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (.app t u) B

/-! ## Local safety

A variable is *local* if its binder lies inside an argument, and *global* otherwise. An
argument of order `n` may only mention local variables of order at least `n`; the others are
hidden while the argument is checked.
-/

inductive Zone where
  | glob
  | loc
  | hid
  deriving DecidableEq, Repr

structure Bind where
  ty : Ty
  zone : Zone
  deriving DecidableEq, Repr

/-- Hides the local variables whose order is below `n`. -/
def hide (n : Nat) (Γ : List Bind) : List Bind :=
  Γ.map fun b => if b.zone = .loc ∧ b.ty.order < n then { b with zone := .hid } else b

/-- The zone of a variable bound at a place that is (`true`) or is not (`false`) inside an argument. -/
def zoneOf (inArg : Bool) : Zone := if inArg then .loc else .glob

/-- `LS inArg Γ t A`: `t` has type `A` and is locally safe; `inArg` says whether `t` lies
inside an argument. -/
inductive LS : Bool → List Bind → Term → Ty → Prop
  | var {inArg : Bool} {Γ : List Bind} {i : Nat} {π : Path} {b : Bind} :
      Γ[i]? = some b → b.zone ≠ .hid → LS inArg Γ (.var i π) b.ty
  | lam {inArg : Bool} {Γ : List Bind} {A B : Ty} {t : Term} :
      LS inArg (⟨A, zoneOf inArg⟩ :: Γ) t B → LS inArg Γ (.lam A t) (.arr A B)
  | app {inArg : Bool} {Γ : List Bind} {A B : Ty} {t u : Term} :
      LS inArg Γ t (.arr A B) → LS true (hide A.order Γ) u A → LS inArg Γ (.app t u) B

/-- A closed term is locally safe at type `A`. -/
def LocallySafe (t : Term) (A : Ty) : Prop := LS false [] t A

/-- An executable checker for `LS`. -/
def infer : Bool → List Bind → Term → Option Ty
  | _, Γ, .var i _ =>
    match Γ[i]? with
    | some b => if b.zone = .hid then none else some b.ty
    | none => none
  | inArg, Γ, .lam A t => (infer inArg (⟨A, zoneOf inArg⟩ :: Γ) t).map (Ty.arr A)
  | inArg, Γ, .app t u =>
    match infer inArg Γ t with
    | some (.arr A B) => if infer true (hide A.order Γ) u = some A then some B else none
    | _ => none

theorem infer_sound : ∀ (t : Term) (inArg : Bool) (Γ : List Bind) (A : Ty),
    infer inArg Γ t = some A → LS inArg Γ t A
  | .var i π, inArg, Γ, A, h => by
    simp only [infer] at h
    split at h
    · rename_i b hb
      split at h
      · cases h
      · cases h
        exact LS.var hb (by assumption)
    · cases h
  | .lam B t, inArg, Γ, A, h => by
    simp only [infer] at h
    cases hC : infer inArg (⟨B, zoneOf inArg⟩ :: Γ) t with
    | none => simp [hC] at h
    | some C =>
      simp [hC] at h
      subst h
      exact LS.lam (infer_sound t _ _ _ hC)
  | .app t u, inArg, Γ, A, h => by
    simp only [infer] at h
    split at h
    · rename_i A' B' ht
      split at h
      · rename_i hu
        cases h
        exact LS.app (infer_sound t _ _ _ ht) (infer_sound u _ _ _ hu)
      · cases h
    · cases h

/-! ## Beta reduction

Substituting `s` for an occurrence with path `π` puts `π` in front of the path of every free
variable of that copy of `s`: the fans that select the copy now also lie on those variables.
-/

/-- Adds `d` to the variables of `t` that are free above the cutoff `c`. -/
def shift (d : Nat) : Nat → Term → Term
  | c, .var i π => if i < c then .var i π else .var (i + d) π
  | c, .lam A t => .lam A (shift d (c + 1) t)
  | c, .app t u => .app (shift d c t) (shift d c u)

/-- Puts `π` in front of the path of every variable of `t` that is free above the cutoff `c`. -/
def graft (π : Path) : Nat → Term → Term
  | c, .var i ρ => if i < c then .var i ρ else .var i (π ++ ρ)
  | c, .lam A t => .lam A (graft π (c + 1) t)
  | c, .app t u => .app (graft π c t) (graft π c u)

/-- `subst j s t` replaces variable `j` of `t` by `s` and closes the gap. -/
def subst : Nat → Term → Term → Term
  | j, s, .var i π =>
    if i < j then .var i π
    else if i = j then graft π 0 (shift j 0 s)
    else .var (i - 1) π
  | j, s, .lam A t => .lam A (subst (j + 1) s t)
  | j, s, .app t u => .app (subst j s t) (subst j s u)

inductive Step : Term → Term → Prop
  | beta {A : Ty} {t u : Term} : Step (.app (.lam A t) u) (subst 0 u t)
  | lam {A : Ty} {t t' : Term} : Step t t' → Step (.lam A t) (.lam A t')
  | appL {t t' u : Term} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Term} : Step u u' → Step (.app t u) (.app t u')

inductive Steps : Term → Term → Prop
  | refl {t : Term} : Steps t t
  | tail {t u v : Term} : Steps t u → Step u v → Steps t v

/-- One leftmost-outermost step, for experiments. -/
def beta? : Term → Option Term
  | .var _ _ => none
  | .lam A t => (beta? t).map (.lam A)
  | .app (.lam _ t) u => some (subst 0 u t)
  | .app t u =>
    match beta? t with
    | some t' => some (.app t' u)
    | none => (beta? u).map (.app t)

end LSL
