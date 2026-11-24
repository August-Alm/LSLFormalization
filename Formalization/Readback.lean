import Formalization.Token

/-!
# Readback

Readback recovers a normal form from the context semantics of a closed term by queries, as
in the paper. A *point* `(D, U)` stands for a subterm of the normal form: a token entering
at the root with exponential stacks `D` and multiplicative stack `U` arrives at it. One
query finds the number `n` of leading lambdas (the least `n` for which `U ++ qⁿ` gives an
output) and the head variable; the output's multiplicative stack `V ++ qˡ ++ [p] ++ qᵐ`
says that the head is bound by lambda `l` of the point with address `V`, and has `m` arguments.

Readback uses the exponential stacks only as inputs to later queries. When several enclosing
points share the address `V`, it takes the innermost. That is right for locally safe normal
forms, but not in general: see `ReadbackExamples.lean`.
-/

namespace LSL

/-- Pure lambda terms: the results of readback. -/
inductive Tm where
  | var (i : Nat)
  | lam (t : Tm)
  | app (t u : Tm)
  deriving DecidableEq, Repr

namespace Tm

def lams : Nat → Tm → Tm
  | 0, t => t
  | n + 1, t => .lam (lams n t)

def apps (head : Tm) (args : List Tm) : Tm := args.foldl .app head

end Tm

def erase : Term → Tm
  | .var i _ => .var i
  | .lam _ t => .lam (erase t)
  | .app t u => .app (erase t) (erase u)

/-- The number of leading `q`s of a stack, and the rest. -/
def dropQ : List Side → Nat × List Side
  | .q :: r => ((dropQ r).1 + 1, (dropQ r).2)
  | r => (0, r)

/-- Splits `V ++ qˡ ++ [p] ++ qᵐ` into `(V, l, m)`, with `l` as large as possible. -/
def parse (S : List Side) : Option (List Side × Nat × Nat) :=
  match dropQ S.reverse with
  | (m, .p :: r) => some ((dropQ r).2.reverse, (dropQ r).1, m)
  | _ => none

/-- An enclosing point: its address and its number of leading lambdas. -/
structure Frame where
  addr : List Side
  lams : Nat

/-- The de Bruijn index of lambda `l` of the innermost frame with address `V`. -/
def resolve : List Frame → List Side → Nat → Option Nat
  | [], _, _ => none
  | f :: fs, V, l =>
    if f.addr = V then (if l < f.lams then some (f.lams - 1 - l) else none)
    else (resolve fs V l).map (· + f.lams)

/-- The address of argument `i` of a head bound by lambda `l` of the point with address `V`. -/
def childAddr (V : List Side) (l i : Nat) : List Side :=
  V ++ List.replicate l .q ++ [.p] ++ List.replicate i .q ++ [.p]

/-- `Reads t anc D U u`: the point `(D, U)` of `t`, inside the points `anc` (innermost
first), reads back as `u`. -/
inductive Reads (t : Term) : List Frame → Stacks → List Side → Tm → Prop
  | node {anc : List Frame} {D E : Stacks} {U S V : List Side} {n l m x : Nat}
      {args : List Tm} :
      Sem t .root D (U ++ List.replicate n .q) (.root, E, S) →
      (∀ k, k < n → ¬ Defined t .root D (U ++ List.replicate k .q)) →
      parse S = some (V, l, m) →
      resolve (⟨U, n⟩ :: anc) V l = some x →
      args.length = m →
      (∀ (i : Nat) (a : Tm), args[i]? = some a →
        Reads t (⟨U, n⟩ :: anc) E (childAddr V l i) a) →
      Reads t anc D U (Tm.lams n (Tm.apps (.var x) args))

/-- The closed term `t` reads back as `u`. -/
def ReadsBack (t : Term) (u : Tm) : Prop := Reads t [] Stacks.empty [] u

/-! ## An executable readback

It is sound for `Reads` (`readback_sound`) but can fail where `Reads` holds: it gives up
when a run exceeds `fuel` steps.
-/

/-- The least `n ≥ k` for which the token gives an output, if it gets stuck for every
smaller `n` from `k` on; `b` bounds the number of tries. -/
def firstDefined (fuel : Nat) (t : Term) (D : Stacks) (U : List Side) :
    Nat → Nat → Option (Nat × Output)
  | 0, _ => none
  | b + 1, k =>
    match eval fuel t ⟨.down [], D, U ++ List.replicate k .q⟩ with
    | some (some out) => some (k, out)
    | some none => firstDefined fuel t D U b (k + 1)
    | none => none

/-- `[f 0, …, f (m - 1)]`, if all are defined. -/
def readArgs (f : Nat → Option Tm) : Nat → Option (List Tm)
  | 0 => some []
  | m + 1 =>
    match readArgs f m, f m with
    | some as, some a => some (as ++ [a])
    | _, _ => none

/-- Readback with at most `fuel` steps per run and nesting depth below the third argument. -/
def readback (fuel : Nat) (t : Term) : Nat → List Frame → Stacks → List Side → Option Tm
  | 0, _, _, _ => none
  | d + 1, anc, D, U =>
    match firstDefined fuel t D U fuel 0 with
    | some (n, (.root, E, S)) =>
      match parse S with
      | some (V, l, m) =>
        match resolve (⟨U, n⟩ :: anc) V l with
        | some x =>
          match readArgs (fun i => readback fuel t d (⟨U, n⟩ :: anc) E (childAddr V l i)) m with
          | some args => some (Tm.lams n (Tm.apps (.var x) args))
          | none => none
        | none => none
      | none => none
    | _ => none

theorem firstDefined_spec (fuel : Nat) (t : Term) (D : Stacks) (U : List Side) :
    ∀ (b k n : Nat) (out : Output), firstDefined fuel t D U b k = some (n, out) →
      eval fuel t ⟨.down [], D, U ++ List.replicate n .q⟩ = some (some out) ∧
      ∀ j, k ≤ j → j < n →
        eval fuel t ⟨.down [], D, U ++ List.replicate j .q⟩ = some none
  | 0, _, _, _, h => by simp [firstDefined] at h
  | b + 1, k, n, out, h => by
    simp only [firstDefined] at h
    cases he : eval fuel t ⟨.down [], D, U ++ List.replicate k .q⟩ with
    | none => simp [he] at h
    | some r =>
      cases r with
      | some o =>
        simp only [he] at h
        cases h
        exact ⟨he, fun j hkj hjn => absurd hjn (by omega)⟩
      | none =>
        simp only [he] at h
        obtain ⟨h₁, h₂⟩ := firstDefined_spec fuel t D U b (k + 1) n out h
        refine ⟨h₁, fun j hkj hjn => ?_⟩
        by_cases hj : j = k
        · subst hj
          exact he
        · exact h₂ j (by omega) hjn

theorem readArgs_spec (f : Nat → Option Tm) : ∀ (m : Nat) (as : List Tm),
    readArgs f m = some as →
      as.length = m ∧ ∀ (i : Nat) (a : Tm), as[i]? = some a → f i = some a
  | 0, as, h => by
    simp only [readArgs] at h
    cases h
    exact ⟨rfl, fun i a hi => by simp at hi⟩
  | m + 1, as, h => by
    simp only [readArgs] at h
    split at h
    · rename_i as' a' hr hf
      cases h
      obtain ⟨hlen, hget⟩ := readArgs_spec f m as' hr
      refine ⟨by simp [hlen], fun i a hi => ?_⟩
      by_cases hlt : i < as'.length
      · rw [List.getElem?_append_left hlt] at hi
        exact hget i a hi
      · rw [List.getElem?_append_right (by omega)] at hi
        cases hk : i - as'.length with
        | zero =>
          simp [hk] at hi
          subst hi
          have : i = m := by omega
          subst this
          exact hf
        | succ j => simp [hk] at hi
    · cases h

theorem not_defined_of_stuck {fuel : Nat} {t : Term} {D : Stacks} {T : List Side}
    (h : eval fuel t ⟨.down [], D, T⟩ = some none) : ¬ Defined t .root D T := by
  rintro ⟨out, hsem⟩
  obtain ⟨n, hn⟩ := sem_root.mp hsem
  rw [eval_stuck t fuel _ h n] at hn
  cases hn

theorem readback_sound (fuel : Nat) (t : Term) :
    ∀ (d : Nat) (anc : List Frame) (D : Stacks) (U : List Side) (u : Tm),
      readback fuel t d anc D U = some u → Reads t anc D U u
  | 0, _, _, _, _, h => by simp [readback] at h
  | d + 1, anc, D, U, u, h => by
    simp only [readback] at h
    split at h
    · rename_i n E S hfd
      split at h
      · rename_i V l m hp
        split at h
        · rename_i x hr
          split at h
          · rename_i args ha
            cases h
            obtain ⟨hlen, hget⟩ := readArgs_spec _ _ _ ha
            obtain ⟨hev, hst⟩ := firstDefined_spec fuel t D U fuel 0 n _ hfd
            exact Reads.node (sem_root.mpr ⟨fuel, eval_out t fuel _ _ hev⟩)
              (fun k hk => not_defined_of_stuck (hst k (Nat.zero_le k) hk)) hp hr hlen
              (fun i a hi => readback_sound fuel t d _ _ _ _ (hget i a hi))
          · cases h
        · cases h
      · cases h
    · cases h

end LSL
