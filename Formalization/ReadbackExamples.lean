import Formalization.Preservation
import Formalization.Keep
import Formalization.PointerReadback

/-!
# Readback: examples

For the locally safe examples, every term along the reduction of the shared term reads back
as the normal form. That is what `LOPreservation` says; here it is only checked.
The last two examples are not locally safe, and readback fails or gives a wrong term.
-/

namespace LSL.ReadbackExamples

open LSL LSL.Examples LSL.Counterexample

/-- `t` and its reducts by at most `n` leftmost-outermost steps, last first. -/
def trace : Nat → Term → List Term
  | 0, t => [t]
  | n + 1, t =>
    match beta? t with
    | some t' => trace n t' ++ [t]
    | none => [t]

def rb (t : Term) : Option Tm := readback 2000 t 40 [] Stacks.empty []

/-- The reduction of `share t` ends within 200 steps, and every term along it reads back
as the erasure of its last term. -/
def agrees (t : Term) : Bool :=
  match trace 200 (share t) with
  | nf :: rest => (beta? nf).isNone && (nf :: rest).all fun r => rb r == some (erase nf)
  | [] => false

#guard rb (share (numeral .o 2)) == some (erase (numeral .o 2))
#guard rb (share twoTwo) == some (erase (numeral .o 4))
#guard agrees (numeral .o 3)
#guard agrees twoTwo
#guard agrees threeTwo
#guard agrees twoTwoTwo
#guard agrees square

/-- The term of `strictPreservation_fails`: its context semantics is not preserved, but its
readback is. -/
example : agrees term = true := by decide

/-- A proof of `ReadsBack`, from the executable readback. -/
example : ReadsBack (share twoTwo) (erase (numeral .o 4)) :=
  readback_sound 200 _ 20 _ _ _ _ (by decide)

/-! ## Outside the locally safe terms -/

#guard !agrees selfApplication

/-- `(λt. (λy. t (λz. y t z)) (λu.λw. u (λq. w) w)) 2`: the term of the counterexample with
`y` bound to a term that captures `t`. Its normal form is `λx. x`. -/
def forbidden : Term :=
  .app (.lam tT (.app (.lam tY (.app (v 1) (.lam .o (.app (.app (v 1) (v 2)) (v 0)))))
    (.lam tT (.lam .o (.app (.app (v 1) (.lam .o (v 1))) (v 0)))))) (numeral .o 2)

#guard infer false [] forbidden == none
#guard (trace 200 forbidden).head? == some (.lam .o (v 0))
#guard rb (share forbidden) == none

/-- `λf. f (λx. f (λy. x))` is a normal form that is not locally safe. Both inner lambdas
have the same address, so readback takes `x` for `y`. -/
def kx : Term := .lam (.arr o1 .o) (.app (v 0) (.lam .o (.app (v 1) (.lam .o (v 1)))))

/-- `λf. f (λx. f (λy. y))` is locally safe. -/
def ky : Term := .lam (.arr o1 .o) (.app (v 0) (.lam .o (.app (v 1) (.lam .o (v 0)))))

#guard infer false [] kx == none
#guard (infer false [] ky).isSome
#guard rb (share ky) == some (erase ky)
#guard rb (share kx) == some (erase ky)

/-! ## Keeping erased arguments -/

/-- Takes the first reduct, at most `n` times. -/
def knormalize : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match kreducts t with
    | t' :: _ => knormalize n t'
    | [] => t

/-- The reduction that keeps erased arguments ends within 300 steps, in a term that without
its kept arguments is the normal form, and the shared term reads back as that. -/
def kagrees (t : Term) : Bool :=
  let k := knormalize 300 (share t)
  match trace 200 (share t) with
  | nf :: _ =>
    (kreducts k).isEmpty && eraseK id k == erase nf && rb (share t) == some (eraseK id k)
  | [] => false

#guard kagrees twoTwo
#guard kagrees threeTwo
#guard kagrees square
#guard kagrees term
#guard kagrees erasing

/-- `u₃`, the reduct of `u₂` that does not read back (`readbackPreservation_fails`), is not
a reduct here, and all the reducts of `u₂` here read back as `λx. x`. -/
example : u₃ ∉ kreducts u₂ ∧
    (kreducts u₂).all (fun r => rb r == some (.lam (.var 0))) = true := by decide

/-! ## The pointer machine -/

/-- The pointer machine has to stop within `n` steps: a return is not to the newest exit. -/
def parts (t : Term) : Nat → PState → Bool
  | 0, _ => false
  | n + 1, s =>
    match pstep t s with
    | .next s' => parts t n s'
    | .parted => true
    | _ => false

#guard (prun 2000 (share twoTwoTwo) (.first 2)).isSome
#guard (prun 2000 (share erasing) (.first 1)).isSome
#guard parts (share selfApplication) 2000 (.first 2)
#guard parts (share forbidden) 2000 (.first 1)

/-! ## Pointer readback

It gives the normal form also for the terms that are not locally safe. -/

def prb (t : Term) : Option Tm := preadback 4000 t 40 [] []

#guard prb twoTwo == some (erase (numeral .o 4))
#guard prb twoTwoTwo == (trace 200 twoTwoTwo).head?.map erase
#guard prb term == (trace 200 term).head?.map erase
#guard prb erasing == some (.lam (.var 0))
#guard prb forbidden == some (.lam (.var 0))
#guard prb kx == some (erase kx)

/-- The machine on `t` follows the first runs of the machine on the reduct, for the redex at
`r`. -/
def followsBeta (t : Term) (r : Addr) : Bool :=
  match Beta.of t r with
  | some β => (List.range 4).all fun n =>
      (checkRun β t 3000 ⟨.down [], List.replicate n .q, []⟩).isOk
  | none => false

#guard followsBeta twoTwo []
#guard followsBeta term []
#guard followsBeta erasing []
#guard followsBeta forbidden []

end LSL.ReadbackExamples
