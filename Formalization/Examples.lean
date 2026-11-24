import Formalization.Sharing
import Formalization.Token

/-!
# Examples: the definitions agree with the F# implementation of SIC

The token machine computes through redexes, so a numeral can be read off a term that has
not been reduced at all. The results below match what SIC reduction plus readback gives in
the F# tests: correct where SIC is correct, and wrong where SIC is wrong.
-/

namespace LSL.Examples

open LSL

def v (i : Nat) : Term := .var i []

def o1 : Ty := .arr .o .o

/-- The type of Church numerals over `A`. -/
def nat (A : Ty) : Ty := .arr (.arr A A) (.arr A A)

def numeral (A : Ty) (n : Nat) : Term :=
  .lam (.arr A A) (.lam A (n.repeat (fun t => .app (v 1) t) (v 0)))

/-- Reads a Church numeral off the context semantics of a closed term: the first query asks
for the head under two lambdas, and each further query asks for the argument of the head. -/
def readNumeral (fuel : Nat) (t : Term) : Option Nat :=
  match run fuel t ⟨.down [], Stacks.empty, [.q, .q]⟩ with
  | some (.root, D, [.p, .q]) => loop fuel D 1
  | some (.root, _, [.q, .p]) => some 0
  | _ => none
where
  loop : Nat → Stacks → Nat → Option Nat
    | 0, _, _ => none
    | n + 1, D, k =>
      match run fuel t ⟨.down [], D, [.p, .p]⟩ with
      | some (.root, D', [.p, .q]) => loop n D' (k + 1)
      | some (.root, _, [.q, .p]) => some k
      | _ => none

def twoTwo : Term := .app (numeral o1 2) (numeral .o 2)
def threeTwo : Term := .app (numeral o1 3) (numeral .o 2)
def twoTwoTwo : Term := .app (.app (numeral (nat .o) 2) (numeral o1 2)) (numeral .o 2)

/-- `(λn.λs. n (n s)) 3`, with the numeral shared. -/
def square : Term :=
  .app (.lam (nat .o) (.lam o1 (.app (v 1) (.app (v 1) (v 0))))) (numeral .o 3)

/-- `(λx. x x) 2`: not simply typed, and SIC reduces it wrongly. -/
def selfApplication : Term := .app (.lam (nat .o) (.app (v 0) (v 0))) (numeral .o 2)

#guard readNumeral 10000 (share (numeral .o 3)) == some 3
#guard readNumeral 10000 (share twoTwo) == some 4
#guard readNumeral 10000 (share threeTwo) == some 8
#guard readNumeral 10000 (share twoTwoTwo) == some 16
#guard readNumeral 10000 (share square) == some 9
#guard readNumeral 10000 (share selfApplication) == none

end LSL.Examples
