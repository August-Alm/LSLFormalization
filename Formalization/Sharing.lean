import Formalization.LSL

/-!
# The initial sharing of a plain term

A variable used `n > 1` times is split by a chain of `n - 1` fans, each with a label of its
own. Occurrence `k` leaves the chain at fan `k` (the last two leave at fan `n - 2`).
-/

namespace LSL

/-- The number of occurrences of variable `i` in `t`. -/
def occurrences : Nat → Term → Nat
  | i, .var j _ => if j = i then 1 else 0
  | i, .lam _ t => occurrences (i + 1) t
  | i, .app t u => occurrences i t + occurrences i u

/-- The path of occurrence `k` of a variable with `n` occurrences whose fans are labelled
`base, base + 1, …`. -/
def chain (base n k : Nat) : Path :=
  (if k + 1 < n then [(base + k, Side.p)] else [])
    ++ ((List.range (min k (n - 1))).reverse.map fun j => (base + j, Side.q))

/-- `shareAux t env seen next`: `env` gives, for each enclosing binder, the first label and
the number of occurrences; `seen` counts the occurrences met so far; `next` is the next
unused label. -/
def shareAux : Term → List (Nat × Nat) → List Nat → Nat → Term × List Nat × Nat
  | .var i π, env, seen, next =>
    match env[i]?, seen[i]? with
    | some (base, n), some k => (.var i (chain base n k), seen.set i (k + 1), next)
    | _, _ => (.var i π, seen, next)
  | .lam A t, env, seen, next =>
    let n := occurrences 0 t
    let (t', seen', next') := shareAux t ((next, n) :: env) (0 :: seen) (next + (n - 1))
    (.lam A t', seen'.tail, next')
  | .app t u, env, seen, next =>
    let (t', seen', next') := shareAux t env seen next
    let (u', seen'', next'') := shareAux u env seen' next'
    (.app t' u', seen'', next'')

/-- The term with its initial sharing: the analogue of the paper's distinct-labelling translation. -/
def share (t : Term) : Term := (shareAux t [] [] 0).1

end LSL
