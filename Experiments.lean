import Formalization
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# Experiments on the conjectures

These tests run the definitions of the library on generated terms. They prove nothing; they
found the counterexamples behind `betaSimulation_fails` and `readbackPreservation_fails`, and
they are the evidence for `LOPreservation` and `KeepPreservation`.

Build once with `lake build experiments`, then run `lake exe experiments <command>`:

* `random <seed> <count> <size> <plain|keep> <safe|unsafe>`: random typed terms. Each is
  reduced leftmost-outermost and in a random order, and every term on the way is read back.
* `family <seed> <count> <size> <plain|keep>`: the same for terms of the shape
  `(λt. (λy. body) arg) n` and `(λt.λy. body) n`, in which the known failures occur.
* `explore <erasing2|erasing3|capture> <limit> <plain|keep>`: every term reachable from one
  known term.
* `returns <seed> <count> <size>`: how often the token comes back through a binder to an
  occurrence other than the one it last left through.
* `counterparts <seed> <count> <size> <family|random>`, `counterparts known`: the machine
  against a reference machine with pointers, and candidate invariants of the reference
  machine (`inspect`); see the section on counterparts.
* `known`: the clauses of `Simulated` along the reductions of four known terms.
* `beta <seed> <count> <size> <family|random>`: whether pointer readback gives the normal
  form, and whether the pointer machine on a term follows the machine on each of its reducts
  (`checkRun`).

`plain` is beta reduction in any order (`reducts`); `keep` never erases an argument
(`kreducts`). All runs are bounded by step and size limits, but large counts take minutes.
-/

open LSL

namespace Experiments

instance : Inhabited Term := ⟨.var 0 []⟩

/-! ## Generating terms -/

abbrev Gen := StateM Nat

/-- A number below `n`, from a linear congruential generator. -/
def rnd (n : Nat) : Gen Nat := do
  let s ← get
  let s' := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  set s'
  pure ((s' / 4294967296) % n)

def randTy : Nat → Gen Ty
  | 0 => pure .o
  | d + 1 => do
    if (← rnd 3) == 0 then pure .o else
      let a ← randTy d
      let b ← randTy d
      pure (.arr a b)

/-- The argument types with which a variable of type `T` reaches `A`. -/
def argsTo (A : Ty) : Ty → List (List Ty)
  | .o => []
  | .arr B C => (if C = A then [[B]] else []) ++ (argsTo A C).map (B :: ·)

/-- A term of type `A` in context `Γ`, of size about `fuel`; it is typed but need not be
locally safe. -/
partial def gen (fuel : Nat) (Γ : List Ty) (A : Ty) : Gen (Option Term) := do
  let vars := (List.range Γ.length).filter fun i => Γ[i]? == some A
  let pickVar : Gen (Option Term) := do
    if vars.isEmpty then pure none else
      let k ← rnd vars.length
      pure (some (.var vars[k]! []))
  let mkLam : Gen (Option Term) :=
    match A with
    | .arr B C => do
      let b ← gen (fuel - 1) (B :: Γ) C
      pure (b.map (.lam B))
    | .o => pure none
  let varOrLam : Gen (Option Term) := do
    match ← pickVar with
    | some v => pure (some v)
    | none => mkLam
  if fuel == 0 then varOrLam
  else
    let r ← rnd 12
    if r < 2 && !vars.isEmpty then pickVar
    else if r < 3 then
      match A with
      | .arr (.arr B B') (.arr B'' B''') =>
        if B = B' ∧ B = B'' ∧ B = B''' then
          pure (some (Examples.numeral B (1 + (← rnd 3))))
        else mkLam
      | _ => mkLam
    else if r < 6 && A != .o then mkLam
    else if r < 9 then
      let cands := (List.range Γ.length).flatMap fun i =>
        match Γ[i]? with
        | some T => (argsTo A T).map fun as => (i, as)
        | none => []
      if cands.isEmpty then varOrLam
      else
        let (i, as) := cands[← rnd cands.length]!
        let mut t : Term := .var i []
        for B in as do
          match ← gen ((fuel - 1) / as.length) Γ B with
          | some u => t := .app t u
          | none => return none
        pure (some t)
    else
      let B ← randTy 2
      match ← gen (fuel / 2) Γ (.arr B A), ← gen (fuel / 2) Γ B with
      | some f, some u => pure (some (.app f u))
      | _, _ => pure none

def o1 : Ty := .arr .o .o
def tT : Ty := .arr o1 o1
def tY : Ty := .arr tT o1

/-- A term of the targeted family, with its type. -/
def genFamily (fuel : Nat) : Gen (Option (Term × Ty)) := do
  let body ← gen fuel [tY, tT] o1
  let arg ← gen fuel [tT] tY
  let k ← rnd 4
  let n ← if k < 3 then pure (some (Examples.numeral .o (k + 1))) else gen 5 [] tT
  let applied ← rnd 2
  match body, arg, n with
  | some body, some arg, some n =>
    if applied == 0 then pure (some (.app (.lam tT (.app (.lam tY body) arg)) n, o1))
    else pure (some (.app (.lam tT (.lam tY body)) n, .arr tY o1))
  | _, _, _ => pure none

/-- `(λt. (λy.λx. t (λz. y t x) x) (λu. t (u (λw. w)))) n` -/
def erasing (n : Nat) : Term :=
  let v (i : Nat) : Term := .var i []
  .app (.lam tT (.app
      (.lam tY (.lam .o (.app (.app (v 2) (.lam .o (.app (.app (v 2) (v 3)) (v 1)))) (v 0))))
      (.lam tT (.app (v 1) (.app (v 0) (.lam .o (v 0)))))))
    (Examples.numeral .o n)

/-! ## Reducing and reading back -/

def size : Term → Nat
  | .var _ _ => 1
  | .lam _ b => size b + 1
  | .app f u => size f + size u + 1

inductive Mode where
  | plain
  | keep
  deriving BEq

def Mode.ofString (s : String) : Mode := if s == "keep" then .keep else .plain

def Mode.reducts : Mode → Term → List Term
  | .plain => LSL.reducts
  | .keep => kreducts

/-- The leftmost-outermost reduction, first term first; `none` if it does not end. -/
def traceLO : Nat → Term → Option (List Term)
  | 0, t => if (beta? t).isNone then some [t] else none
  | n + 1, t =>
    match beta? t with
    | none => some [t]
    | some t' => if size t' > 1500 then none else (traceLO n t').map (t :: ·)

/-- A reduction in random order, and whether it reached a normal form. -/
def randomTrace (mode : Mode) (steps maxSize : Nat) (t : Term) : Gen (List Term × Bool) := do
  let mut cur := t
  let mut acc := [t]
  for _ in [0:steps] do
    let rs := mode.reducts cur
    if rs.isEmpty then return (acc.reverse, true)
    cur := rs[← rnd rs.length]!
    if size cur > maxSize then return (acc.reverse, false)
    acc := cur :: acc
  return (acc.reverse, false)

def rb (t : Term) : Option Tm := readback 4000 t 60 [] Stacks.empty []

def showSides (s : List Side) : String :=
  String.ofList (s.map fun | .p => 'p' | .q => 'q')

def showPath (π : Path) : String :=
  if π.isEmpty then ""
  else "{" ++ String.intercalate "," (π.map fun (l, s) => toString l ++ showSides [s]) ++ "}"

/-- A term with its binders named by depth and its paths in braces. -/
def pp : Nat → Term → String
  | d, .var i π => (if i < d then "v" ++ toString (d - 1 - i) else "free") ++ showPath π
  | d, .lam _ b => "(λv" ++ toString d ++ ". " ++ pp (d + 1) b ++ ")"
  | d, .app f u => "(" ++ pp d f ++ " " ++ pp d u ++ ")"

/-! ## Readback along reductions -/

structure Counts where
  terms : Nat := 0
  readbacks : Nat := 0
  wrong : Nat := 0
  changesLO : Nat := 0
  changesRandom : Nat := 0
  reachedNormal : Nat := 0

def Counts.show (c : Counts) : String :=
  s!"terms {c.terms}, readbacks {c.readbacks}, not the normal form {c.wrong}, readback " ++
  s!"changes along leftmost-outermost {c.changesLO}, along random order {c.changesRandom}, " ++
  s!"random order reached a normal form {c.reachedNormal}"

/-- Reduces `share t₀` leftmost-outermost and in random order, and reads back every term. -/
def checkTerm (mode : Mode) (t₀ : Term) (c : Counts) : Gen (Counts × Option Term) := do
  let some lo := traceLO 80 (share t₀) | return (c, none)
  if lo.length < 2 then return (c, none)
  let nf := erase lo.getLast!
  let (random, normal) ← randomTrace mode 90 600 (share t₀)
  let mut c := { c with terms := c.terms + 1 }
  if normal then c := { c with reachedNormal := c.reachedNormal + 1 }
  let mut bad : Option Term := none
  for (trace, isLO) in [(lo, true), (random, false)] do
    let rbs := (trace.filter (size · ≤ 400)).map fun t => (t, rb t)
    c := { c with readbacks := c.readbacks + rbs.length }
    for (t, r) in rbs do
      if r != some nf then
        c := { c with wrong := c.wrong + 1 }
        if bad.isNone then bad := some t
    if rbs.any (·.2 != some nf) && rbs.any (·.2 == some nf) then
      if isLO then c := { c with changesLO := c.changesLO + 1 }
      else c := { c with changesRandom := c.changesRandom + 1 }
  return (c, bad)

def randomTests (seed n fuel : Nat) (mode : Mode) (wantSafe : Bool) : IO Unit := do
  let mut seed := seed
  let mut c : Counts := {}
  let mut shown := 0
  for _ in [0:n] do
    let ((A, t), s) := (do
      let A ← randTy 3
      pure (A, ← gen fuel [] A)).run seed
    seed := s
    let some t₀ := t | continue
    if (infer false [] t₀ == some A) != wantSafe then continue
    let ((c', bad), s) := (checkTerm mode t₀ c).run seed
    seed := s
    c := c'
    if let some b := bad then
      if wantSafe && shown < 3 then
        shown := shown + 1
        IO.println s!"wrong readback: from {pp 0 t₀}\n  at {pp 0 b}"
  IO.println c.show

def familyTests (seed n fuel : Nat) (mode : Mode) : IO Unit := do
  let mut seed := seed
  let mut safe : Counts := {}
  let mut notSafe : Counts := {}
  let mut shown := 0
  for _ in [0:n] do
    let (r, s) := (genFamily fuel).run seed
    seed := s
    let some (t₀, A) := r | continue
    let isSafe := infer false [] t₀ == some A
    let ((c', bad), s) := (checkTerm mode t₀ (if isSafe then safe else notSafe)).run seed
    seed := s
    if isSafe then safe := c' else notSafe := c'
    if let some b := bad then
      if isSafe && shown < 3 then
        shown := shown + 1
        IO.println s!"wrong readback: from {pp 0 t₀}\n  at {pp 0 b}"
  IO.println s!"locally safe: {safe.show}"
  IO.println s!"not locally safe: {notSafe.show}"

/-- Reads back every term reachable from `share t₀`, up to `limit` terms. -/
def explore (mode : Mode) (t₀ : Term) (limit : Nat) : IO Unit := do
  let some lo := traceLO 300 (share t₀) | IO.println "no normal form found"
  let nf := erase lo.getLast!
  let mut seen : Std.HashSet String := {}
  let mut queue := #[share t₀]
  seen := seen.insert (pp 0 (share t₀))
  let mut head := 0
  let mut wrong := 0
  let mut normal := 0
  let mut first : Option Term := none
  while head < queue.size && head < limit do
    let t := queue[head]!
    head := head + 1
    if readback 6000 t 40 [] Stacks.empty [] != some nf then
      wrong := wrong + 1
      if first.isNone then first := some t
    let rs := mode.reducts t
    if rs.isEmpty then normal := normal + 1
    for r in rs do
      let k := pp 0 r
      if !seen.contains k && size r ≤ 250 then
        seen := seen.insert k
        queue := queue.push r
  let all := if head < queue.size then "more remain" else "all reachable terms"
  IO.println s!"read back {head} terms ({all}), {normal} normal, {wrong} not as the normal form"
  if let some t := first then IO.println s!"  first: {pp 0 t}"

/-! ## Returns to another occurrence -/

/-- Runs one query and counts the returns through a binder (a lambda entered at its variable
side), and those that go to an occurrence other than the one last left through. -/
def returnStats (t : Term) (T : List Side) (fuel : Nat) : Nat × Nat := Id.run do
  let mut s : State := ⟨.down [], Stacks.empty, T⟩
  let mut pending : List (Addr × Addr) := []
  let mut returns := 0
  let mut other := 0
  for _ in [0:fuel] do
    match step t s with
    | .next s' =>
      match s.pos, s'.pos with
      | .down a, .up b =>
        match t.sub a with
        | some (.var _ _) => pending := (b, a) :: pending
        | some (.lam _ _) =>
          match pending.find? (·.1 == a) with
          | some (_, left) =>
            returns := returns + 1
            if left != b then other := other + 1
            pending := pending.eraseP (·.1 == a)
          | none => pure ()
        | _ => pure ()
      | _, _ => pure ()
      s := s'
    | _ => break
  return (returns, other)

/-- The statistics of the first query of readback that has an output. -/
def firstQueryReturns (t : Term) : Option (Nat × Nat) :=
  (List.range 8).findSome? fun n =>
    let T := List.replicate n Side.q
    match eval 4000 t ⟨.down [], Stacks.empty, T⟩ with
    | some (some _) => some (returnStats t T 4000)
    | _ => none

def returnTests (seed n fuel : Nat) : IO Unit := do
  let mut seed := seed
  -- per class: terms read, terms with a return to another occurrence, returns, such returns
  let mut safe := (0, 0, 0, 0)
  let mut notSafe := (0, 0, 0, 0)
  let mut witness : Option Term := none
  for _ in [0:n] do
    let (r, s) := (genFamily fuel).run seed
    seed := s
    let some (t₀, A) := r | continue
    let isSafe := infer false [] t₀ == some A
    let ((trace, _), s) := (randomTrace .keep 60 400 (share t₀)).run seed
    seed := s
    for t in trace do
      let some (returns, other) := firstQueryReturns t | continue
      let (a, b, c, d) := if isSafe then safe else notSafe
      let new := (a + 1, b + (if other > 0 then 1 else 0), c + returns, d + other)
      if isSafe then
        safe := new
        if other > 0 && witness.isNone then witness := some t
      else notSafe := new
  let line (x : Nat × Nat × Nat × Nat) : String :=
    s!"{x.1} terms read, {x.2.1} with a return to another occurrence; " ++
    s!"{x.2.2.1} returns, {x.2.2.2} to another occurrence"
  IO.println s!"locally safe: {line safe}"
  IO.println s!"not locally safe: {line notSafe}"
  if let some t := witness then IO.println s!"a locally safe example: {pp 0 t}"

/-! ## Counterparts: the machine against a machine with pointers

The reference machine does not use the sharing paths. When the token leaves a variable for
its binder it records the occurrence (a pointer) and comes back to exactly that occurrence.
Its log has one entry for each argument around the token: how that argument was entered.
This is the usual interaction abstract machine for lambda terms, and it reads every term back
correctly, locally safe or not.

Both machines run together. Each entry that the machine of the library pushes on a stack is
tagged with the exit that pushed it. A return is *foreign* if it pops an entry of another
exit: in a sharing graph, a duplication meeting a superposition that is not its counterpart. -/

/-- An exit from a variable to its binder: the occurrence, and the log entries left behind. -/
inductive Logged where
  | mk (id : Nat) (occ : Addr) (saved : List Logged)

def Logged.id : Logged → Nat
  | .mk i _ _ => i

def Logged.occ : Logged → Addr
  | .mk _ o _ => o

def Logged.saved : Logged → List Logged
  | .mk _ _ s => s

inductive Item where
  | q
  | p (l : Logged)

/-- The same exit, possibly made at another time. An entry made up by readback (it has no
occurrence) is only the same as itself. -/
partial def Logged.same (a b : Logged) : Bool :=
  if a.occ.isEmpty || b.occ.isEmpty then a.id == b.id
  else a.occ == b.occ && a.saved.length == b.saved.length &&
    (a.saved.zip b.saved).all fun (x, y) => x.same y

def Item.same : Item → Item → Bool
  | .q, .q => true
  | .p a, .p b => a.same b
  | _, _ => false

def sameItems : List Item → List Item → Bool
  | [], [] => true
  | a :: as, b :: bs => a.same b && sameItems as bs
  | _, _ => false

abbrev Tagged := Label → List (Side × Nat)

def pushTagged (S : Tagged) (tag : Nat) : Path → Tagged
  | [] => S
  | (l, s) :: π => pushTagged (fun k => if k = l then (s, tag) :: S k else S k) tag π

def popTagged (S : Tagged) : Path → Option (Tagged × List Nat)
  | [] => some (S, [])
  | (l, s) :: π =>
    match S l with
    | (s', tag) :: rest =>
      if s' = s then
        (popTagged (fun k => if k = l then rest else S k) π).map fun (S', tags) => (S', tag :: tags)
      else none
    | [] => none

def selectTagged (S : Tagged) (os : List (Addr × Path)) : Option (Addr × Tagged × List Nat) :=
  os.findSome? fun (a, π) => (popTagged S π.reverse).map fun (S', tags) => (a, S', tags)

structure Both where
  pos : Pos
  tape : List Item
  log : List Logged
  stacks : Tagged

structure Tally where
  nextId : Nat := 0
  returns : Nat := 0
  foreign : Nat := 0
  /-- The machine of the library chose another occurrence than the pointer, or got stuck. -/
  parted : Bool := false
  /-- The reference machine itself failed; this would be a mistake in this file. -/
  broken : Bool := false
  /-- Candidate invariants of the reference machine that failed in some state; see `inspect`. -/
  tapeTwice : Bool := false
  logOrder : Bool := false
  tapeThenLog : Bool := false
  logThenTape : Bool := false
  underTape : Bool := false
  notNewest : Bool := false
  bottomUp : Bool := false
  blocked : Bool := false
  globalOnTape : Bool := false
  orderGap : Bool := false
  /-- How pairs of exits to one binder were found to lie; see `pairClasses`. -/
  classes : List String := []

inductive Outcome where
  | next (s : Both)
  | done (tape : List Item) (stacks : Tagged)
  | stuck

/-- The number of arguments that enclose `a` but not its ancestor `b`. -/
def argsBetween (a b : Addr) : Nat :=
  ((a.take (a.length - b.length - 1)).filter (· == Dir.arg)).length

def stepBoth (t : Term) (s : Both) : StateM Tally Outcome := do
  let fail : StateM Tally Outcome := do
    modify fun c => { c with broken := true }
    pure .stuck
  match s.pos with
  | .down a =>
    match t.sub a with
    | some (.app _ _) => pure (.next { s with pos := .down (.fn :: a), tape := .q :: s.tape })
    | some (.lam _ b) =>
      match s.tape with
      | .q :: T => pure (.next { s with pos := .down (.body :: a), tape := T })
      | .p l :: T =>
        if binderOf t l.occ != some a then return ← fail
        let mut stacks := s.stacks
        if !(← get).parted then
          match selectTagged s.stacks (occs b 0 (.body :: a)) with
          | some (o, S', tags) =>
            if o == l.occ then
              stacks := S'
              let foreign := if tags.all (· == l.id) then 0 else 1
              modify fun c => { c with returns := c.returns + 1, foreign := c.foreign + foreign }
            else modify fun c => { c with parted := true }
          | none => modify fun c => { c with parted := true }
        pure (.next { pos := .up l.occ, tape := T, log := l.saved ++ s.log, stacks })
      | [] => pure .stuck
    | some (.var i π) =>
      match binder a i with
      | .inr b =>
        let n := argsBetween a b
        if s.log.length < n then return ← fail
        let id := (← get).nextId
        modify fun c => { c with nextId := id + 1 }
        let l := Logged.mk id a (s.log.take n)
        pure (.next { pos := .up b, tape := .p l :: s.tape, log := s.log.drop n,
                      stacks := pushTagged s.stacks id π })
      | .inl _ => pure .stuck
    | none => pure .stuck
  | .up [] => if s.log.isEmpty then pure (.done s.tape s.stacks) else fail
  | .up (.body :: a) => pure (.next { s with pos := .up a, tape := .q :: s.tape })
  | .up (.fn :: a) =>
    match s.tape with
    | .p l :: T => pure (.next { s with pos := .down (.arg :: a), tape := T, log := l :: s.log })
    | .q :: T => pure (.next { s with pos := .up a, tape := T })
    | [] => pure .stuck
  | .up (.arg :: a) =>
    match s.log with
    | l :: L => pure (.next { s with pos := .down (.fn :: a), tape := .p l :: s.tape, log := L })
    | [] => fail

/-- An exit and the exits saved under it, the exit first. -/
partial def Logged.tree (l : Logged) : List Logged :=
  l :: l.saved.flatMap Logged.tree

/-- The binder and the age of each exit to a bound variable. -/
def keyed (t : Term) (ls : List Logged) : List (Addr × Nat) :=
  ls.filterMap fun l => (binderOf t l.occ).map (·, l.id)

/-- Among the exits to one binder, an earlier one in the list is newer. -/
def newestFirst : List (Addr × Nat) → Bool
  | [] => true
  | (b, id) :: rest => rest.all (fun (b', id') => b' != b || id' < id) && newestFirst rest

def noRepeat : List (Addr × Nat) → Bool
  | [] => true
  | (b, _) :: rest => rest.all (fun (b', _) => b' != b) && noRepeat rest

/-- Where a live exit lies: under which entry of the tape or of the log, whether it is that
entry itself, and whether the exit of a global variable lies above it. -/
structure Place where
  onTape : Bool
  index : Nat
  direct : Bool
  viaGlobal : Bool
  exit : Logged

partial def placesUnder (t : Term) (onTape : Bool) (index : Nat) (direct viaGlobal : Bool)
    (l : Logged) : List Place :=
  let glob := match binderOf t l.occ with
    | some b => argDepth b == 0
    | none => false
  ⟨onTape, index, direct, viaGlobal, l⟩ ::
    l.saved.flatMap (placesUnder t onTape index false (viaGlobal || glob))

def Place.show (p : Place) : String :=
  (if p.onTape then "tape" else "log") ++ (if p.direct then "" else if p.viaGlobal then
    "/under-global" else "/under-local")

/-- For each pair of live exits to one binder: whether the binder is global, where the newer
and the older exit lie, and how: the older one under the newer one (`inside`), under the same
entry, under an earlier or a later entry of the same list, or one on the tape and one in the
log. -/
def pairClasses (t : Term) (s : Both) : List String := Id.run do
  let onTape := s.tape.filterMap fun | .p l => some l | .q => none
  let places := (onTape.zipIdx.flatMap fun (l, i) => placesUnder t true i true false l) ++
    (s.log.zipIdx.flatMap fun (l, i) => placesUnder t false i true false l)
  let mut out : List String := []
  for x in places do
    let some b := binderOf t x.exit.occ | continue
    for y in places do
      if y.exit.id < x.exit.id && binderOf t y.exit.occ == some b then
        let rel := if x.exit.tree.any (·.id == y.exit.id) then "inside"
          else if x.onTape != y.onTape then "other list"
          else if x.index == y.index then "same entry"
          else if x.index < y.index then "newer first" else "older first"
        let c := s!"{if argDepth b == 0 then "global" else "local"} binder; newer {x.show}; " ++
          s!"older {y.show}; {rel}"
        if !out.contains c then out := c :: out
  return out

/-- Checks candidate invariants in a state of the reference machine:

* `tapeTwice`: two exits to the same binder lie on the tape itself;
* `logOrder`: of two exits to the same binder in the log itself, the outer one is newer;
* `tapeThenLog`, `logThenTape`: listing the exits on the tape and then those in the log (or
  the other way round), each followed by the exits saved under it, does not list the exits
  to each binder newest first;
* at the root of an argument, where its log entry goes back on the tape: `underTape`,
  another exit to the same binder is saved under an exit on the tape; `notNewest`, the entry
  is not the newest exit to its binder;
* `bottomUp`: like `tapeThenLog`, with the tape listed from the bottom up;
* `blocked`: the state is not `PState.Clear`: the token leaves for a lambda or comes back to
  one while another exit to it lies under the tape;
* `globalOnTape`: inside an argument, the exit of a global variable lies on the tape itself;
* `orderGap`: in the two situations of `blocked`, some exit under the tape belongs to a
  variable whose order is not below that of the variable of the lambda concerned. -/
def inspect (t : Term) (s : Both) : StateM Tally Unit := do
  let onTape := s.tape.filterMap fun | .p l => some l | .q => none
  let underTape := keyed t (onTape.flatMap Logged.tree)
  let underLog := keyed t (s.log.flatMap Logged.tree)
  if !noRepeat (keyed t onTape) then modify fun c => { c with tapeTwice := true }
  if !newestFirst (keyed t s.log) then modify fun c => { c with logOrder := true }
  if !newestFirst (underTape ++ underLog) then modify fun c => { c with tapeThenLog := true }
  if !newestFirst (underLog ++ underTape) then modify fun c => { c with logThenTape := true }
  if !newestFirst (keyed t (onTape.reverse.flatMap Logged.tree) ++ underLog) then
    modify fun c => { c with bottomUp := true }
  let isGlobal (l : Logged) : Bool := match binderOf t l.occ with
    | some b => argDepth b == 0
    | none => false
  let here := match s.pos with
    | .down a => a
    | .up a => a
  if argDepth here > 0 && onTape.any isGlobal then modify fun c => { c with globalOnTape := true }
  let orderAt (b : Addr) : Nat := match t.sub b with
    | some (.lam A _) => A.order
    | _ => 0
  let orders (ls : List Logged) : List Nat :=
    (ls.flatMap Logged.tree).filterMap fun l => (binderOf t l.occ).map orderAt
  match s.pos with
  | .down a =>
    match t.sub a, s.tape with
    | some (.var _ _), _ =>
      if let some b := binderOf t a then
        if underTape.any (·.1 == b) then modify fun c => { c with blocked := true }
        if (orders onTape).any (· ≥ orderAt b) then modify fun c => { c with orderGap := true }
    | some (.lam _ _), .p _ :: T =>
      let below := keyed t ((T.filterMap fun | .p l => some l | .q => none).flatMap Logged.tree)
      if below.any (·.1 == a) then modify fun c => { c with blocked := true }
      if (orders (T.filterMap fun | .p l => some l | .q => none)).any (· ≥ orderAt a) then
        modify fun c => { c with orderGap := true }
    | _, _ => pure ()
  | .up _ => pure ()
  for c in pairClasses t s do
    if !(← get).classes.contains c then modify fun y => { y with classes := c :: y.classes }
  match s.pos, s.log with
  | .up (.arg :: _), l :: L =>
    if let some b := binderOf t l.occ then
      if underTape.any (·.1 == b) then modify fun c => { c with underTape := true }
      let others := underTape ++ keyed t (L.flatMap Logged.tree)
      if others.any (fun (b', id') => b' == b && id' > l.id) then
        modify fun c => { c with notNewest := true }
  | _, _ => pure ()

/-- `none`: out of steps; `some none`: stuck. -/
def runBoth (t : Term) : Nat → Both → StateM Tally (Option (Option (List Item × Tagged)))
  | 0, _ => pure none
  | n + 1, s => do
    inspect t s
    match ← stepBoth t s with
    | .next s' => runBoth t n s'
    | .done tape stacks => pure (some (some (tape, stacks)))
    | .stuck => pure (some none)

def countQ : List Item → Nat × List Item
  | .q :: r => let (n, rest) := countQ r; (n + 1, rest)
  | r => (0, r)

/-- Like `resolve`, but a block is known by the exits on its address, not by their sides. -/
def resolveRef : List (List Item × Nat) → List Item → Nat → Option Nat
  | [], _, _ => none
  | (U, n) :: fs, V, l =>
    if sameItems U V then (if l < n then some (n - 1 - l) else none)
    else (resolveRef fs V l).map (· + n)

/-- Readback driven by the reference machine, with the machine of the library alongside. -/
partial def readBoth (t : Term) (fuel : Nat) (depth : Nat) (anc : List (List Item × Nat))
    (stacks : Tagged) (U : List Item) : StateM Tally (Option Tm) := do
  if depth == 0 then return none
  let mut found : Option (Nat × List Item × Tagged) := none
  for n in [0:16] do
    match ← runBoth t fuel ⟨.down [], U ++ List.replicate n .q, [], stacks⟩ with
    | some (some (S, E)) =>
      found := some (n, S, E)
      break
    | some none => continue
    | none => return none
  let some (n, S, E) := found | return none
  let (m, rest) := countQ S.reverse
  let .p l₀ :: rest := rest | return none
  let (l, Vrev) := countQ rest
  let V := Vrev.reverse
  let some x := resolveRef ((U, n) :: anc) V l | return none
  let mut args : List Tm := []
  for i in [0:m] do
    let id := (← get).nextId
    modify fun c => { c with nextId := id + 1 }
    let child := V ++ List.replicate l .q ++ [.p l₀] ++ List.replicate i .q ++ [.p (.mk id [] [])]
    let some a ← readBoth t fuel (depth - 1) ((U, n) :: anc) E child | return none
    args := args ++ [a]
  return some (Tm.lams n (Tm.apps (.var x) args))

/-- The reference readback of `t`, and how the machine of the library fared alongside. -/
def compareMachines (t : Term) : Option Tm × Tally :=
  (readBoth t 20000 60 [] (fun _ => []) []).run {}

structure Compared where
  terms : Nat := 0
  referenceWrong : Nat := 0
  parted : Nat := 0
  withForeign : Nat := 0
  returns : Nat := 0
  foreign : Nat := 0
  tapeTwice : Nat := 0
  logOrder : Nat := 0
  tapeThenLog : Nat := 0
  logThenTape : Nat := 0
  underTape : Nat := 0
  notNewest : Nat := 0
  bottomUp : Nat := 0
  blocked : Nat := 0
  globalOnTape : Nat := 0
  orderGap : Nat := 0
  classes : Std.HashMap String Nat := {}

def Compared.add (c : Compared) (nf : Tm) (r : Option Tm × Tally) : Compared :=
  let (tm, tally) := r
  let count (b : Bool) : Nat := if b then 1 else 0
  { terms := c.terms + 1
    referenceWrong := c.referenceWrong + (if tm == some nf && !tally.broken then 0 else 1)
    parted := c.parted + (if tally.parted then 1 else 0)
    withForeign := c.withForeign + (if tally.foreign > 0 then 1 else 0)
    returns := c.returns + tally.returns
    foreign := c.foreign + tally.foreign
    tapeTwice := c.tapeTwice + count tally.tapeTwice
    logOrder := c.logOrder + count tally.logOrder
    tapeThenLog := c.tapeThenLog + count tally.tapeThenLog
    logThenTape := c.logThenTape + count tally.logThenTape
    underTape := c.underTape + count tally.underTape
    notNewest := c.notNewest + count tally.notNewest
    bottomUp := c.bottomUp + count tally.bottomUp
    blocked := c.blocked + count tally.blocked
    globalOnTape := c.globalOnTape + count tally.globalOnTape
    orderGap := c.orderGap + count tally.orderGap
    classes := tally.classes.foldl (fun m k => m.insert k (m.getD k 0 + 1)) c.classes }

def Compared.show (c : Compared) : String :=
  s!"terms {c.terms}, reference machine wrong {c.referenceWrong}, the machine leaves the " ++
  s!"reference {c.parted}, terms with a foreign return {c.withForeign}; returns {c.returns}, " ++
  s!"foreign {c.foreign}\n    terms in which a candidate invariant fails: tapeTwice " ++
  s!"{c.tapeTwice}, logOrder {c.logOrder}, tapeThenLog {c.tapeThenLog}, logThenTape " ++
  s!"{c.logThenTape}, underTape {c.underTape}, notNewest {c.notNewest}, bottomUp " ++
  s!"{c.bottomUp}, blocked {c.blocked}, globalOnTape {c.globalOnTape}, orderGap {c.orderGap}"

/-- Compares the machines on `share t₀` and on the terms of one reduction that keeps erased
arguments. -/
def counterpartTests (seed n fuel : Nat) (family : Bool) : IO Unit := do
  let mut seed := seed
  let mut initial : Compared × Compared := ({}, {})
  let mut reducts : Compared × Compared := ({}, {})
  let mut witness : Option Term := none
  for _ in [0:n] do
    let (r, s) := (if family then genFamily fuel else do
      let A ← randTy 3
      pure ((← gen fuel [] A).map (·, A))).run seed
    seed := s
    let some (t₀, A) := r | continue
    let some lo := traceLO 80 (share t₀) | continue
    if lo.length < 2 then continue
    let nf := erase lo.getLast!
    let isSafe := infer false [] t₀ == some A
    let r₀ := compareMachines (share t₀)
    if isSafe then initial := (initial.1.add nf r₀, initial.2)
    else initial := (initial.1, initial.2.add nf r₀)
    if isSafe && witness.isNone && (r₀.2.parted || r₀.2.foreign > 0) then witness := some t₀
    let ((trace, _), s) := (randomTrace .keep 40 300 (share t₀)).run seed
    seed := s
    for t in trace.drop 1 do
      let r := compareMachines t
      if isSafe then reducts := (reducts.1.add nf r, reducts.2)
      else reducts := (reducts.1, reducts.2.add nf r)
  IO.println s!"initial sharing, locally safe: {initial.1.show}"
  IO.println s!"initial sharing, not locally safe: {initial.2.show}"
  IO.println s!"reducts, locally safe: {reducts.1.show}"
  IO.println s!"reducts, not locally safe: {reducts.2.show}"
  IO.println "pairs of live exits to one binder (terms in which the case occurs: initial safe, initial unsafe, reducts safe):"
  let keys := (initial.1.classes.toList ++ initial.2.classes.toList ++ reducts.1.classes.toList).map (·.1)
  for k in keys.eraseDups.toArray.qsort (· < ·) do
    IO.println s!"  {k}: {initial.1.classes.getD k 0}, {initial.2.classes.getD k 0}, {reducts.1.classes.getD k 0}"
  if let some t := witness then
    IO.println s!"a locally safe term whose initial sharing has one: {pp 0 (share t)}"

def knownCounterparts : IO Unit := do
  for (name, t₀) in [("self-application", Examples.selfApplication),
      ("forbidden capture", ReadbackExamples.forbidden), ("allowed capture", Counterexample.term),
      ("erasing 2", erasing 2), ("2 2 2", Examples.twoTwoTwo), ("kx", ReadbackExamples.kx)] do
    let some lo := traceLO 300 (share t₀) | continue
    let nf := erase lo.getLast!
    let (tm, tally) := compareMachines (share t₀)
    IO.println (s!"{name}: reference reads the normal form: {tm == some nf && !tally.broken}; " ++
      s!"the machine leaves the reference: {tally.parted}; returns {tally.returns}, " ++
      s!"foreign {tally.foreign}")

/-! ## The clauses of `Simulated` -/

def labelsOf : Term → List Nat
  | .var _ π => π.map (·.1)
  | .lam _ b => labelsOf b
  | .app f u => labelsOf f ++ labelsOf u

def sidesUpTo : Nat → List (List Side)
  | 0 => [[]]
  | n + 1 => let r := sidesUpTo n; [[]] ++ r.map (.p :: ·) ++ r.map (.q :: ·)

/-- Checks the two clauses of `Simulated t' t` for the least relation between stacks, on the
queries in `Ts`, from at most `maxPairs` pairs of stacks. -/
def simulatedFails (t t' : Term) (Ts : List (List Side)) (maxPairs fuel : Nat) :
    Option String := Id.run do
  let labels := (labelsOf t ++ labelsOf t').eraseDups
  let key (D : Stacks) := labels.map D
  let mut seen := [(key Stacks.empty, key Stacks.empty)]
  let mut queue := #[(Stacks.empty, Stacks.empty)]
  let mut head := 0
  while head < queue.size && head < maxPairs do
    let (D, D') := queue[head]!
    head := head + 1
    for T in Ts do
      match eval fuel t' ⟨.down [], D', T⟩, eval fuel t ⟨.down [], D, T⟩ with
      | some (some (_, E', S')), some (some (_, E, S)) =>
        if S != S' then
          return some s!"query {showSides T}: outputs {showSides S} and {showSides S'}"
        let k := (key E, key E')
        if !seen.contains k then
          seen := k :: seen
          queue := queue.push (E, E')
      | some (some (_, _, S')), some none =>
        return some s!"query {showSides T}: the reduct outputs {showSides S'}, the term is stuck"
      | some (some (_, _, S')), none =>
        return some s!"query {showSides T}: the reduct outputs {showSides S'}, the term runs on"
      | some none, some (some _) =>
        for T₂ in sidesUpTo 2 do
          if let some (some _) := eval fuel t' ⟨.down [], D', T ++ T₂⟩ then
            return some s!"query {showSides T}: the reduct is stuck, but not on a longer query"
      | _, _ => pure ()
  return none

def knownTests : IO Unit := do
  let Ts := sidesUpTo 5
  for (name, t₀) in [("self-application", Examples.selfApplication),
      ("forbidden capture", ReadbackExamples.forbidden), ("allowed capture", Counterexample.term),
      ("2 2 2", Examples.twoTwoTwo)] do
    let some trace := traceLO 200 (share t₀) | continue
    IO.println s!"{name}: {trace.length} terms"
    for (t, t') in trace.zip (trace.drop 1) do
      if let some msg := simulatedFails t t' Ts 12 1500 then IO.println s!"  {msg}"

end Experiments

/-! ## Pointer readback, and the pointer machine under a beta step -/

namespace BetaTest

open Experiments

def redexes : Term → Addr → List Addr
  | .var _ _, _ => []
  | .lam _ b, a => redexes b (.body :: a)
  | .app f u, a =>
    (match f with
      | .lam _ _ => [a]
      | _ => []) ++ redexes f (.fn :: a) ++ redexes u (.arg :: a)

/-- `checkRun` in the runs of readback on the reduct: the number of runs, the number of
failures and the first failure. -/
partial def points (β : Beta) (t : Term) (fuel depth : Nat) (U : List LSL.Item) :
    Nat × Nat × Option String := Id.run do
  if depth == 0 then return (0, 0, none)
  let mut runs := 0
  for n in [0:7] do
    runs := runs + 1
    match checkRun β t fuel ⟨.down [], U ++ List.replicate n .q, []⟩ with
    | .error "out of steps" => return (runs, 0, none)
    | .error msg => return (runs, 1, some s!"{msg}, {n} lambdas")
    | .ok none => continue
    | .ok (some S) =>
      let some (V, l, e, m) := pparse S | return (runs, 0, none)
      let mut bad := 0
      let mut first : Option String := none
      for i in [0:m] do
        let (r, b, f) := points β t fuel (depth - 1) (childTape V l e i)
        runs := runs + r
        bad := bad + b
        if first.isNone then first := f
      return (runs, bad, first)
  return (runs, 0, none)

/-- On generated terms: whether pointer readback gives the normal form, and whether the
machine on the term follows the machine on each of its reducts. -/
def betaTests (seed n fuel : Nat) (family : Bool) : IO Unit := do
  let mut seed := seed
  let mut terms := 0
  let mut wrong := 0
  let mut redexCount := 0
  let mut runs := 0
  let mut bad := 0
  let mut witness : Option String := none
  for _ in [0:n] do
    let (r, s) := (if family then genFamily fuel else do
      let A ← randTy 3
      pure ((← gen fuel [] A).map (·, A))).run seed
    seed := s
    let some (t₀, _) := r | continue
    let some lo := traceLO 80 t₀ | continue
    if lo.length < 2 then continue
    terms := terms + 1
    if preadback 20000 t₀ 60 [] [] != some (erase lo.getLast!) then wrong := wrong + 1
    for r in (redexes t₀ []).take 8 do
      let some β := Beta.of t₀ r | continue
      redexCount := redexCount + 1
      let (k, b, f) := points β t₀ 20000 8 []
      runs := runs + k
      bad := bad + b
      if witness.isNone then
        if let some msg := f then witness := some s!"{msg}; redex at {repr r} of {pp 0 t₀}"
  IO.println s!"terms {terms}, pointer readback is not the normal form {wrong}"
  IO.println s!"redexes {redexCount}, runs on reducts {runs}, runs that the term does not follow {bad}"
  if let some w := witness then IO.println s!"first: {w}"

end BetaTest

open Experiments in
def main (args : List String) : IO Unit := do
  let num (i : Nat) (default : Nat) : Nat := (args[i]? >>= String.toNat?).getD default
  let mode (i : Nat) : Mode := Mode.ofString (args[i]?.getD "plain")
  match args[0]? with
  | some "random" => randomTests (num 1 1) (num 2 1000) (num 3 8) (mode 4) (args[5]? != some "unsafe")
  | some "family" => familyTests (num 1 1) (num 2 1000) (num 3 8) (mode 4)
  | some "explore" =>
    let t₀ := match args[1]? with
      | some "erasing3" => erasing 3
      | some "capture" => Counterexample.term
      | _ => erasing 2
    explore (mode 3) t₀ (num 2 2000)
  | some "returns" => returnTests (num 1 1) (num 2 1000) (num 3 8)
  | some "counterparts" =>
    if args[1]? == some "known" then knownCounterparts
    else counterpartTests (num 1 1) (num 2 1000) (num 3 8) (args[4]? != some "random")
  | some "known" => knownTests
  | some "beta" => BetaTest.betaTests (num 1 1) (num 2 1000) (num 3 8) (args[4]? != some "random")
  | _ =>
    IO.println "commands: random, family, explore, returns, counterparts, known, beta (see Experiments.lean)"
