import Formalization.FirstRun

/-!
# Readback with the pointer machine

`qstep` is the pointer machine itself, without the history that `pstep` keeps to check the
order of returns; `pstep_forget` relates the two. `PReads` is readback with it, like `Reads`
for the token machine; `preadback` runs it.

`PointerSound` states (B): pointer readback of a typed term gives its normal form. It is not
proved in this form. It holds on all tests, also for terms that are not locally safe. What is
proved is (B) for `QReads` (in `QReads.lean`) on locally safe terms: `normal_qreads` and
`qreads_steps`.
-/

namespace LSL

structure QState where
  pos : Pos
  tape : List Item
  log : List Exit

inductive QResult where
  | next (s : QState)
  | done (tape : List Item)
  | stuck

def qstep (t : Term) (s : QState) : QResult :=
  match s.pos with
  | .down a =>
    match t.sub a with
    | some (.app _ _) => .next ⟨.down (.fn :: a), .q :: s.tape, s.log⟩
    | some (.lam _ _) =>
      match s.tape with
      | .q :: T => .next ⟨.down (.body :: a), T, s.log⟩
      | .p e :: T =>
        if binderOf t e.occ = some a then .next ⟨.up e.occ, T, e.saved ++ s.log⟩ else .stuck
      | [] => .stuck
    | some (.var i _) =>
      match binder a i with
      | .inr b =>
        .next ⟨.up b, .p ⟨a, s.log.take (argDepth a - argDepth b)⟩ :: s.tape,
          s.log.drop (argDepth a - argDepth b)⟩
      | .inl _ => .stuck
    | none => .stuck
  | .up [] => .done s.tape
  | .up (.body :: a) => .next ⟨.up a, .q :: s.tape, s.log⟩
  | .up (.fn :: a) =>
    match s.tape with
    | .p e :: T => .next ⟨.down (.arg :: a), T, e :: s.log⟩
    | .q :: T => .next ⟨.up a, T, s.log⟩
    | [] => .stuck
  | .up (.arg :: a) =>
    match s.log with
    | e :: L => .next ⟨.down (.fn :: a), .p e :: s.tape, L⟩
    | [] => .stuck

/-- `none`: out of steps; `some none`: stuck. -/
def qeval : Nat → Term → QState → Option (Option (List Item))
  | 0, _, _ => none
  | n + 1, t, s =>
    match qstep t s with
    | .next s' => qeval n t s'
    | .done T => some (some T)
    | .stuck => some none

/-- The machine reaches the root with the tape `S`. -/
def QOut (t : Term) (s : QState) (S : List Item) : Prop :=
  ∃ k, qeval k t s = some (some S)

def PState.forget (s : PState) : QState := ⟨s.pos, s.tape, s.log⟩

/-- Unless a return is out of order, the machine with the history does the same. -/
def Matches : PResult → QResult → Prop
  | .next s, .next s' => s.forget = s'
  | .done T _, .done T' => T = T'
  | .stuck, .stuck => True
  | .parted, _ => True
  | _, _ => False

theorem pstep_forget (t : Term) (s : PState) : Matches (pstep t s) (qstep t s.forget) := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | down a =>
    cases hsub : t.sub a with
    | none => simp [pstep, qstep, PState.forget, hsub, Matches]
    | some u =>
      cases u with
      | var i π => cases hb : binder a i <;> simp [pstep, qstep, PState.forget, hsub, hb, Matches]
      | lam A body =>
        cases tape with
        | nil => simp [pstep, qstep, PState.forget, hsub, Matches]
        | cons x T =>
          cases x with
          | q => simp [pstep, qstep, PState.forget, hsub, Matches]
          | p e =>
            by_cases hbe : binderOf t e.occ = some a
            · cases hpop : popNewest t a hist with
              | none => simp [pstep, qstep, PState.forget, hsub, hbe, hpop, Matches]
              | some r =>
                obtain ⟨o, H⟩ := r
                by_cases ho : o = e.occ <;>
                  simp [pstep, qstep, PState.forget, hsub, hbe, hpop, ho, Matches]
            · simp [pstep, qstep, PState.forget, hsub, hbe, Matches]
      | app f u => simp [pstep, qstep, PState.forget, hsub, Matches]
  | up a =>
    cases a with
    | nil => simp [pstep, qstep, PState.forget, Matches]
    | cons d a =>
      cases d with
      | body => simp [pstep, qstep, PState.forget, Matches]
      | fn =>
        cases tape with
        | nil => simp [pstep, qstep, PState.forget, Matches]
        | cons x T => cases x <;> simp [pstep, qstep, PState.forget, Matches]
      | arg => cases log <;> simp [pstep, qstep, PState.forget, Matches]

/-! ## Comparing exits -/

mutual
def Exit.beq : Exit → Exit → Bool
  | .mk o σ, .mk o' σ' => o == o' && Exit.beqs σ σ'
def Exit.beqs : List Exit → List Exit → Bool
  | [], [] => true
  | e :: es, e' :: es' => Exit.beq e e' && Exit.beqs es es'
  | _, _ => false
end

def Item.beq : Item → Item → Bool
  | .q, .q => true
  | .p e, .p e' => e.beq e'
  | _, _ => false

def itemsBeq : List Item → List Item → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.beq y && itemsBeq xs ys
  | _, _ => false

def QState.beq (s s' : QState) : Bool :=
  s.pos == s'.pos && itemsBeq s.tape s'.tape && Exit.beqs s.log s'.log

/-! ## Readback -/

/-- The number of leading `q`s of a tape, and the rest. -/
def dropQs : List Item → Nat × List Item
  | .q :: r => ((dropQs r).1 + 1, (dropQs r).2)
  | r => (0, r)

/-- Splits `V ++ qˡ ++ [p e] ++ qᵐ` into `(V, l, e, m)`, with `l` as large as possible. -/
def pparse (S : List Item) : Option (List Item × Nat × Exit × Nat) :=
  match dropQs S.reverse with
  | (m, .p e :: r) => some ((dropQs r).2.reverse, (dropQs r).1, e, m)
  | _ => none

/-- The de Bruijn index of lambda `l` of the innermost enclosing point with tape `V`. A point
is given by its tape and its number of leading lambdas. -/
def presolve : List (List Item × Nat) → List Item → Nat → Option Nat
  | [], _, _ => none
  | (U, n) :: fs, V, l =>
    if itemsBeq U V then (if l < n then some (n - 1 - l) else none)
    else (presolve fs V l).map (· + n)

/-- The tape of argument `i` of a head whose exit is `e`, bound by lambda `l` of the point
with tape `V`. -/
def childTape (V : List Item) (l : Nat) (e : Exit) (i : Nat) : List Item :=
  V ++ List.replicate l .q ++ .p e :: (List.replicate i .q ++ [.p .outside])

/-- `PReads t anc U u`: the point with tape `U` of `t`, inside the points `anc` (innermost
first), reads back as `u`. -/
inductive PReads (t : Term) : List (List Item × Nat) → List Item → Tm → Prop
  | node {anc : List (List Item × Nat)} {U S V : List Item} {n l m x : Nat} {e : Exit}
      {args : List Tm} :
      QOut t ⟨.down [], U ++ List.replicate n .q, []⟩ S →
      (∀ k, k < n → ∀ S', ¬ QOut t ⟨.down [], U ++ List.replicate k .q, []⟩ S') →
      pparse S = some (V, l, e, m) →
      presolve ((U, n) :: anc) V l = some x →
      args.length = m →
      (∀ (i : Nat) (a : Tm), args[i]? = some a →
        PReads t ((U, n) :: anc) (childTape V l e i) a) →
      PReads t anc U (Tm.lams n (Tm.apps (.var x) args))

/-- The closed term `t` reads back as `u` with the pointer machine. -/
def PReadsBack (t : Term) (u : Tm) : Prop := PReads t [] [] u

/-- The least `n ≥ k` for which the machine gives an output, if it gets stuck for every
smaller `n` from `k` on; `b` bounds the number of tries. -/
def qfirst (fuel : Nat) (t : Term) (U : List Item) : Nat → Nat → Option (Nat × List Item)
  | 0, _ => none
  | b + 1, k =>
    match qeval fuel t ⟨.down [], U ++ List.replicate k .q, []⟩ with
    | some (some S) => some (k, S)
    | some none => qfirst fuel t U b (k + 1)
    | none => none

/-- Pointer readback with at most `fuel` steps per run and nesting depth below the third
argument. -/
def preadback (fuel : Nat) (t : Term) : Nat → List (List Item × Nat) → List Item → Option Tm
  | 0, _, _ => none
  | d + 1, anc, U =>
    match qfirst fuel t U fuel 0 with
    | some (n, S) =>
      match pparse S with
      | some (V, l, e, m) =>
        match presolve ((U, n) :: anc) V l with
        | some x =>
          match readArgs (fun i => preadback fuel t d ((U, n) :: anc) (childTape V l e i)) m with
          | some args => some (Tm.lams n (Tm.apps (.var x) args))
          | none => none
        | none => none
      | none => none
    | none => none

/-- (B): the pointer machine reads back the normal form of a typed term. -/
def PointerSound : Prop :=
  ∀ (t v : Term) (A : Ty), HasType [] t A → Steps t v → (∀ v', ¬ Step v v') →
    PReadsBack t (erase v)

/-! ## The machine under a beta step

`Beta` describes the contraction of the redex `(λx. M) N` at the address `r` of `t`, with
reduct `t'`. `Beta.state` maps a state of the machine on `t'` to a state of the machine on
`t`. A position in a copy of `N` becomes the position in `N` with one more log entry: the
exit from the occurrence of `x` that the copy replaces. The machine on `t` should get from
the image of a state to the image of the next state in a few steps. This is only tested
(`checkRun`), not proved. -/

/-- `a = e ++ r`. -/
def stripSuffix (r a : Addr) : Option Addr :=
  if a.drop (a.length - r.length) = r ∧ r.length ≤ a.length then
    some (a.take (a.length - r.length))
  else none

/-- Contracts the redex at the address given outermost step first. -/
def contractAt : Term → List Dir → Option Term
  | .app (.lam _ b) u, [] => some (subst 0 u b)
  | .lam A b, .body :: r => (contractAt b r).map (.lam A)
  | .app f u, .fn :: r => (contractAt f r).map (.app · u)
  | .app f u, .arg :: r => (contractAt u r).map (.app f ·)
  | _, _ => none

structure Beta where
  r : Addr
  /-- The occurrences of `x`, as addresses in `M`. -/
  xs : List Addr
  t' : Term

def Beta.of (t : Term) (r : Addr) : Option Beta :=
  match t.sub r with
  | some (.app (.lam _ M) _) =>
    (contractAt t r.reverse).map fun t' => ⟨r, (occs M 0 []).map (·.1), t'⟩
  | _ => none

/-- Where an address of the reduct comes from. -/
inductive Origin where
  /-- Outside the redex. -/
  | same (a : Addr)
  /-- The address `e` of `M`. -/
  | body (e : Addr)
  /-- The address `n` of the copy of `N` at the occurrence `e` of `x`. -/
  | copy (n e : Addr)

def Beta.origin (β : Beta) (a : Addr) : Origin :=
  match stripSuffix β.r a with
  | none => .same a
  | some e' =>
    match β.xs.findSome? fun e => (stripSuffix e e').map (·, e) with
    | some (n, e) => .copy n e
    | none => .body e'

/-- The entry for the argument `N`, in a log `L` that is already translated, for the copy at
the occurrence `e` of `x` and a position at depth `k` in it. -/
def Beta.withArg (β : Beta) (k : Nat) (e : Addr) (L : List Exit) : List Exit :=
  L.take k ++ .mk (e ++ .body :: .fn :: β.r) ((L.drop k).take (argDepth e)) ::
    L.drop (k + argDepth e)

mutual
def Beta.exit (β : Beta) : Exit → Exit
  | .mk o σ =>
    match binderOf β.t' o, β.origin o with
    | none, _ => .mk o (Beta.exits β σ)
    | some _, .same a => .mk a (Beta.exits β σ)
    | some _, .body e => .mk (e ++ .body :: .fn :: β.r) (Beta.exits β σ)
    | some b, .copy n e =>
      -- a variable bound inside the copy keeps its saved entries
      if (stripSuffix (e ++ β.r) b).isSome then .mk (n ++ .arg :: β.r) (Beta.exits β σ)
      else .mk (n ++ .arg :: β.r) (β.withArg (argDepth n) e (Beta.exits β σ))
def Beta.exits (β : Beta) : List Exit → List Exit
  | [] => []
  | e :: es => Beta.exit β e :: Beta.exits β es
end

def Beta.item (β : Beta) : Item → Item
  | .q => .q
  | .p e => .p (β.exit e)

/-- The state of the machine on `t` that belongs to a state of the machine on `t'`. -/
def Beta.state (β : Beta) (s : QState) : QState :=
  let at' (a : Addr) : Pos :=
    match s.pos with
    | .down _ => .down a
    | .up _ => .up a
  let L := β.exits s.log
  let T := s.tape.map β.item
  match β.origin s.pos.addr with
  | .same a => ⟨at' a, T, L⟩
  | .body e => ⟨at' (e ++ .body :: .fn :: β.r), T, L⟩
  | .copy n e => ⟨at' (n ++ .arg :: β.r), T, β.withArg (argDepth n) e L⟩

/-- The machine on `t` gets from `s` to `goal` in at least one and at most `k` steps. -/
def reaches (t : Term) (goal : QState) : Nat → QState → Bool
  | 0, _ => false
  | k + 1, s =>
    match qstep t s with
    | .next s' => s'.beq goal || reaches t goal k s'
    | _ => false

/-- The machine on `t` gets from `s` to the root with the tape `T` in at most `k` steps. -/
def finishes (t : Term) (T : List Item) : Nat → QState → Bool
  | 0, _ => false
  | k + 1, s =>
    match qstep t s with
    | .next s' => finishes t T k s'
    | .done T' => itemsBeq T T'
    | .stuck => false

/-- The machine on `t` gets stuck from `s` in at most `k` steps. -/
def sticks (t : Term) : Nat → QState → Bool
  | 0, _ => false
  | k + 1, s =>
    match qstep t s with
    | .next s' => sticks t k s'
    | .done _ => false
    | .stuck => true

/-- Runs the machine on the reduct, and checks at every step that the machine on `t` follows
within 8 steps. The result is the outcome on the reduct (`none`: stuck), or what went wrong. -/
def checkRun (β : Beta) (t : Term) : Nat → QState → Except String (Option (List Item))
  | 0, _ => .error "out of steps"
  | k + 1, s =>
    match qstep β.t' s with
    | .next s' =>
      if reaches t (β.state s') 8 (β.state s) then checkRun β t k s' else .error "step"
    | .done T => if finishes t (T.map β.item) 8 (β.state s) then .ok (some T) else .error "end"
    | .stuck => if sticks t 8 (β.state s) then .ok none else .error "stuck"

end LSL
