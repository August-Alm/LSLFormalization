import Formalization.LSL

/-!
# Context semantics: the token machine

A token walks over a term with sharing paths. It carries one stack per fan label (the
exponential stacks) and one stack for lambdas and applications (the multiplicative stack).
At a lambda, `q` stands for the body and `p` for the variable; at an application, `q` stands
for the result and `p` for the argument.

This is the context semantics of the paper (its Table 1), with a term in place of a
proof net: an argument plays the role of a box.
-/

namespace LSL

inductive Dir where
  | body
  | fn
  | arg
  deriving DecidableEq, Repr

/-- The address of a subterm: the steps from the root, innermost first. -/
abbrev Addr := List Dir

def Term.child : Term → Dir → Option Term
  | .lam _ t, .body => some t
  | .app t _, .fn => some t
  | .app _ u, .arg => some u
  | _, _ => none

def Term.sub (t : Term) (a : Addr) : Option Term :=
  a.foldr (fun d r => r.bind (·.child d)) (some t)

/-- The lambda that binds variable `i` at address `a` (right), or the number of the free
variable it is (left). -/
def binder : Addr → Nat → Nat ⊕ Addr
  | [], i => .inl i
  | .body :: a, 0 => .inr a
  | .body :: a, i + 1 => binder a i
  | .fn :: a, i => binder a i
  | .arg :: a, i => binder a i

/-- The occurrences of variable `i` in the subterm `t` at address `a`, with their paths. -/
def occs : Term → Nat → Addr → List (Addr × Path)
  | .var j π, i, a => if j = i then [(a, π)] else []
  | .lam _ t, i, a => occs t (i + 1) (.body :: a)
  | .app t u, i, a => occs t i (.fn :: a) ++ occs u i (.arg :: a)

/-! ## Stacks -/

abbrev Stacks := Label → List Side

def Stacks.empty : Stacks := fun _ => []

def Stacks.push (S : Stacks) (l : Label) (s : Side) : Stacks :=
  fun k => if k = l then s :: S k else S k

/-- Pushes a path walked from the occurrence towards the binder. -/
def pushPath (S : Stacks) : Path → Stacks
  | [] => S
  | (l, s) :: π => pushPath (Stacks.push S l s) π

/-- Pops a path walked from the binder towards the occurrence (so given binder side first);
fails if some stack does not have the expected side on top. -/
def popPath (S : Stacks) : Path → Option Stacks
  | [] => some S
  | (l, s) :: π =>
    match S l with
    | s' :: rest => if s' = s then popPath (fun k => if k = l then rest else S k) π else none
    | [] => none

/-- The occurrence that the stacks select, and the stacks after the fans have been passed. -/
def select (S : Stacks) (os : List (Addr × Path)) : Option (Addr × Stacks) :=
  os.findSome? fun (a, π) => (popPath S π.reverse).map fun S' => (a, S')

/-! ## The machine -/

/-- Where the token is: about to enter a subterm from above, or leaving it upwards. -/
inductive Pos where
  | down (a : Addr)
  | up (a : Addr)
  deriving DecidableEq, Repr

structure State where
  pos : Pos
  exp : Stacks
  mul : List Side

/-- A conclusion: the root of the term or one of its free variables. -/
inductive Concl where
  | root
  | free (k : Nat)
  deriving DecidableEq, Repr

abbrev Output := Concl × Stacks × List Side

inductive Result where
  | next (s : State)
  | done (out : Output)
  | stuck

def step (t : Term) (s : State) : Result :=
  match s.pos with
  | .down a =>
    match t.sub a with
    | some (.app _ _) => .next ⟨.down (.fn :: a), s.exp, .q :: s.mul⟩
    | some (.lam _ b) =>
      match s.mul with
      | .q :: m => .next ⟨.down (.body :: a), s.exp, m⟩
      | .p :: m =>
        match select s.exp (occs b 0 (.body :: a)) with
        | some (o, S) => .next ⟨.up o, S, m⟩
        | none => .stuck
      | [] => .stuck
    | some (.var i π) =>
      match binder a i with
      | .inr b => .next ⟨.up b, pushPath s.exp π, .p :: s.mul⟩
      | .inl k => .done (.free k, pushPath s.exp π, s.mul)
    | none => .stuck
  | .up [] => .done (.root, s.exp, s.mul)
  | .up (.body :: a) => .next ⟨.up a, s.exp, .q :: s.mul⟩
  | .up (.fn :: a) =>
    match s.mul with
    | .p :: m => .next ⟨.down (.arg :: a), s.exp, m⟩
    | .q :: m => .next ⟨.up a, s.exp, m⟩
    | [] => .stuck
  | .up (.arg :: a) => .next ⟨.down (.fn :: a), s.exp, .p :: s.mul⟩

/-- Runs the machine for at most `n` steps. -/
def run : Nat → Term → State → Option Output
  | 0, _, _ => none
  | n + 1, t, s =>
    match step t s with
    | .next s' => run n t s'
    | .done out => some out
    | .stuck => none

/-- The state in which a token enters at a conclusion. -/
def enter (t : Term) (c : Concl) (D : Stacks) (T : List Side) : Option State :=
  match c with
  | .root => some ⟨.down [], D, T⟩
  | .free k => (select D (occs t k [])).map fun (o, S) => ⟨.up o, S, T⟩

/-- The context semantics of `t`: a token that enters at `c` with stacks `D` and `T` leaves
with output `out`. It is a partial function, because `run` is one. -/
def Sem (t : Term) (c : Concl) (D : Stacks) (T : List Side) (out : Output) : Prop :=
  ∃ s n, enter t c D T = some s ∧ run n t s = some out

def Defined (t : Term) (c : Concl) (D : Stacks) (T : List Side) : Prop :=
  ∃ out, Sem t c D T out

theorem sem_root {t : Term} {D : Stacks} {T : List Side} {out : Output} :
    Sem t .root D T out ↔ ∃ n, run n t ⟨.down [], D, T⟩ = some out := by
  constructor
  · rintro ⟨s, n, hs, hn⟩
    simp only [enter] at hs
    cases hs
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, n, rfl, hn⟩

/-! ## A runner that tells stuck from out of steps -/

/-- Like `run`, but `some none` means the token got stuck and `none` that the steps ran out. -/
def eval : Nat → Term → State → Option (Option Output)
  | 0, _, _ => none
  | n + 1, t, s =>
    match step t s with
    | .next s' => eval n t s'
    | .done out => some (some out)
    | .stuck => some none

theorem eval_out (t : Term) : ∀ (n : Nat) (s : State) (out : Output),
    eval n t s = some (some out) → run n t s = some out
  | 0, _, _, h => by simp [eval] at h
  | n + 1, s, out, h => by
    simp only [eval] at h
    simp only [run]
    cases hs : step t s with
    | next s' =>
      simp only [hs] at h ⊢
      exact eval_out t n s' out h
    | done o => simpa [hs] using h
    | stuck => simp [hs] at h

theorem eval_stuck (t : Term) : ∀ (n : Nat) (s : State),
    eval n t s = some none → ∀ m : Nat, run m t s = none
  | 0, _, h, _ => by simp [eval] at h
  | _ + 1, _, _, 0 => rfl
  | n + 1, s, h, m + 1 => by
    simp only [eval] at h
    simp only [run]
    cases hs : step t s with
    | next s' =>
      simp only [hs] at h ⊢
      exact eval_stuck t n s' h m
    | done o => simp [hs] at h
    | stuck => rfl

end LSL
