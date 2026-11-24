import Formalization.Coherence

/-!
# The pointer machine

The pointer machine walks over a term like the token machine, but it does not use the sharing
paths. When it leaves a variable for its binder it records the occurrence, and it comes back
to exactly that occurrence. Its log has one entry for each argument around the token: the
exit through which that argument was entered.

The machine defined here also keeps the exits that it has not yet returned through, newest
first, and it stops (`parted`) when a return is not to the occurrence of the newest exit to
that binder. Until it stops, the token machine makes the same steps (`follows`), provided
the fan labels of different binders are apart, as they are in `share t`.

So the token machine is sound on `share t` if the returns of the pointer machine to each
binder come in last-in-first-out order. That is a statement about plain terms: it does not
mention labels. `FirstRunLifo` states it for the first run on a locally safe term. It follows
from `FirstRunClear`, which does not mention the history either (`firstRunLifo_of_clear`);
both are proved in `FirstRun.lean`.

The machine is `stuck`, not `parted`, at a lambda that does not bind the occurrence it is
sent back to. That would be a fault of the pointers themselves, not of the order of returns.
-/

namespace LSL

/-- An exit from a variable to its binder: the occurrence, and the log entries left behind. -/
inductive Exit where
  | mk (occ : Addr) (saved : List Exit)

def Exit.occ : Exit → Addr
  | .mk o _ => o

def Exit.saved : Exit → List Exit
  | .mk _ s => s

inductive Item where
  | q
  | p (e : Exit)

def Item.side : Item → Side
  | .q => .q
  | .p _ => .p

/-- The number of arguments around the address. -/
def argDepth (a : Addr) : Nat := a.count .arg

/-- The lambda that binds the variable at `o`. -/
def binderOf (t : Term) (o : Addr) : Option Addr :=
  match t.sub o with
  | some (.var i _) =>
    match binder o i with
    | .inr b => some b
    | .inl _ => none
  | _ => none

/-- The sharing path of the bound variable at `o`. -/
def pathAt (t : Term) (o : Addr) : Path :=
  match t.sub o with
  | some (.var i π) =>
    match binder o i with
    | .inr _ => π
    | .inl _ => []
  | _ => []

structure PState where
  pos : Pos
  tape : List Item
  log : List Exit
  /-- The occurrences of the exits not yet returned through, newest first. -/
  hist : List Addr

inductive PResult where
  | next (s : PState)
  | done (tape : List Item) (hist : List Addr)
  | stuck
  /-- A return that is not to the newest exit to its binder. -/
  | parted

/-- Takes the newest exit to the binder `b` out of the history. -/
def popNewest (t : Term) (b : Addr) : List Addr → Option (Addr × List Addr)
  | [] => none
  | o :: H =>
    if binderOf t o = some b then some (o, H)
    else (popNewest t b H).map fun (o', H') => (o', o :: H')

def pstep (t : Term) (s : PState) : PResult :=
  match s.pos with
  | .down a =>
    match t.sub a with
    | some (.app _ _) => .next ⟨.down (.fn :: a), .q :: s.tape, s.log, s.hist⟩
    | some (.lam _ _) =>
      match s.tape with
      | .q :: T => .next ⟨.down (.body :: a), T, s.log, s.hist⟩
      | .p e :: T =>
        if binderOf t e.occ = some a then
          match popNewest t a s.hist with
          | some (o, H) => if o = e.occ then .next ⟨.up o, T, e.saved ++ s.log, H⟩ else .parted
          | none => .parted
        else .stuck
      | [] => .stuck
    | some (.var i _) =>
      match binder a i with
      | .inr b =>
        .next ⟨.up b, .p ⟨a, s.log.take (argDepth a - argDepth b)⟩ :: s.tape,
          s.log.drop (argDepth a - argDepth b), a :: s.hist⟩
      | .inl _ => .stuck
    | none => .stuck
  | .up [] => .done s.tape s.hist
  | .up (.body :: a) => .next ⟨.up a, .q :: s.tape, s.log, s.hist⟩
  | .up (.fn :: a) =>
    match s.tape with
    | .p e :: T => .next ⟨.down (.arg :: a), T, e :: s.log, s.hist⟩
    | .q :: T => .next ⟨.up a, T, s.log, s.hist⟩
    | [] => .stuck
  | .up (.arg :: a) =>
    match s.log with
    | e :: L => .next ⟨.down (.fn :: a), .p e :: s.tape, L, s.hist⟩
    | [] => .stuck

/-- Runs the pointer machine for at most `n` steps; `none` also if it stops before the end. -/
def prun : Nat → Term → PState → Option (List Item × List Addr)
  | 0, _, _ => none
  | n + 1, t, s =>
    match pstep t s with
    | .next s' => prun n t s'
    | .done T H => some (T, H)
    | _ => none

inductive PReach (t : Term) : PState → PState → Prop
  | refl {s : PState} : PReach t s s
  | head {s s' s'' : PState} : pstep t s = .next s' → PReach t s' s'' → PReach t s s''

/-! ## The token machine follows -/

/-- The stacks of the token machine after the exits in the history, starting from `S`. -/
def stacksOf (t : Term) (S : Stacks) : List Addr → Stacks
  | [] => S
  | o :: H => pushPath (stacksOf t S H) (pathAt t o)

/-- The state of the token machine that belongs to a state of the pointer machine. -/
def PState.abs (t : Term) (S : Stacks) (s : PState) : State :=
  ⟨s.pos, stacksOf t S s.hist, s.tape.map Item.side⟩

/-- Variables with different binders have no fan label in common. -/
def Apart (t : Term) : Prop :=
  ∀ o₁ o₂ : Addr, binderOf t o₁ ≠ binderOf t o₂ →
    ∀ l : Label, bproj l (pathAt t o₁) = [] ∨ bproj l (pathAt t o₂) = []

theorem stacksOf_apply (t : Term) (S : Stacks) (l : Label) : ∀ H : List Addr,
    stacksOf t S H l = (H.flatMap fun o => bproj l (pathAt t o)) ++ S l
  | [] => by simp [stacksOf]
  | o :: H => by
    simp only [stacksOf, pushPath_apply, stacksOf_apply t S l H, List.flatMap_cons,
      List.append_assoc]

theorem popPath_of_apply : ∀ (σ : Path) (S S' : Stacks), (∀ l, S l = fproj l σ ++ S' l) →
    popPath S σ = some S'
  | [], S, S', h => by
    have e : S = S' := funext fun l => by simpa [fproj] using h l
    rw [e]
    rfl
  | (l', s) :: σ, S, S', h => by
    have h' := h l'
    simp only [fproj, ite_true, List.cons_append] at h'
    simp only [popPath, h', ite_true]
    refine popPath_of_apply σ _ S' fun l => ?_
    by_cases hl : l = l'
    · subst hl
      simp
    · have h2 := h l
      have hl' : ¬ l' = l := fun e => hl e.symm
      simp only [fproj, hl', ite_false] at h2
      simpa [hl] using h2

theorem popNewest_spec (t : Term) (b : Addr) : ∀ (H : List Addr) (o : Addr) (H' : List Addr),
    popNewest t b H = some (o, H') →
      binderOf t o = some b ∧ ∃ H₁ H₂, H = H₁ ++ o :: H₂ ∧ H' = H₁ ++ H₂ ∧
        ∀ h ∈ H₁, binderOf t h ≠ some b
  | [], _, _, h => by simp [popNewest] at h
  | x :: H, o, H', h => by
    simp only [popNewest] at h
    by_cases hx : binderOf t x = some b
    · simp only [hx, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hx, [], _, rfl, rfl, by simp⟩
    · simp only [hx, ite_false] at h
      cases hr : popNewest t b H with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨o', H''⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hb, H₁, H₂, e₁, e₂, hall⟩ := popNewest_spec t b H _ _ hr
        refine ⟨hb, x :: H₁, H₂, by simp [e₁], by simp [e₂], ?_⟩
        intro h' hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hx
        · exact hall h' hm

theorem binderOf_mem {t : Term} {o b : Addr} (h : binderOf t o = some b) :
    ∃ A body, t.sub b = some (.lam A body) ∧ (o, pathAt t o) ∈ occs body 0 (.body :: b) := by
  unfold binderOf at h
  cases hso : t.sub o with
  | none => simp [hso] at h
  | some u =>
    cases u with
    | var i π =>
      simp only [hso] at h
      cases hbi : binder o i with
      | inl k => simp [hbi] at h
      | inr b' =>
        simp only [hbi, Option.some.injEq] at h
        rw [h] at hbi
        obtain ⟨A, body, hs, hm⟩ := occ_mem hso hbi
        exact ⟨A, body, hs, by simpa [pathAt, hso, hbi] using hm⟩
    | lam _ _ => simp [hso] at h
    | app _ _ => simp [hso] at h

theorem pathAt_of_none {t : Term} {o : Addr} (h : binderOf t o = none) : pathAt t o = [] := by
  unfold binderOf at h
  unfold pathAt
  cases hso : t.sub o with
  | none => rfl
  | some u =>
    cases u with
    | var i π =>
      simp only [hso] at h
      cases hbi : binder o i with
      | inl k => simp [hbi]
      | inr b => simp [hbi] at h
    | lam _ _ => rfl
    | app _ _ => rfl

/-- At a lambda the stacks select the occurrence of the newest exit to it. -/
theorem select_newest {t : Term} (hd : Distinct t) (ha : Apart t) (S : Stacks) {a : Addr}
    {A : Ty} {b : Term} (hsub : t.sub a = some (.lam A b)) {H H' : List Addr} {o : Addr}
    (hpop : popNewest t a H = some (o, H')) :
    select (stacksOf t S H) (occs b 0 (.body :: a)) = some (o, stacksOf t S H') := by
  obtain ⟨hb, H₁, H₂, rfl, rfl, hall⟩ := popNewest_spec t a H o H' hpop
  have hocc : (o, pathAt t o) ∈ occs b 0 (.body :: a) := by
    obtain ⟨A', body, hs', hm⟩ := binderOf_mem hb
    rw [hsub] at hs'
    cases hs'
    exact hm
  have hp : ((occs b 0 (.body :: a)).map Prod.snd).Pairwise Clash := by
    rw [occs_paths]
    exact (distinct_sub hd a _ hsub).1
  refine select_unique _ o _ _ _ hp hocc (popPath_of_apply _ _ _ fun l => ?_)
  show _ = bproj l (pathAt t o) ++ _
  rw [stacksOf_apply, stacksOf_apply]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  by_cases hl : bproj l (pathAt t o) = []
  · simp [hl]
  · have hX : (H₁.flatMap fun h => bproj l (pathAt t h)) = [] :=
      List.flatMap_eq_nil_iff.mpr fun h hm =>
        (ha h o (by rw [hb]; exact hall h hm) l).resolve_right hl
    simp [hX]

/-- What the token machine does where the pointer machine makes a step or finishes. -/
def Follows (t : Term) (S : Stacks) (s : PState) : PResult → Prop
  | .next s' => step t (s.abs t S) = .next (s'.abs t S)
  | .done T H => step t (s.abs t S) = .done (.root, stacksOf t S H, T.map Item.side)
  | _ => True

theorem follows {t : Term} (hd : Distinct t) (ha : Apart t) (S : Stacks) (s : PState) :
    Follows t S s (pstep t s) := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | down a =>
    cases hsub : t.sub a with
    | none => simp [pstep, hsub, Follows]
    | some u =>
      cases u with
      | var i π =>
        cases hb : binder a i with
        | inl k => simp [pstep, hsub, hb, Follows]
        | inr b =>
          have hp : pathAt t a = π := by simp [pathAt, hsub, hb]
          simp only [pstep, hsub, hb, Follows, PState.abs, stacksOf, hp, List.map_cons,
            Item.side]
          exact step_var hsub hb _ _
      | lam A b =>
        cases tape with
        | nil => simp [pstep, hsub, Follows]
        | cons x T =>
          cases x with
          | q =>
            simp only [pstep, hsub, Follows, PState.abs, List.map_cons, Item.side]
            exact step_lam_q hsub _ _
          | p e =>
            by_cases hbe : binderOf t e.occ = some a
            · cases hpop : popNewest t a hist with
              | none => simp [pstep, hsub, hbe, hpop, Follows]
              | some r =>
                obtain ⟨o, H⟩ := r
                by_cases ho : o = e.occ
                · subst ho
                  simp only [pstep, hsub, hbe, hpop, ite_true, Follows, PState.abs, List.map_cons,
                    Item.side]
                  exact step_lam_p hsub (select_newest hd ha S hsub hpop) _
                · simp [pstep, hsub, hbe, hpop, ho, Follows]
            · simp [pstep, hsub, hbe, Follows]
      | app f u =>
        simp only [pstep, hsub, Follows, PState.abs, List.map_cons, Item.side]
        exact step_app hsub _ _
  | up a =>
    cases a with
    | nil => simp [pstep, Follows, PState.abs, step]
    | cons d a =>
      cases d with
      | body => simp [pstep, Follows, PState.abs, step, Item.side]
      | fn =>
        cases tape with
        | nil => simp [pstep, Follows]
        | cons x T => cases x <;> simp [pstep, Follows, PState.abs, step, Item.side]
      | arg =>
        cases log with
        | nil => simp [pstep, Follows]
        | cons e L => simp [pstep, Follows, PState.abs, step, Item.side]

/-- A run of the pointer machine that reaches the root is a run of the token machine. -/
theorem run_of_prun {t : Term} (hd : Distinct t) (ha : Apart t) (S : Stacks) :
    ∀ (n : Nat) (s : PState) (T : List Item) (H : List Addr), prun n t s = some (T, H) →
      run n t (s.abs t S) = some (.root, stacksOf t S H, T.map Item.side)
  | 0, _, _, _, h => by simp [prun] at h
  | n + 1, s, T, H, h => by
    have hf := follows hd ha S s
    simp only [prun] at h
    simp only [run]
    cases hp : pstep t s with
    | next s' =>
      simp only [hp] at h hf
      simp only [Follows] at hf
      simp only [hf]
      exact run_of_prun hd ha S n s' T H h
    | done T' H' =>
      simp only [hp, Option.some.injEq, Prod.mk.injEq] at h hf
      obtain ⟨rfl, rfl⟩ := h
      simp only [Follows] at hf
      simp only [hf]
    | stuck => simp [hp] at h
    | parted => simp [hp] at h

/-! ## The labels of `share t` are apart

Every lambda of `share t` has a range of labels of its own. -/

/-- The labels on the variables bound in `t` lie between `lo` and `hi`, those of different
lambdas in disjoint ranges. -/
def Ranged : Term → Nat → Nat → Prop
  | .var _ _, lo, hi => lo ≤ hi
  | .lam _ b, lo, hi =>
    ∃ mid, lo ≤ mid ∧
      (∀ π ∈ paths 0 b, ∀ (l : Nat) (sd : Side), (l, sd) ∈ π → lo ≤ l ∧ l < mid) ∧ Ranged b mid hi
  | .app f u, lo, hi => ∃ mid, Ranged f lo mid ∧ Ranged u mid hi

theorem ranged_le : ∀ (t : Term) (lo hi : Nat), Ranged t lo hi → lo ≤ hi
  | .var _ _, _, _, h => h
  | .lam _ b, lo, hi, h => by
    simp only [Ranged] at h
    obtain ⟨mid, h1, _, h3⟩ := h
    exact Nat.le_trans h1 (ranged_le b mid hi h3)
  | .app f u, lo, hi, h => by
    simp only [Ranged] at h
    obtain ⟨mid, h1, h2⟩ := h
    exact Nat.le_trans (ranged_le f lo mid h1) (ranged_le u mid hi h2)

/-- The labels of a lambda inside a ranged term lie in the range. -/
theorem ranged_labels : ∀ (r : List Dir) (t : Term) (lo hi : Nat), Ranged t lo hi →
    ∀ (A : Ty) (body : Term), t.sub r.reverse = some (.lam A body) →
      ∀ π ∈ paths 0 body, ∀ (l : Nat) (sd : Side), (l, sd) ∈ π → lo ≤ l ∧ l < hi
  | [], t, lo, hi, h, A, body, hs, π, hπ, l, sd, hx => by
    simp only [List.reverse_nil, Term.sub, List.foldr_nil, Option.some.injEq] at hs
    subst hs
    simp only [Ranged] at h
    obtain ⟨mid, h1, h2, h3⟩ := h
    have := h2 π hπ l sd hx
    have := ranged_le _ _ _ h3
    omega
  | d :: r, t, lo, hi, h, A, body, hs, π, hπ, l, sd, hx => by
    rw [List.reverse_cons, sub_append] at hs
    cases t with
    | var j ρ => cases d <;> simp [Term.sub, Term.child] at hs
    | lam B s =>
      cases d with
      | body =>
        have hs' : s.sub r.reverse = some (.lam A body) := by
          simpa [Term.sub, Term.child] using hs
        simp only [Ranged] at h
        obtain ⟨mid, h1, h2, h3⟩ := h
        have := ranged_labels r s mid hi h3 A body hs' π hπ l sd hx
        omega
      | fn => simp [Term.sub, Term.child] at hs
      | arg => simp [Term.sub, Term.child] at hs
    | app f u =>
      simp only [Ranged] at h
      obtain ⟨mid, h1, h2⟩ := h
      have := ranged_le _ _ _ h1
      have := ranged_le _ _ _ h2
      cases d with
      | body => simp [Term.sub, Term.child] at hs
      | fn =>
        have hs' : f.sub r.reverse = some (.lam A body) := by
          simpa [Term.sub, Term.child] using hs
        have := ranged_labels r f lo mid h1 A body hs' π hπ l sd hx
        omega
      | arg =>
        have hs' : u.sub r.reverse = some (.lam A body) := by
          simpa [Term.sub, Term.child] using hs
        have := ranged_labels r u mid hi h2 A body hs' π hπ l sd hx
        omega

/-- Two lambdas of a ranged term have no label in common. -/
theorem ranged_apart : ∀ (r₁ r₂ : List Dir) (t : Term) (lo hi : Nat), Ranged t lo hi →
    r₁ ≠ r₂ → ∀ (A₁ A₂ : Ty) (b₁ b₂ : Term), t.sub r₁.reverse = some (.lam A₁ b₁) →
      t.sub r₂.reverse = some (.lam A₂ b₂) →
        ∀ π₁ ∈ paths 0 b₁, ∀ π₂ ∈ paths 0 b₂, ∀ (l₁ : Nat) (s₁ : Side), (l₁, s₁) ∈ π₁ →
          ∀ (l₂ : Nat) (s₂ : Side), (l₂, s₂) ∈ π₂ → l₁ ≠ l₂
  | [], [], _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | [], d :: r₂, t, lo, hi, h, _, A₁, A₂, b₁, b₂, hs₁, hs₂, π₁, hπ₁, π₂, hπ₂, l₁, s₁, hx₁, l₂, s₂,
      hx₂ => by
    simp only [List.reverse_nil, Term.sub, List.foldr_nil, Option.some.injEq] at hs₁
    subst hs₁
    rw [List.reverse_cons, sub_append] at hs₂
    simp only [Ranged] at h
    obtain ⟨mid, h1, h2, h3⟩ := h
    cases d with
    | body =>
      have hs' : b₁.sub r₂.reverse = some (.lam A₂ b₂) := by
        simpa [Term.sub, Term.child] using hs₂
      have := h2 π₁ hπ₁ l₁ s₁ hx₁
      have := ranged_labels r₂ b₁ mid hi h3 A₂ b₂ hs' π₂ hπ₂ l₂ s₂ hx₂
      omega
    | fn => simp [Term.sub, Term.child] at hs₂
    | arg => simp [Term.sub, Term.child] at hs₂
  | d :: r₁, [], t, lo, hi, h, _, A₁, A₂, b₁, b₂, hs₁, hs₂, π₁, hπ₁, π₂, hπ₂, l₁, s₁, hx₁, l₂, s₂,
      hx₂ => by
    simp only [List.reverse_nil, Term.sub, List.foldr_nil, Option.some.injEq] at hs₂
    subst hs₂
    rw [List.reverse_cons, sub_append] at hs₁
    simp only [Ranged] at h
    obtain ⟨mid, h1, h2, h3⟩ := h
    cases d with
    | body =>
      have hs' : b₂.sub r₁.reverse = some (.lam A₁ b₁) := by
        simpa [Term.sub, Term.child] using hs₁
      have := h2 π₂ hπ₂ l₂ s₂ hx₂
      have := ranged_labels r₁ b₂ mid hi h3 A₁ b₁ hs' π₁ hπ₁ l₁ s₁ hx₁
      omega
    | fn => simp [Term.sub, Term.child] at hs₁
    | arg => simp [Term.sub, Term.child] at hs₁
  | d₁ :: r₁, d₂ :: r₂, t, lo, hi, h, hne, A₁, A₂, b₁, b₂, hs₁, hs₂, π₁, hπ₁, π₂, hπ₂, l₁, s₁, hx₁,
      l₂, s₂, hx₂ => by
    rw [List.reverse_cons, sub_append] at hs₁ hs₂
    cases t with
    | var j ρ => cases d₁ <;> simp [Term.sub, Term.child] at hs₁
    | lam B s =>
      simp only [Ranged] at h
      obtain ⟨mid, h1, h2, h3⟩ := h
      cases d₁ with
      | body =>
        cases d₂ with
        | body =>
          have hs₁' : s.sub r₁.reverse = some (.lam A₁ b₁) := by
            simpa [Term.sub, Term.child] using hs₁
          have hs₂' : s.sub r₂.reverse = some (.lam A₂ b₂) := by
            simpa [Term.sub, Term.child] using hs₂
          exact ranged_apart r₁ r₂ s mid hi h3 (fun e => hne (by rw [e])) A₁ A₂ b₁ b₂ hs₁' hs₂'
            π₁ hπ₁ π₂ hπ₂ l₁ s₁ hx₁ l₂ s₂ hx₂
        | fn => simp [Term.sub, Term.child] at hs₂
        | arg => simp [Term.sub, Term.child] at hs₂
      | fn => simp [Term.sub, Term.child] at hs₁
      | arg => simp [Term.sub, Term.child] at hs₁
    | app f u =>
      simp only [Ranged] at h
      obtain ⟨mid, h1, h2⟩ := h
      cases d₁ with
      | body => simp [Term.sub, Term.child] at hs₁
      | fn =>
        have hs₁' : f.sub r₁.reverse = some (.lam A₁ b₁) := by
          simpa [Term.sub, Term.child] using hs₁
        cases d₂ with
        | body => simp [Term.sub, Term.child] at hs₂
        | fn =>
          have hs₂' : f.sub r₂.reverse = some (.lam A₂ b₂) := by
            simpa [Term.sub, Term.child] using hs₂
          exact ranged_apart r₁ r₂ f lo mid h1 (fun e => hne (by rw [e])) A₁ A₂ b₁ b₂ hs₁' hs₂'
            π₁ hπ₁ π₂ hπ₂ l₁ s₁ hx₁ l₂ s₂ hx₂
        | arg =>
          have hs₂' : u.sub r₂.reverse = some (.lam A₂ b₂) := by
            simpa [Term.sub, Term.child] using hs₂
          have := ranged_labels r₁ f lo mid h1 A₁ b₁ hs₁' π₁ hπ₁ l₁ s₁ hx₁
          have := ranged_labels r₂ u mid hi h2 A₂ b₂ hs₂' π₂ hπ₂ l₂ s₂ hx₂
          omega
      | arg =>
        have hs₁' : u.sub r₁.reverse = some (.lam A₁ b₁) := by
          simpa [Term.sub, Term.child] using hs₁
        cases d₂ with
        | body => simp [Term.sub, Term.child] at hs₂
        | fn =>
          have hs₂' : f.sub r₂.reverse = some (.lam A₂ b₂) := by
            simpa [Term.sub, Term.child] using hs₂
          have := ranged_labels r₁ u mid hi h2 A₁ b₁ hs₁' π₁ hπ₁ l₁ s₁ hx₁
          have := ranged_labels r₂ f lo mid h1 A₂ b₂ hs₂' π₂ hπ₂ l₂ s₂ hx₂
          omega
        | arg =>
          have hs₂' : u.sub r₂.reverse = some (.lam A₂ b₂) := by
            simpa [Term.sub, Term.child] using hs₂
          exact ranged_apart r₁ r₂ u mid hi h2 (fun e => hne (by rw [e])) A₁ A₂ b₁ b₂ hs₁' hs₂'
            π₁ hπ₁ π₂ hπ₂ l₁ s₁ hx₁ l₂ s₂ hx₂

theorem fproj_ne_nil {l : Label} : ∀ {σ : Path}, fproj l σ ≠ [] → ∃ s, (l, s) ∈ σ
  | [], h => absurd rfl h
  | (l', s) :: σ, h => by
    by_cases hl : l' = l
    · subst hl
      exact ⟨s, List.mem_cons_self⟩
    · simp only [fproj, hl, ite_false] at h
      obtain ⟨s', hs'⟩ := fproj_ne_nil h
      exact ⟨s', List.mem_cons_of_mem _ hs'⟩

theorem apart_of_ranged {t : Term} {lo hi : Nat} (h : Ranged t lo hi) : Apart t := by
  intro o₁ o₂ hne l
  cases h₁ : binderOf t o₁ with
  | none => exact .inl (by rw [pathAt_of_none h₁]; rfl)
  | some b₁ =>
    cases h₂ : binderOf t o₂ with
    | none => exact .inr (by rw [pathAt_of_none h₂]; rfl)
    | some b₂ =>
      rw [h₁, h₂] at hne
      obtain ⟨A₁, body₁, hs₁, hm₁⟩ := binderOf_mem h₁
      obtain ⟨A₂, body₂, hs₂, hm₂⟩ := binderOf_mem h₂
      have hp₁ : pathAt t o₁ ∈ paths 0 body₁ := by
        rw [← occs_paths body₁ 0 (.body :: b₁)]
        exact List.mem_map.mpr ⟨_, hm₁, rfl⟩
      have hp₂ : pathAt t o₂ ∈ paths 0 body₂ := by
        rw [← occs_paths body₂ 0 (.body :: b₂)]
        exact List.mem_map.mpr ⟨_, hm₂, rfl⟩
      by_cases e₁ : bproj l (pathAt t o₁) = []
      · exact .inl e₁
      · by_cases e₂ : bproj l (pathAt t o₂) = []
        · exact .inr e₂
        · obtain ⟨s₁, m₁⟩ := fproj_ne_nil e₁
          obtain ⟨s₂, m₂⟩ := fproj_ne_nil e₂
          exact absurd rfl (ranged_apart b₁.reverse b₂.reverse t lo hi h
            (fun e => hne (by rw [List.reverse_inj.mp e])) A₁ A₂ body₁ body₂
            (by rw [List.reverse_reverse]; exact hs₁) (by rw [List.reverse_reverse]; exact hs₂)
            _ hp₁ _ hp₂ l s₁ (List.mem_reverse.mp m₁) l s₂ (List.mem_reverse.mp m₂))

theorem mem_chain {base n k l : Nat} {sd : Side} (h : (l, sd) ∈ chain base n k) :
    base ≤ l ∧ l < base + (n - 1) := by
  unfold chain at h
  rcases List.mem_append.mp h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      omega
    · simp at h
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hj' : j < min k (n - 1) := by simpa using hj
    have := (Prod.mk.inj he).1
    omega

theorem ranged_shareAux : ∀ (t : Term) (env : List (Nat × Nat)) (seen : List Nat) (next : Nat),
    env.length = seen.length →
      Ranged (shareAux t env seen next).1 next (shareAux t env seen next).2.2
  | .var j π, env, seen, next, _ => by
    simp only [shareAux]
    split <;> simp [Ranged]
  | .lam A b, env, seen, next, hlen => by
    have hlen' : ((next, occurrences 0 b) :: env).length = (0 :: seen).length := by simp [hlen]
    have hp := ((shareAux_paths b _ _ (next + (occurrences 0 b - 1)) hlen').2 0 next
      (occurrences 0 b) 0 rfl rfl).2
    rw [shareAux_lam]
    simp only [Ranged]
    refine ⟨next + (occurrences 0 b - 1), Nat.le_add_right _ _, ?_, ranged_shareAux b _ _ _ hlen'⟩
    intro π hπ l sd hx
    rw [hp] at hπ
    obtain ⟨k, _, _, rfl⟩ := mem_chains _ _ _ _ _ hπ
    exact mem_chain hx
  | .app f u, env, seen, next, hlen => by
    rw [shareAux_app]
    simp only [Ranged]
    exact ⟨_, ranged_shareAux f env seen next hlen, ranged_shareAux u env _ _
      (by rw [(shareAux_paths f env seen next hlen).1]; exact hlen)⟩

theorem share_apart (t : Term) : Apart (share t) :=
  apart_of_ranged (ranged_shareAux t [] [] 0 rfl)

/-- On `share t` the token machine follows every run of the pointer machine. -/
theorem run_share_of_prun (t : Term) (S : Stacks) {n : Nat} {s : PState} {T : List Item}
    {H : List Addr} (h : prun n (share t) s = some (T, H)) :
    run n (share t) (s.abs (share t) S) = some (.root, stacksOf (share t) S H, T.map Item.side) :=
  run_of_prun (share_distinct t) (share_apart t) S n s T H h

/-! ## Returns in last-in-first-out order -/

/-- The state in which the first run starts: `n` lambdas of the result are asked for. -/
def PState.first (n : Nat) : PState := ⟨.down [], List.replicate n .q, [], []⟩

/-- On a locally safe term the pointer machine never has to stop: every return is to the
newest exit to its binder. Stated for the first run only; the later runs of readback start
from the tape and the history that the earlier ones leave. Proved as `firstRunLifo`. -/
def FirstRunLifo : Prop :=
  ∀ (t : Term) (A : Ty), LocallySafe t A → ∀ (n : Nat) (s : PState),
    PReach t (.first n) s → pstep t s ≠ .parted

/-! ## The history and the live exits

The exits that have not been returned through all lie in the state: under the tape or under
the log. Listed from the bottom of the tape to its top and then from the inside of the log
outwards, each exit before the exits saved under it, they stay in the same order under every
step; a new exit is put between the tape and the log, and a return takes out the last exit
of the tape. So the history agrees with this list, binder by binder, as long as no exit to a
lambda lies under the tape when the token leaves for that lambda or comes back to it. -/

mutual
/-- An exit and the exits saved under it, the exit first. -/
def Exit.tree : Exit → List Exit
  | .mk o σ => .mk o σ :: Exit.trees σ
/-- The exits under the entries of a list. -/
def Exit.trees : List Exit → List Exit
  | [] => []
  | e :: es => e.tree ++ Exit.trees es
end

theorem Exit.trees_nil : Exit.trees [] = [] := by simp [Exit.trees]

theorem Exit.trees_cons (e : Exit) (es : List Exit) :
    Exit.trees (e :: es) = e :: (Exit.trees e.saved ++ Exit.trees es) := by
  cases e with
  | mk o σ => simp [Exit.trees, Exit.tree, Exit.saved]

theorem Exit.trees_append : ∀ (xs ys : List Exit),
    Exit.trees (xs ++ ys) = Exit.trees xs ++ Exit.trees ys
  | [], _ => by simp [Exit.trees_nil]
  | x :: xs, ys => by simp [Exit.trees_cons, Exit.trees_append xs ys]

/-- The exits on the tape itself, the bottom one first. -/
def tapeExits : List Item → List Exit
  | [] => []
  | .q :: T => tapeExits T
  | .p e :: T => tapeExits T ++ [e]

/-- The exits not yet returned through, in the order in which they lie in the state. -/
def PState.live (s : PState) : List Exit :=
  Exit.trees (tapeExits s.tape) ++ Exit.trees s.log

/-- The occurrences in a list that the lambda at `b` binds. -/
def boundBy (t : Term) (b : Addr) (os : List Addr) : List Addr :=
  os.filter fun o => binderOf t o = some b

/-- For each lambda, the history has the exits to it in the order in which they lie. -/
def Agree (t : Term) (s : PState) : Prop :=
  ∀ b, boundBy t b s.hist = boundBy t b (s.live.map Exit.occ)

/-- No exit to the lambda at `b` lies under the tape. -/
def Free (t : Term) (b : Addr) (T : List Item) : Prop :=
  ∀ e ∈ Exit.trees (tapeExits T), binderOf t e.occ ≠ some b

/-- Where the token leaves a variable for its lambda, or comes back to a lambda, no other
exit to that lambda lies under the tape. -/
def PState.Clear (t : Term) (s : PState) : Prop :=
  match s.pos with
  | .down a =>
    match t.sub a, s.tape with
    | some (.var _ _), T => ∀ b, binderOf t a = some b → Free t b T
    | some (.lam _ _), .p _ :: T => Free t a T
    | _, _ => True
  | .up _ => True

theorem boundBy_append (t : Term) (b : Addr) (xs ys : List Addr) :
    boundBy t b (xs ++ ys) = boundBy t b xs ++ boundBy t b ys := by
  simp [boundBy]

theorem boundBy_cons_of {t : Term} {b o : Addr} (h : binderOf t o = some b) (xs : List Addr) :
    boundBy t b (o :: xs) = o :: boundBy t b xs := by
  simp [boundBy, h]

theorem boundBy_cons_ne {t : Term} {b o : Addr} (h : binderOf t o ≠ some b) (xs : List Addr) :
    boundBy t b (o :: xs) = boundBy t b xs := by
  simp [boundBy, h]

theorem boundBy_free {t : Term} {b : Addr} {T : List Item} (h : Free t b T) :
    boundBy t b ((Exit.trees (tapeExits T)).map Exit.occ) = [] := by
  simp only [boundBy, List.filter_eq_nil_iff, List.mem_map]
  rintro o ⟨e, he, rfl⟩
  simpa using h e he

theorem popNewest_of_boundBy (t : Term) (a : Addr) : ∀ (H : List Addr) (o : Addr)
    (X : List Addr), boundBy t a H = o :: X →
      ∃ H', popNewest t a H = some (o, H') ∧ boundBy t a H' = X ∧
        ∀ b, b ≠ a → boundBy t b H' = boundBy t b H
  | [], _, _, h => by simp [boundBy] at h
  | x :: hs, o, X, h => by
    by_cases hx : binderOf t x = some a
    · rw [boundBy_cons_of hx] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      refine ⟨hs, by simp [popNewest, hx], rfl, fun b hb => ?_⟩
      exact (boundBy_cons_ne (by rw [hx]; exact fun e => hb (Option.some.inj e).symm) hs).symm
    · rw [boundBy_cons_ne hx] at h
      obtain ⟨H', hp, hX, hb⟩ := popNewest_of_boundBy t a hs o X h
      refine ⟨x :: H', by simp [popNewest, hx, hp], ?_, fun b hba => ?_⟩
      · rw [boundBy_cons_ne hx, hX]
      · by_cases hxb : binderOf t x = some b
        · rw [boundBy_cons_of hxb, boundBy_cons_of hxb, hb b hba]
        · rw [boundBy_cons_ne hxb, boundBy_cons_ne hxb, hb b hba]

theorem live_tape (pos : Pos) (e : Exit) (T : List Item) (L : List Exit) (H : List Addr) :
    (PState.mk pos (.p e :: T) L H).live =
      Exit.trees (tapeExits T) ++ e :: (Exit.trees e.saved ++ Exit.trees L) := by
  simp [PState.live, tapeExits, Exit.trees_append, Exit.trees_cons, Exit.trees_nil]

theorem live_log (pos : Pos) (e : Exit) (T : List Item) (L : List Exit) (H : List Addr) :
    (PState.mk pos T (e :: L) H).live =
      Exit.trees (tapeExits T) ++ e :: (Exit.trees e.saved ++ Exit.trees L) := by
  simp [PState.live, Exit.trees_cons]

theorem agree_of_live {t : Term} {s s' : PState} (ha : Agree t s) (hh : s'.hist = s.hist)
    (hl : s'.live = s.live) : Agree t s' := by
  intro b
  rw [hh, hl]
  exact ha b

/-- A step from a clear state keeps the history in agreement, and is not out of order. -/
theorem agree_step {t : Term} {s : PState} (ha : Agree t s) (hc : s.Clear t) :
    pstep t s ≠ .parted ∧ ∀ s', pstep t s = .next s' → Agree t s' := by
  obtain ⟨pos, tape, log, hist⟩ := s
  cases pos with
  | down a =>
    cases hsub : t.sub a with
    | none => simp [pstep, hsub]
    | some u =>
      cases u with
      | var i π =>
        cases hb : binder a i with
        | inl k => simp [pstep, hsub, hb]
        | inr b =>
          have hbo : binderOf t a = some b := by simp [binderOf, hsub, hb]
          have hfree : Free t b tape := by
            simp only [PState.Clear, hsub] at hc
            exact hc b hbo
          have hE := boundBy_free hfree
          refine ⟨by simp [pstep, hsub, hb], fun s' hs' => ?_⟩
          simp only [pstep, hsub, hb, PResult.next.injEq] at hs'
          subst hs'
          intro b'
          have key := ha b'
          simp only [PState.live, List.map_append, boundBy_append] at key
          have h2 : Exit.trees (Exit.mk a (List.take (argDepth a - argDepth b) log)).saved ++
              Exit.trees (List.drop (argDepth a - argDepth b) log) = Exit.trees log := by
            simp only [Exit.saved]
            rw [← Exit.trees_append, List.take_append_drop]
          rw [live_tape, h2, List.map_append, List.map_cons, boundBy_append]
          simp only [Exit.occ]
          by_cases hbb : b' = b
          · subst hbb
            rw [boundBy_cons_of hbo, boundBy_cons_of hbo, key, hE]
            rfl
          · have hne : binderOf t a ≠ some b' := by
              rw [hbo]
              exact fun e => hbb (Option.some.inj e).symm
            rw [boundBy_cons_ne hne, boundBy_cons_ne hne, key]
      | lam A body =>
        cases tape with
        | nil => simp [pstep, hsub]
        | cons x T =>
          cases x with
          | q =>
            refine ⟨by simp [pstep, hsub], fun s' hs' => ?_⟩
            simp only [pstep, hsub, PResult.next.injEq] at hs'
            subst hs'
            exact agree_of_live ha rfl (by simp [PState.live, tapeExits])
          | p e =>
            by_cases hbe : binderOf t e.occ = some a
            · have hfree : Free t a T := by simpa [PState.Clear, hsub] using hc
              have hE := boundBy_free hfree
              have hlive := ha a
              rw [live_tape, List.map_append, List.map_cons, boundBy_append, hE,
                boundBy_cons_of hbe, List.nil_append] at hlive
              obtain ⟨H', hp, hX, hother⟩ := popNewest_of_boundBy t a hist _ _ hlive
              refine ⟨by simp [pstep, hsub, hbe, hp], fun s' hs' => ?_⟩
              simp only [pstep, hsub, hbe, hp, ite_true, PResult.next.injEq] at hs'
              subst hs'
              intro b'
              have hl : (PState.mk (.up e.occ) T (e.saved ++ log) H').live =
                  Exit.trees (tapeExits T) ++ (Exit.trees e.saved ++ Exit.trees log) := by
                simp [PState.live, Exit.trees_append]
              rw [hl, List.map_append, boundBy_append]
              by_cases hbb : b' = a
              · subst hbb
                rw [hE, hX]
                rfl
              · have hne : binderOf t e.occ ≠ some b' := by
                  rw [hbe]
                  exact fun e => hbb (Option.some.inj e).symm
                have key := ha b'
                rw [live_tape, List.map_append, List.map_cons, boundBy_append,
                  boundBy_cons_ne hne] at key
                rw [hother b' hbb, key]
            · simp [pstep, hsub, hbe]
      | app f u =>
        refine ⟨by simp [pstep, hsub], fun s' hs' => ?_⟩
        simp only [pstep, hsub, PResult.next.injEq] at hs'
        subst hs'
        exact agree_of_live ha rfl (by simp [PState.live, tapeExits])
  | up a =>
    cases a with
    | nil => simp [pstep]
    | cons d a =>
      cases d with
      | body =>
        refine ⟨by simp [pstep], fun s' hs' => ?_⟩
        simp only [pstep, PResult.next.injEq] at hs'
        subst hs'
        exact agree_of_live ha rfl (by simp [PState.live, tapeExits])
      | fn =>
        cases tape with
        | nil => simp [pstep]
        | cons x T =>
          cases x with
          | q =>
            refine ⟨by simp [pstep], fun s' hs' => ?_⟩
            simp only [pstep, PResult.next.injEq] at hs'
            subst hs'
            exact agree_of_live ha rfl (by simp [PState.live, tapeExits])
          | p e =>
            refine ⟨by simp [pstep], fun s' hs' => ?_⟩
            simp only [pstep, PResult.next.injEq] at hs'
            subst hs'
            exact agree_of_live ha rfl (by rw [live_tape, live_log])
      | arg =>
        cases log with
        | nil => simp [pstep]
        | cons e L =>
          refine ⟨by simp [pstep], fun s' hs' => ?_⟩
          simp only [pstep, PResult.next.injEq] at hs'
          subst hs'
          exact agree_of_live ha rfl (by rw [live_tape, live_log])

theorem agree_reach {t : Term} {s s' : PState} (hr : PReach t s s') :
    Agree t s → (∀ u, PReach t s u → u.Clear t) → Agree t s' := by
  induction hr with
  | refl => exact fun ha _ => ha
  | head hs _ ih =>
    intro ha hc
    exact ih ((agree_step ha (hc _ .refl)).2 _ hs) fun u hu => hc u (.head hs hu)

theorem agree_first (t : Term) (n : Nat) : Agree t (.first n) := by
  intro b
  have h : tapeExits (List.replicate n Item.q) = [] := by
    induction n with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ, tapeExits] using ih
  simp [PState.first, PState.live, h, Exit.trees_nil, boundBy]

/-- `FirstRunLifo` without the history: in the first run on a locally safe term, no exit to
a lambda lies under the tape when the token leaves for that lambda or comes back to it. -/
def FirstRunClear : Prop :=
  ∀ (t : Term) (A : Ty), LocallySafe t A → ∀ (n : Nat) (s : PState),
    PReach t (.first n) s → s.Clear t

theorem firstRunLifo_of_clear (h : FirstRunClear) : FirstRunLifo := by
  intro t A hs n s hr
  have hc : ∀ u, PReach t (.first n) u → u.Clear t := h t A hs n
  exact (agree_step (agree_reach hr (agree_first t n) hc) (hc s hr)).1

end LSL
