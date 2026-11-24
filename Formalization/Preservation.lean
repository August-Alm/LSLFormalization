import Formalization.Sharing
import Formalization.Token
import Formalization.Readback
import Formalization.Examples

/-!
# How beta reduction acts on the context semantics

The paper proves soundness from the fact that a reduction step of a proof net preserves the
context semantics: whatever the reduct outputs, the original outputs too. For locally safe
terms three versions of that statement are false:

* `StrictPreservation`, the paper's (`strictPreservation_fails`);
* `BetaSimulation`, a simulation up to a relation on stacks, over all queries
  (`betaSimulation_fails`);
* `ReadbackPreservation`, which only asks that readback is preserved, but along any step
  (`readbackPreservation_fails`): a step that erases a copy of a subterm can break it.

What remains are two conjectures, and nothing here proves either. `LOPreservation` is the
same statement for leftmost-outermost steps only. `KeepPreservation` (in `Keep.lean`) is the
same statement for any step of a reduction that keeps erased arguments.
-/

namespace LSL

/-- The paper's preservation property (first clause of its ordering on context semantics),
for reducts of locally safe terms: an output of the reduct is an output of the original. -/
def StrictPreservation : Prop :=
  ∀ (t₀ : Term) (A : Ty), LocallySafe t₀ A →
    ∀ t t' : Term, Steps (share t₀) t → Step t t' →
      ∀ (D : Stacks) (T : List Side) (out : Output),
        Sem t' .root D T out → Sem t .root D T out

/-- `t'` is simulated by `t`, up to a relation `ρ` between their exponential stacks: from
related inputs, an output of `t'` is matched by an output of `t` with the same multiplicative
stack and related exponential stacks. The last clause is the paper's: where `t'` is undefined
but `t` is defined, `t'` stays undefined however the multiplicative stack is extended. -/
def Simulated (t' t : Term) : Prop :=
  ∃ ρ : Stacks → Stacks → Prop,
    ρ Stacks.empty Stacks.empty ∧
    ∀ D D' : Stacks, ρ D D' → ∀ T : List Side,
      (∀ (E' : Stacks) (S : List Side), Sem t' .root D' T (.root, E', S) →
        ∃ E : Stacks, Sem t .root D T (.root, E, S) ∧ ρ E E') ∧
      (¬ Defined t' .root D' T → Defined t .root D T →
        ∀ T₂ : List Side, ¬ Defined t' .root D' (T ++ T₂))

/-- Along the reduction of a locally safe closed term, every step is a simulation in the
sense of `Simulated`. This is false: `betaSimulation_fails`. -/
def BetaSimulation : Prop :=
  ∀ (t₀ : Term) (A : Ty), LocallySafe t₀ A →
    ∀ t t' : Term, Steps (share t₀) t → Step t t' → Simulated t' t

/-! ## A simulation preserves readback -/

theorem replicate_split {α : Type} (a : α) {k n : Nat} (h : k ≤ n) :
    List.replicate k a ++ List.replicate (n - k) a = List.replicate n a := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have := ih (n := n) (by omega)
      simp only [List.replicate_succ, List.cons_append, Nat.add_sub_add_right, this]

/-- If every point of `t'` is simulated by `t`, what `t'` reads back as, `t` reads back as. -/
theorem Reads.of_simulation {t t' : Term} {ρ : Stacks → Stacks → Prop}
    (hρ : ∀ D D' : Stacks, ρ D D' → ∀ T : List Side,
      (∀ (E' : Stacks) (S : List Side), Sem t' .root D' T (.root, E', S) →
        ∃ E : Stacks, Sem t .root D T (.root, E, S) ∧ ρ E E') ∧
      (¬ Defined t' .root D' T → Defined t .root D T →
        ∀ T₂ : List Side, ¬ Defined t' .root D' (T ++ T₂)))
    {anc : List Frame} {D' : Stacks} {U : List Side} {u : Tm} (h : Reads t' anc D' U u) :
    ∀ D : Stacks, ρ D D' → Reads t anc D U u := by
  induction h with
  | @node anc D' E' U S V n l m x args hsem hmin hparse hres hlen _ ih =>
    intro D hD
    obtain ⟨E, hE, hEE'⟩ := (hρ D D' hD (U ++ List.replicate n .q)).1 E' S hsem
    refine Reads.node hE ?_ hparse hres hlen (fun i a hi => ih i a hi E hEE')
    intro k hk hdef
    have hstay := (hρ D D' hD (U ++ List.replicate k .q)).2 (hmin k hk) hdef
      (List.replicate (n - k) .q)
    rw [List.append_assoc, replicate_split Side.q (Nat.le_of_lt hk)] at hstay
    exact hstay ⟨_, hsem⟩

theorem Simulated.readsBack {t t' : Term} (h : Simulated t' t) {u : Tm}
    (hu : ReadsBack t' u) : ReadsBack t u := by
  obtain ⟨ρ, hempty, hρ⟩ := h
  exact Reads.of_simulation hρ hu Stacks.empty hempty

/-- Along the reduction of a locally safe closed term, what a reduct reads back as, the term
before the step reads back as. This is false: `readbackPreservation_fails`. -/
def ReadbackPreservation : Prop :=
  ∀ (t₀ : Term) (A : Ty), LocallySafe t₀ A →
    ∀ t t' : Term, Steps (share t₀) t → Step t t' → ∀ u : Tm, ReadsBack t' u → ReadsBack t u

/-! ## The strict property fails -/

theorem beta?_sound : ∀ (t t' : Term), beta? t = some t' → Step t t'
  | .var _ _, _, h => by simp [beta?] at h
  | .lam A t, t', h => by
    simp only [beta?] at h
    cases hb : beta? t with
    | none => simp [hb] at h
    | some u =>
      simp [hb] at h
      subst h
      exact Step.lam (beta?_sound t u hb)
  | .app (.lam A t) u, t', h => by
    simp only [beta?] at h
    cases h
    exact Step.beta
  | .app (.var i π) u, t', h => by
    simp only [beta?] at h
    cases hb : beta? u with
    | none => simp [hb] at h
    | some u' =>
      simp [hb] at h
      subst h
      exact Step.appR (beta?_sound u u' hb)
  | .app (.app t₁ t₂) u, t', h => by
    simp only [beta?] at h
    cases hf : beta? (.app t₁ t₂) with
    | some f' =>
      simp [hf] at h
      subst h
      exact Step.appL (beta?_sound _ f' hf)
    | none =>
      cases hb : beta? u with
      | none => simp [hf, hb] at h
      | some u' =>
        simp [hf, hb] at h
        subst h
        exact Step.appR (beta?_sound u u' hb)

theorem run_mono (t : Term) : ∀ (n m : Nat) (s : State) (out : Output),
    n ≤ m → run n t s = some out → run m t s = some out
  | 0, _, _, _, _, h => by simp [run] at h
  | n + 1, 0, _, _, hle, _ => absurd hle (by omega)
  | n + 1, m + 1, s, out, hle, h => by
    simp only [run] at h ⊢
    cases hs : step t s with
    | next s' =>
      simp only [hs] at h ⊢
      exact run_mono t n m s' out (by omega) h
    | done o => simpa [hs] using h
    | stuck => simp [hs] at h

theorem run_det (t : Term) (n m : Nat) (s : State) (a b : Output)
    (ha : run n t s = some a) (hb : run m t s = some b) : a = b := by
  have h₁ := run_mono t n (max n m) s a (Nat.le_max_left n m) ha
  have h₂ := run_mono t m (max n m) s b (Nat.le_max_right n m) hb
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- All one-step reducts of a term. -/
def reducts : Term → List Term
  | .var _ _ => []
  | .lam A b => (reducts b).map (.lam A)
  | .app f u =>
    (match f with
      | .lam _ b => [subst 0 u b]
      | _ => [])
      ++ (reducts f).map (.app · u) ++ (reducts u).map (.app f ·)

theorem reducts_sound : ∀ (t t' : Term), t' ∈ reducts t → Step t t'
  | .var _ _, _, h => by simp [reducts] at h
  | .lam A b, t', h => by
    simp only [reducts, List.mem_map] at h
    obtain ⟨b', hb', rfl⟩ := h
    exact Step.lam (reducts_sound b b' hb')
  | .app f u, t', h => by
    simp only [reducts, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨f', hf', rfl⟩) | ⟨u', hu', rfl⟩
    · cases f with
      | lam A b =>
        simp only [List.mem_singleton] at h
        subst h
        exact Step.beta
      | var i π => simp at h
      | app f₁ f₂ => simp at h
    · exact Step.appL (reducts_sound f f' hf')
    · exact Step.appR (reducts_sound u u' hu')

/-! ## Leftmost-outermost reduction -/

inductive LOSteps : Term → Term → Prop
  | refl {t : Term} : LOSteps t t
  | tail {t u v : Term} : LOSteps t u → beta? u = some v → LOSteps t v

theorem LOSteps.steps {t t' : Term} (h : LOSteps t t') : Steps t t' := by
  induction h with
  | refl => exact Steps.refl
  | tail _ hb ih => exact Steps.tail ih (beta?_sound _ _ hb)

/-- **Conjecture.** Along the leftmost-outermost reduction of a locally safe closed term,
what a reduct reads back as, the term before the step reads back as. -/
def LOPreservation : Prop :=
  ∀ (t₀ : Term) (A : Ty), LocallySafe t₀ A →
    ∀ t t' : Term, LOSteps (share t₀) t → beta? t = some t' →
      ∀ u : Tm, ReadsBack t' u → ReadsBack t u

theorem ReadsBack.of_loSteps (conj : LOPreservation) {t₀ : Term} {A : Ty}
    (safe : LocallySafe t₀ A) {t : Term} (hs : LOSteps (share t₀) t) {u : Tm}
    (hu : ReadsBack t u) : ReadsBack (share t₀) u := by
  induction hs with
  | refl => exact hu
  | tail hs' hb ih => exact ih (conj t₀ A safe _ _ hs' hb u hu)

namespace Counterexample

open Examples

def tT : Ty := nat .o
def tY : Ty := .arr tT (.arr .o .o)

/-- `(λt.λy. t (λz. y t z)) 2`: locally safe, yet after one step the copy of `2` in
function position duplicates an argument that contains the other copy. -/
def term : Term :=
  .app (.lam tT (.lam tY (.app (v 1) (.lam .o (.app (.app (v 1) (v 2)) (v 0))))))
    (numeral .o 2)

def t₁ : Term := share term
def t₂ : Term := (beta? t₁).getD t₁
def t₃ : Term := (beta? t₂).getD t₂

/-- The input on which `t₂` and `t₃` differ: it asks for the argument of the head of the
first argument of the head. -/
def input : State :=
  ⟨.down [], Stacks.push (Stacks.push Stacks.empty 1 .p) 1 .p, [.p, .p, .p, .p]⟩

/-- The stack of label 1 in the output. -/
def stack1 (r : Option Output) : Option (List Side) := r.map fun out => out.2.1 1

/-- The conclusion and the multiplicative stack of an output. -/
def shape (r : Option Output) : Option (Concl × List Side) := r.map fun out => (out.1, out.2.2)

def stacksOf (r : Option Output) : Stacks :=
  match r with
  | some out => out.2.1
  | none => Stacks.empty

theorem eq_of_shape {r : Option Output} {c : Concl} {S : List Side}
    (h : shape r = some (c, S)) : r = some (c, stacksOf r, S) := by
  cases r with
  | none => simp [shape] at h
  | some out =>
    obtain ⟨c', E, S'⟩ := out
    simp only [shape, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-! Three queries, each made with the exponential stacks that the one before it left. The
first asks about the second lambda's variable, which readback never does. -/

def after₁ (t : Term) : Option Output := run 100 t ⟨.down [], Stacks.empty, [.q, .p]⟩

def after₂ (t : Term) : Option Output :=
  run 100 t ⟨.down [], stacksOf (after₁ t), [.p, .p, .q, .q]⟩

def after₃ (t : Term) : Option Output :=
  run 100 t ⟨.down [], stacksOf (after₂ t), [.p, .q, .p]⟩

/-- `(λt. (λy.λx. t (λz. y t x) x) (λu. t (u (λw. w)))) 2`: locally safe, with normal form
`λx. x`. -/
def erasing : Term :=
  .app (.lam tT (.app
      (.lam tY (.lam .o (.app (.app (v 2) (.lam .o (.app (.app (v 2) (v 3)) (v 1)))) (v 0))))
      (.lam tT (.app (v 1) (.app (v 0) (.lam .o (v 0)))))))
    (numeral .o 2)

/-- Three steps, none of them leftmost-outermost after the first. The second copies
`λz. y 2 x`; the third applies the first copy, which erases the second. -/
def u₀ : Term := share erasing
def u₁ : Term := ((reducts u₀)[0]?).getD u₀
def u₂ : Term := ((reducts u₁)[1]?).getD u₁
def u₃ : Term := ((reducts u₂)[2]?).getD u₂
def u₄ : Term := (beta? u₃).getD u₃

end Counterexample

open Counterexample in
/-- On the same input, the term before the step leaves `[q, p]` on the stack of label 1 and
the term after it leaves `[p, q]`. -/
theorem strictPreservation_fails : ¬ StrictPreservation := by
  intro h
  have safe : LocallySafe term (.arr tY (.arr .o .o)) := infer_sound _ _ _ _ (by decide)
  have s₁₂ : Step t₁ t₂ := beta?_sound _ _ (by decide)
  have s₂₃ : Step t₂ t₃ := beta?_sound _ _ (by decide)
  have a₂ : stack1 (run 100 t₂ input) = some [.q, .p] := by decide
  have a₃ : stack1 (run 100 t₃ input) = some [.p, .q] := by decide
  cases h₃ : run 100 t₃ input with
  | none => simp [h₃, stack1] at a₃
  | some out₃ =>
    cases h₂ : run 100 t₂ input with
    | none => simp [h₂, stack1] at a₂
    | some out₂ =>
      obtain ⟨s, n, hs, hn⟩ :=
        h term _ safe t₂ t₃ (Steps.tail Steps.refl s₁₂) s₂₃ input.exp input.mul out₃
          ⟨input, 100, rfl, h₃⟩
      have hs' : s = input := by
        simp only [enter] at hs
        exact (Option.some.inj hs).symm
      subst hs'
      have e := run_det t₂ n 100 _ _ _ hn h₂
      subst e
      simp only [h₂, stack1, Option.map_some] at a₂
      simp only [h₃, stack1, Option.map_some] at a₃
      rw [Option.some.inj a₂] at a₃
      exact absurd a₃ (by decide)

open Counterexample in
/-- `t₂` and `t₃` answer the first two queries alike, so their stacks stay related, but they
answer the third with `[p, q, q]` and `[q, p]`. -/
theorem betaSimulation_fails : ¬ BetaSimulation := by
  intro h
  have safe : LocallySafe term (.arr tY (.arr .o .o)) := infer_sound _ _ _ _ (by decide)
  have s₁₂ : Step t₁ t₂ := beta?_sound _ _ (by decide)
  have s₂₃ : Step t₂ t₃ := beta?_sound _ _ (by decide)
  obtain ⟨ρ, hρ₀, hρ⟩ := h term _ safe t₂ t₃ (Steps.tail Steps.refl s₁₂) s₂₃
  have key : ∀ (D D' : Stacks) (T S S' : List Side), ρ D D' →
      shape (run 100 t₂ ⟨.down [], D, T⟩) = some (.root, S) →
      shape (run 100 t₃ ⟨.down [], D', T⟩) = some (.root, S') →
      S = S' ∧ ρ (stacksOf (run 100 t₂ ⟨.down [], D, T⟩))
        (stacksOf (run 100 t₃ ⟨.down [], D', T⟩)) := by
    intro D D' T S S' hD ha hb
    obtain ⟨E, hE, hEρ⟩ := (hρ D D' hD T).1 _ S' (sem_root.mpr ⟨100, eq_of_shape hb⟩)
    obtain ⟨n, hn⟩ := sem_root.mp hE
    have e := run_det t₂ n 100 _ _ _ hn (eq_of_shape ha)
    obtain ⟨_, e'⟩ := Prod.mk.inj e
    obtain ⟨eE, eS⟩ := Prod.mk.inj e'
    exact ⟨eS.symm, eE ▸ hEρ⟩
  have a₁ : shape (after₁ t₂) = some (.root, [.p, .q, .p]) := by decide
  have b₁ : shape (after₁ t₃) = some (.root, [.p, .q, .p]) := by decide
  have a₂ : shape (after₂ t₂) = some (.root, [.p, .p, .p, .q]) := by decide
  have b₂ : shape (after₂ t₃) = some (.root, [.p, .p, .p, .q]) := by decide
  have a₃ : shape (after₃ t₂) = some (.root, [.p, .q, .q]) := by decide
  have b₃ : shape (after₃ t₃) = some (.root, [.q, .p]) := by decide
  have h₁ := (key _ _ _ _ _ hρ₀ a₁ b₁).2
  have h₂ := (key _ _ _ _ _ h₁ a₂ b₂).2
  exact absurd (key _ _ _ _ _ h₂ a₃ b₃).1 (by decide)

theorem Tm.apps_ne_lam : ∀ (args : List Tm) (h : Tm), (∀ b, h ≠ .lam b) →
    ∀ b, Tm.apps h args ≠ .lam b
  | [], _, hh, b => hh b
  | a :: rest, h, _, b => Tm.apps_ne_lam rest (.app h a) (fun _ e => by cases e) b

open Counterexample in
/-- `u₄` reads back as `λx. x`, but `u₃`, one step before it, does not: its first query gets
stuck, because the occurrence that the stacks select was in the erased copy. -/
theorem readbackPreservation_fails : ¬ ReadbackPreservation := by
  intro h
  have safe : LocallySafe erasing (.arr .o .o) := infer_sound _ _ _ _ (by decide)
  have s₀₁ : Step u₀ u₁ := reducts_sound _ _ (by decide)
  have s₁₂ : Step u₁ u₂ := reducts_sound _ _ (by decide)
  have s₂₃ : Step u₂ u₃ := reducts_sound _ _ (by decide)
  have s₃₄ : Step u₃ u₄ := beta?_sound _ _ (by decide)
  have good : ReadsBack u₄ (.lam (.var 0)) := readback_sound 300 _ 2 _ _ _ _ (by decide)
  have stuck : (eval 100 u₃ ⟨.down [], Stacks.empty, [.q]⟩).map Option.isSome = some false := by
    decide
  have hst : eval 100 u₃ ⟨.down [], Stacks.empty, [.q]⟩ = some none := by
    cases he : eval 100 u₃ ⟨.down [], Stacks.empty, [.q]⟩ with
    | none => simp [he] at stuck
    | some r =>
      cases r with
      | none => rfl
      | some out => simp [he] at stuck
  have bad := h erasing _ safe u₃ u₄
    (Steps.tail (Steps.tail (Steps.tail Steps.refl s₀₁) s₁₂) s₂₃) s₃₄ _ good
  generalize hw : Tm.lam (Tm.var 0) = w at bad
  cases bad with
  | @node _ _ E _ S V n l m x args hsem =>
    cases n with
    | zero => exact absurd hw.symm (Tm.apps_ne_lam args _ (fun _ e => by cases e) _)
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨k, hk⟩ := sem_root.mp hsem
        have hk' : run k u₃ ⟨.down [], Stacks.empty, [.q]⟩ = some (.root, E, S) := hk
        rw [eval_stuck u₃ 100 _ hst k] at hk'
        cases hk'
      | succ n => simp [Tm.lams] at hw

end LSL
