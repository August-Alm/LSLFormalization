import Formalization.Coherence

/-!
# Reduction that keeps erased arguments

Plain beta reduction drops the argument of a redex whose variable is not used. For the token
machine that is a real change: the stacks can select an occurrence that lay in the dropped
argument (`readbackPreservation_fails`). In the interaction net the argument stays, attached
to an eraser. `KStep` does the same: a redex `(λx. b) g` with `x` unused is never contracted.
It is transparent for the token, and an application of it moves inside:
`((λx. b) g) u ⟶ (λx. b u) g`.

Local safety and distinctness are preserved, and a normal form reads back as itself without
its kept arguments (`eraseK`). `KeepPreservation`, that every such step preserves readback, is
a conjecture.
-/

namespace LSL

inductive KStep : Term → Term → Prop
  | beta {A : Ty} {t u : Term} : occurrences 0 t ≠ 0 → KStep (.app (.lam A t) u) (subst 0 u t)
  | sigma {A : Ty} {t g u : Term} : occurrences 0 t = 0 →
      KStep (.app (.app (.lam A t) g) u) (.app (.lam A (.app t (shift 1 0 u))) g)
  | lam {A : Ty} {t t' : Term} : KStep t t' → KStep (.lam A t) (.lam A t')
  | appL {t t' u : Term} : KStep t t' → KStep (.app t u) (.app t' u)
  | appR {t u u' : Term} : KStep u u' → KStep (.app t u) (.app t u')

inductive KSteps : Term → Term → Prop
  | refl {t : Term} : KSteps t t
  | tail {t u v : Term} : KSteps t u → KStep u v → KSteps t v

/-- All one-step reducts of a term. -/
def kreducts : Term → List Term
  | .var _ _ => []
  | .lam A b => (kreducts b).map (.lam A)
  | .app f u =>
    (match f with
      | .lam _ b => if occurrences 0 b = 0 then [] else [subst 0 u b]
      | .app (.lam A b) g =>
        if occurrences 0 b = 0 then [.app (.lam A (.app b (shift 1 0 u))) g] else []
      | _ => [])
      ++ (kreducts f).map (.app · u) ++ (kreducts u).map (.app f ·)

theorem kreducts_sound : ∀ (t t' : Term), t' ∈ kreducts t → KStep t t'
  | .var _ _, _, h => by simp [kreducts] at h
  | .lam A b, t', h => by
    simp only [kreducts, List.mem_map] at h
    obtain ⟨b', hb', rfl⟩ := h
    exact KStep.lam (kreducts_sound b b' hb')
  | .app f u, t', h => by
    simp only [kreducts, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨f', hf', rfl⟩) | ⟨u', hu', rfl⟩
    · cases f with
      | var i π => simp at h
      | lam A b =>
        by_cases hocc : occurrences 0 b = 0
        · simp [hocc] at h
        · simp only [hocc, ite_false, List.mem_singleton] at h
          subst h
          exact KStep.beta hocc
      | app f₁ g =>
        cases f₁ with
        | var i π => simp at h
        | app a b => simp at h
        | lam A b =>
          by_cases hocc : occurrences 0 b = 0
          · simp only [hocc, ite_true, List.mem_singleton] at h
            subst h
            exact KStep.sigma hocc
          · simp [hocc] at h
    · exact KStep.appL (kreducts_sound f f' hf')
    · exact KStep.appR (kreducts_sound u u' hu')

/-! ## Local safety -/

theorem KStep.safe {t t' : Term} (st : KStep t t') :
    ∀ (m : Bool) (Γ : List Bind) (A : Ty),
      (m = false → ∀ (i : Nat) (b : Bind), Γ[i]? = some b → b.zone ≠ .loc) →
      LS m Γ t A → LS m Γ t' A := by
  induction st with
  | beta _ => exact fun m Γ A hΓ h => Step.beta.safe m Γ A hΓ h
  | sigma _ =>
    intro m Γ C _ h
    cases h with
    | app hf hu =>
      cases hf with
      | app hlam hg =>
        cases hlam with
        | lam hb =>
          refine LS.app (LS.lam (LS.app hb ?_)) hg
          refine shift_safe hu true _ 1 0 (fun e => e) ?_
          intro i b hi
          exact ⟨b, hi, Bind.le_refl b⟩
  | lam _ ih =>
    intro m Γ B hΓ h
    cases h with
    | lam ht =>
      refine LS.lam (ih m _ _ ?_ ht)
      intro hm i b hb
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        subst hm
        show Zone.glob ≠ Zone.loc
        decide
      | succ k =>
        simp only [List.getElem?_cons_succ] at hb
        exact hΓ hm k b hb
  | appL _ ih =>
    intro m Γ B hΓ h
    cases h with
    | app hf hu => exact LS.app (ih m Γ _ hΓ hf) hu
  | appR _ ih =>
    intro m Γ B hΓ h
    cases h with
    | app hf hu => exact LS.app hf (ih true _ _ (fun h => by cases h) hu)

theorem KSteps.safe {t t' : Term} (st : KSteps t t') :
    ∀ A : Ty, LocallySafe t A → LocallySafe t' A := by
  induction st with
  | refl => exact fun _ h => h
  | tail _ s ih =>
    exact fun A h => s.safe false [] A (fun _ i b hb => by simp at hb) (ih A h)

/-! ## Distinctness -/

theorem kstep_paths {t t' : Term} (st : KStep t t') :
    (Distinct t → Distinct t') ∧
    (Distinct t → ∀ i, (paths i t).Pairwise Clash → (paths i t').Pairwise Clash) ∧
    (∀ i ρ', ρ' ∈ paths i t' → ∃ π ρ, ρ ∈ paths i t ∧ ρ' = π ++ ρ) := by
  induction st with
  | beta _ => exact step_paths Step.beta
  | @sigma A t g u _ =>
    have hsh : ∀ i, paths (i + 1) (shift 1 0 u) = paths i u := fun i => by
      rw [paths_shift_ge 1 u (i + 1) 0 (by omega)]
      rfl
    have h0 : paths 0 (shift 1 0 u) = [] := paths_shift_mid 1 u 0 0 (Nat.le_refl 0) (by omega)
    refine ⟨fun h => ?_, fun _ i hp => ?_, fun i ρ' hm => ?_⟩
    · refine ⟨⟨?_, h.1.1.2, distinct_shift 1 u 0 h.2⟩, h.1.2⟩
      simp only [paths, h0, List.append_nil]
      exact h.1.1.1
    · simp only [paths, hsh, List.pairwise_append, List.mem_append] at hp ⊢
      obtain ⟨⟨ht, hg, htg⟩, hu, hcross⟩ := hp
      refine ⟨⟨ht, hu, fun a ha b hb => hcross a (.inl ha) b hb⟩, hg, fun a ha b hb => ?_⟩
      rcases ha with ha | ha
      · exact htg a ha b hb
      · exact (hcross b (.inr hb) a ha).symm
    · simp only [paths, hsh, List.mem_append] at hm ⊢
      refine ⟨[], ρ', ?_, rfl⟩
      rcases hm with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
  | lam _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    exact ⟨fun h => ⟨ih2 h.2 0 h.1, ih1 h.2⟩, fun h i hp => ih2 h.2 (i + 1) hp,
      fun i ρ' hm => ih3 (i + 1) ρ' hm⟩
  | appL _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨fun h => ⟨ih1 h.1, h.2⟩, fun h i hp => ?_, fun i ρ' hm => ?_⟩
    · simp only [paths, List.pairwise_append] at hp ⊢
      refine ⟨ih2 h.1 i hp.1, hp.2.1, fun a ha b hb => ?_⟩
      obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i a ha
      exact (hp.2.2 ρ hρ b hb).append_left π
    · simp only [paths, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i ρ' hm
        exact ⟨π, ρ, .inl hρ, rfl⟩
      · exact ⟨[], ρ', .inr hm, rfl⟩
  | appR _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨fun h => ⟨h.1, ih1 h.2⟩, fun h i hp => ?_, fun i ρ' hm => ?_⟩
    · simp only [paths, List.pairwise_append] at hp ⊢
      refine ⟨hp.1, ih2 h.2 i hp.2.1, fun a ha b hb => ?_⟩
      obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i b hb
      exact (hp.2.2 a ha ρ hρ).append_right π
    · simp only [paths, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact ⟨[], ρ', .inl hm, rfl⟩
      · obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i ρ' hm
        exact ⟨π, ρ, .inr hρ, rfl⟩

theorem KSteps.distinct {t t' : Term} (st : KSteps t t') : Distinct t → Distinct t' := by
  induction st with
  | refl => exact fun h => h
  | tail _ s ih => exact fun h => (kstep_paths s).1 (ih h)

/-! ## Normal forms -/

theorem nf_of_knormal : ∀ s : Term, (∀ s', ¬ KStep s s') → Nf s
  | .var x π, _ => Nf.neu (x := x) (π := π) (args := []) (fun u hu => by simp at hu)
  | .lam A s, h => Nf.lam (nf_of_knormal s fun s' hs => h _ (KStep.lam hs))
  | .app f u, h => by
    have hf := nf_of_knormal f fun f' hs => h _ (KStep.appL hs)
    have hu := nf_of_knormal u fun u' hs => h _ (KStep.appR hs)
    cases hf with
    | @lam A s hs =>
      by_cases hocc : occurrences 0 s = 0
      · exact Nf.gc hocc hs
      · exact absurd (KStep.beta hocc) (h _)
    | gc hocc _ => exact absurd (KStep.sigma hocc) (h _)
    | @neu x π args hargs =>
      have e : Term.app (Term.apps (.var x π) args) u = Term.apps (.var x π) (args ++ [u]) := by
        simp [Term.apps]
      rw [e]
      refine Nf.neu fun v hv => ?_
      rcases List.mem_append.mp hv with hv | hv
      · exact hargs v hv
      · simp only [List.mem_singleton] at hv
        subst hv
        exact hu

/-- A normal form reached from a locally safe term reads back as itself, without the
arguments it keeps. -/
theorem kreduct_readsBack {t₀ t : Term} {A : Ty} (hsafe : LocallySafe t₀ A)
    (hs : KSteps (share t₀) t) (hnormal : ∀ t', ¬ KStep t t') : ReadsBack t (eraseK id t) :=
  nf_readsBack (hs.safe A (share_safe hsafe)) (nf_of_knormal t hnormal)
    (hs.distinct (share_distinct t₀)).coherent

/-! ## The conjecture -/

/-- **Conjecture.** Along a reduction of a locally safe closed term that keeps erased
arguments, what a reduct reads back as, the term before the step reads back as.

A proof cannot pair each entry into an argument with a return to the same occurrence: even
for locally safe terms the token sometimes returns to another one (`experiments returns`). -/
def KeepPreservation : Prop :=
  ∀ (t₀ : Term) (A : Ty), LocallySafe t₀ A →
    ∀ t t' : Term, KSteps (share t₀) t → KStep t t' → ∀ u : Tm, ReadsBack t' u → ReadsBack t u

theorem ReadsBack.of_ksteps (conj : KeepPreservation) {t₀ : Term} {A : Ty}
    (safe : LocallySafe t₀ A) {t : Term} (hs : KSteps (share t₀) t) {u : Tm}
    (hu : ReadsBack t u) : ReadsBack (share t₀) u := by
  induction hs with
  | refl => exact hu
  | tail hs' st ih => exact ih (conj t₀ A safe _ _ hs' st u hu)

/-- If the conjecture holds, a locally safe term with its initial sharing reads back as any
normal form it reaches, without the arguments that normal form keeps. -/
theorem soundness_of_keepPreservation (conj : KeepPreservation) {t₀ t : Term} {A : Ty}
    (hsafe : LocallySafe t₀ A) (hs : KSteps (share t₀) t) (hnormal : ∀ t', ¬ KStep t t') :
    ReadsBack (share t₀) (eraseK id t) :=
  ReadsBack.of_ksteps conj hsafe hs (kreduct_readsBack hsafe hs hnormal)

end LSL
