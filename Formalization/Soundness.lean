import Formalization.Preservation
import Formalization.Coherence
import Formalization.PointerSound

/-!
# Soundness for the leftmost-outermost reduction

The term with its initial sharing reads back as the normal form that the leftmost-outermost
reduction of a locally safe term reaches (`soundness_lo`, from `soundness` in
`PointerSound.lean`).

An earlier route went through the conjecture `LOPreservation`: readback is preserved
backwards along that reduction (`soundness_of_loPreservation`). The conjecture is still open;
`soundness` does not use it.
-/

namespace LSL

theorem normal_of_beta?_none : ∀ t : Term, beta? t = none → ∀ t', ¬ Step t t'
  | .var _ _, _, _, h => by cases h
  | .lam A b, hb, _, h => by
    cases h with
    | lam hs => exact normal_of_beta?_none b (by simpa [beta?] using hb) _ hs
  | .app (.lam A b) u, hb, _, _ => by simp [beta?] at hb
  | .app (.var i π) u, hb, _, h => by
    cases h with
    | appL hs => cases hs
    | appR hs => exact normal_of_beta?_none u (by simpa [beta?] using hb) _ hs
  | .app (.app f g) u, hb, _, h => by
    simp only [beta?] at hb
    cases hf : beta? (.app f g) with
    | some f' => simp [hf] at hb
    | none =>
      cases h with
      | appL hs => exact normal_of_beta?_none (.app f g) hf _ hs
      | appR hs => exact normal_of_beta?_none u (by simpa [hf] using hb) _ hs

theorem soundness_of_loPreservation (conj : LOPreservation) {t₀ t : Term} {A : Ty}
    (hsafe : LocallySafe t₀ A) (hs : LOSteps (share t₀) t) (hnormal : beta? t = none) :
    ReadsBack (share t₀) (erase t) :=
  ReadsBack.of_loSteps conj hsafe hs
    (reduct_readsBack hsafe hs.steps (normal_of_beta?_none t hnormal))

theorem soundness_lo {t₀ t : Term} {A : Ty} (hsafe : LocallySafe t₀ A)
    (hs : LOSteps (share t₀) t) (hnormal : beta? t = none) : ReadsBack (share t₀) (erase t) :=
  soundness hsafe hs.steps (normal_of_beta?_none t hnormal)

end LSL
