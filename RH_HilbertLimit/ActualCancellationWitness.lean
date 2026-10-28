import RH_HilbertLimit.AnalyticClosure
import RH_HilbertLimit.Cancellation
import RH_HilbertLimit.EventualGrowth

/-!
# Actual RH from an assumed admissible cancellation budget

The data object has exactly two natural-number fields. Its mathematical
admissibility is displayed separately and quantifies over every order after
the cutoff. The forward theorem proves actual Mathlib RH from the existence
of data satisfying that predicate; no concrete admissible data are supplied.

This is NOT a finite-checker soundness theorem. There is no Bool checker here,
and the universal admissibility condition has not been discharged by finite
computation. The full finite raw witness equivalence remains open.

The imported AnalyticClosure constructs its spectral calibration and dominant
extraction. Neither is an extra assumption of the endpoints in this module.

Prepared without local Lean, Lake, native compiler, axiom-audit, or CI
execution. Native Windows Lean 4.33.0 compilation and audit remain required.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- Finite natural data only. Validity is deliberately not a structure field. -/
structure CancellationBudget where
  cutoff : ℕ
  coefficient : ℕ

/-- Semantic, all-order admissibility for the literal actual-xi moments.
This predicate is not a terminating finite computation. -/
def CancellationBudget.Admissible (W : CancellationBudget) : Prop :=
  ∀ n : ℕ, W.cutoff ≤ n →
    rowCancellation actualNormalizedMoment n ≤ (W.coefficient : ℝ) * actualVariation n

/-- The exact finite cancellation identity supplies the scalar growth step. -/
theorem cancellationBudget_admissible_iff_eventual_growth_step
    (W : CancellationBudget) :
    W.Admissible ↔
      EventualNaturalGrowthStep actualVariation W.cutoff W.coefficient := by
  constructor
  · intro h n hn
    have hc := h n hn
    rw [rowCancellation_eq] at hc
    exact hc
  · intro h n hn
    rw [rowCancellation_eq]
    exact h n hn

/-- An admissible actual cancellation budget gives subexponential variation. -/
theorem actual_subexponential_of_admissible_cancellationBudget
    (W : CancellationBudget) (hW : W.Admissible) :
    Subexponential actualVariation := by
  exact subexponential_of_eventual_natural_growth_step
    (V := actualVariation) (N := W.cutoff) (K := W.coefficient)
    (fun n => rowVariation_nonneg actualNormalizedMoment n)
    ((cancellationBudget_admissible_iff_eventual_growth_step W).mp hW)

/-- Forward transfer with the universal admissibility premise explicit. -/
theorem nativeRH_of_admissible_cancellationBudget
    (W : CancellationBudget) (hW : W.Admissible) :
    _root_.RiemannHypothesis := by
  exact canonical_actual_subexponential_iff_nativeRH.mp
    (actual_subexponential_of_admissible_cancellationBudget W hW)

/-- Requested hypothetical-existence implication for the semantic witness.
The hypothesis includes Admissible's universal tail condition. -/
theorem nativeRH_of_exists_admissible_cancellationBudget
    (hWitness : ∃ W : CancellationBudget, W.Admissible) :
    _root_.RiemannHypothesis := by
  obtain ⟨W, hW⟩ := hWitness
  exact nativeRH_of_admissible_cancellationBudget W hW

/-- Under RH, cutoff zero and coefficient zero satisfy semantic admissibility.
This does not provide an unconditional witness or a finite acceptance check. -/
theorem zero_cancellationBudget_admissible_of_nativeRH
    (hRH : _root_.RiemannHypothesis) :
    CancellationBudget.Admissible ⟨0, 0⟩ := by
  intro n _hn
  have hv : ∀ m : ℕ, actualVariation m = 1 :=
    canonical_actual_all_variation_one_iff_nativeRH.mpr hRH
  rw [rowCancellation_eq]
  change ((n : ℝ) + 1) * (actualVariation (n + 1) - actualVariation n) ≤
    ((0 : ℕ) : ℝ) * actualVariation n
  rw [hv (n + 1), hv n]
  simp

/-- Analytic equivalence with universally admissible finite natural data.
This is not the requested equivalence with a terminating Bool checker. -/
theorem exists_admissible_cancellationBudget_iff_nativeRH :
    (∃ W : CancellationBudget, W.Admissible) ↔ _root_.RiemannHypothesis := by
  constructor
  · exact nativeRH_of_exists_admissible_cancellationBudget
  · intro hRH
    exact ⟨⟨0, 0⟩, zero_cancellationBudget_admissible_of_nativeRH hRH⟩

/-- Expanded forward signature, displaying every quantified obligation. -/
theorem nativeRH_of_exists_eventual_cancellation_bound
    (hWitness : ∃ N K : ℕ, ∀ n : ℕ, N ≤ n →
      rowCancellation actualNormalizedMoment n ≤ (K : ℝ) * actualVariation n) :
    _root_.RiemannHypothesis := by
  obtain ⟨N, K, hNK⟩ := hWitness
  exact nativeRH_of_admissible_cancellationBudget ⟨N, K⟩ hNK

/-- Semantic local-flux obligations for a proposed auxiliary function.
`H` is an unrestricted mathematical function here, not finite certificate data. -/
def CancellationBudget.LocalFlux (W : CancellationBudget) (H : ℕ → ℕ → ℝ) : Prop :=
  (∀ n : ℕ, W.cutoff ≤ n → ∀ j : ℕ, j ≤ n →
    cancellationDefect actualNormalizedMoment n j ≤
      (W.coefficient : ℝ) * |actualWeight n j| + (H n (j + 1) - H n j)) ∧
  (∀ n : ℕ, W.cutoff ≤ n → H n (n + 1) ≤ H n 0)

/-- The generic finite-row telescoping theorem transfers to actual moments. -/
theorem cancellationBudget_admissible_of_local_flux
    (W : CancellationBudget) (H : ℕ → ℕ → ℝ) (hH : W.LocalFlux H) :
    W.Admissible := by
  intro n hn
  exact rowCancellation_le_of_local_flux actualNormalizedMoment n
    (W.coefficient : ℝ) (H n) (hH.1 n hn) (hH.2 n hn)

/-- A hypothetical universally valid local-flux witness implies actual RH.
The universal function and inequalities are explicit semantic premises. -/
theorem nativeRH_of_exists_local_cancellation_flux
    (hWitness : ∃ W : CancellationBudget, ∃ H : ℕ → ℕ → ℝ, W.LocalFlux H) :
    _root_.RiemannHypothesis := by
  obtain ⟨W, H, hH⟩ := hWitness
  exact nativeRH_of_admissible_cancellationBudget W
    (cancellationBudget_admissible_of_local_flux W H hH)

end RH_HilbertLimit
