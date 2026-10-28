import RH_HilbertLimit.CanonicalPowerSums
import RH_HilbertLimit.SpectralExtraction

/-!
# Actual analytic constructions and the existing RH criteria

Uncompiled candidate for the user's native compiler. The calibration and
dominant extraction are constructed from the existing actual theta function.
The endpoints below have no extra analytic input hypotheses.

These are ordinary-limit and all-order criteria. The natural parameters in
the last criteria still satisfy universally quantified conditions. No finite
raw witness format, terminating actual-RH checker, or finite-checker
equivalence is asserted. The user's formal-closure goal therefore stays open.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RH_HilbertLimit

/-- The literal canonical actual-xi calibration, with every field supplied. -/
def actualCanonicalCalibration : ActualSpectralCalibration AngularMaster.ActualPairIndex :=
  canonicalCalibration canonicalPowerSums

/-- The infinite-spectrum dominant decomposition for this actual calibration. -/
theorem actualCanonicalDominantExtraction : DominantExtraction actualCanonicalCalibration :=
  actualCanonicalCalibration.dominantExtraction

/-- The rooted variation has its ordinary limit for the actual canonical data. -/
theorem canonical_actual_root_tendsto_constructed :
    Tendsto (rootScale actualVariation) atTop (𝓝 (spectralRadius canonicalNode)) :=
  actual_root_tendsto_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

theorem canonical_actual_root_limit_exists :
    ∃ R : ℝ, 1 ≤ R ∧ Tendsto (rootScale actualVariation) atTop (𝓝 R) :=
  exists_actual_root_limit_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

/-- Exact value-one criterion for the actual Riemann hypothesis. -/
theorem canonical_actual_root_one_iff_nativeRH :
    Tendsto (rootScale actualVariation) atTop (𝓝 1) ↔ _root_.RiemannHypothesis :=
  actual_root_one_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

theorem canonical_actual_subexponential_iff_nativeRH :
    Subexponential actualVariation ↔ _root_.RiemannHypothesis :=
  actual_subexponential_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

theorem canonical_actual_all_variation_one_iff_nativeRH :
    (∀ N, actualVariation N = 1) ↔ _root_.RiemannHypothesis :=
  actual_all_variation_one_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

theorem canonical_actual_weights_nonnegative_iff_nativeRH :
    (∀ N j, j ≤ N → 0 ≤ actualWeight N j) ↔ _root_.RiemannHypothesis :=
  actual_weights_nonnegative_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

/-- The natural parameter is finite; its admissibility is still all-order. -/
theorem canonical_actual_natural_growth_step_iff_nativeRH_constructed :
    (∃ K : ℕ, NaturalGrowthStep actualVariation K) ↔ _root_.RiemannHypothesis :=
  actual_exists_natural_growth_step_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

/-- This existential natural bound is not a terminating finite checker. -/
theorem canonical_actual_natural_bound_iff_nativeRH_constructed :
    (∃ B : ℕ, ∀ n : ℕ, actualVariation n ≤ (B : ℝ)) ↔ _root_.RiemannHypothesis :=
  actual_exists_natural_bound_iff_nativeRH_of_analytic_inputs
    actualCanonicalCalibration actualCanonicalDominantExtraction

end RH_HilbertLimit
