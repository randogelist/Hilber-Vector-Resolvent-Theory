import RH_HilbertLimit.ActualCalibrationProgress
import RH_HilbertLimit.ActualMomentReality
import RH_HilbertLimit.GrowthStep
import RH_HilbertLimit.SpectralTail

/-!
# Canonical actual-data interface after the new calibration proofs

The current source supplies the actual nodes, normalization positivity,
summability, exact zero correspondence, all-order moment reality, and the
zeroth normalized power sum.  The remaining calibration input is the
all-order normalized power-sum identity, stated explicitly below.

The endpoint is still conditional on that analytic identity and dominant
extraction.  Its existential natural parameter satisfies a universal
inequality; this file does not manufacture a terminating checker or assert
finite-checker completeness.  No Lean process was run in preparation.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter

namespace RH_HilbertLimit

/-- Exact unit mass for the canonical normalized actual nodes. -/
theorem canonicalNode_mass_one :
    HasSum canonicalNode (1 : ℂ) := by
  have hκ : (actualKappa : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt actualKappa_pos
  have hreal : actualComplexMoment 0 = (actualKappa : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using actualComplexMoment_im_eq_zero 0
  have htrace : HasSum
      (fun i : AngularMaster.ActualPairIndex => (AngularMaster.actualComplexScale i)⁻¹)
      (actualComplexMoment 0) := by
    rw [actualComplexMoment_zero_eq_canonical_trace]
    exact AngularMaster.actualComplexScale_norm_inv_summable.of_norm.hasSum
  have h := htrace.mul_left (actualKappa : ℂ)⁻¹
  simpa only [hreal, ← canonicalNode_eq_inverseScale_mul,
    inv_mul_cancel₀ hκ] using h

/-- The `n = 0` case of the calibration is proved independently of the
remaining all-order power-sum assumption. -/
theorem canonicalNode_power_sum_zero :
    HasSum (fun i : AngularMaster.ActualPairIndex => canonicalNode i ^ (0 + 1))
      (actualNormalizedMoment 0 : ℂ) := by
  simpa only [Nat.zero_add, pow_one,
    actualNormalizedMoment_zero (ne_of_gt actualKappa_pos), Complex.ofReal_one]
    using canonicalNode_mass_one

/-- The remaining analytic calibration obligation.  This is an explicit
universal identity, not finite raw data and not a computable checker. -/
def CanonicalPowerSums : Prop :=
  ∀ n : ℕ, HasSum
    (fun i : AngularMaster.ActualPairIndex => canonicalNode i ^ (n + 1))
    (actualNormalizedMoment n : ℂ)

/-- All calibration fields except the displayed power-sum identities are
filled by source proofs about the actual xi function. -/
def canonicalCalibration (hpower : CanonicalPowerSums) :
    ActualSpectralCalibration AngularMaster.ActualPairIndex :=
  canonicalCalibration_of_moment_identities actualComplexMoment_im_eq_zero hpower

/-- The ordinary root limit now uses a canonical actual node family.
Both remaining analytic inputs are still visible in its signature. -/
theorem canonical_actual_root_tendsto
    (hpower : CanonicalPowerSums)
    (hExtract : DominantExtraction (canonicalCalibration hpower)) :
    Tendsto (rootScale actualVariation) atTop (𝓝 (spectralRadius canonicalNode)) := by
  exact actual_root_tendsto_of_analytic_inputs (canonicalCalibration hpower) hExtract

/-- Semantic natural-parameter criterion.  Its admissibility remains
all-order; it is not the requested finite-checker equivalence. -/
theorem canonical_actual_natural_growth_step_iff_nativeRH
    (hpower : CanonicalPowerSums)
    (hExtract : DominantExtraction (canonicalCalibration hpower)) :
    (∃ K : ℕ, NaturalGrowthStep actualVariation K) ↔ _root_.RiemannHypothesis :=
  actual_exists_natural_growth_step_iff_nativeRH_of_analytic_inputs
    (canonicalCalibration hpower) hExtract

/-- A natural bound exists under RH, while the universally quantified
verification of that bound remains an analytic obligation. -/
theorem canonical_actual_natural_bound_iff_nativeRH
    (hpower : CanonicalPowerSums)
    (hExtract : DominantExtraction (canonicalCalibration hpower)) :
    (∃ B : ℕ, ∀ n : ℕ, actualVariation n ≤ (B : ℝ)) ↔ _root_.RiemannHypothesis :=
  actual_exists_natural_bound_iff_nativeRH_of_analytic_inputs
    (canonicalCalibration hpower) hExtract

end RH_HilbertLimit
