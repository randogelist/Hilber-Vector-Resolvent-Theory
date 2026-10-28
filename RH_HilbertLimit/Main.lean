import RH_HilbertLimit.Spectral
import RH_HilbertLimit.Vandermonde

/-!
# The current ordinary-limit and RH chain, with its Lean boundary exposed

The finite algebra, geometric upper estimate, Vandermonde lower estimate,
ordinary-limit transfer and literal Mathlib RH geometry are proved below
from the stated inputs.  Two constructions remain open in Lean:

1. Inhabit `ActualSpectralCalibration` for the actual xi moments.
2. Construct `DominantTailData` when its geometric radius exceeds one.

Neither an ordinary limit nor RH nor a bound with rate one is a field of
these inputs.  They are still mathematical hypotheses of the final
declarations and must not be described as discharged by a successful build.

The independently missing estimate `Subexponential actualVariation` is the
RH step of the paper.  No finite raw witness or terminating checker is built
by this file.  Native compilation and axiom audit have not yet been run.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter

namespace RH_HilbertLimit

/-- A finite dominant exponential part and its strictly smaller tail.
This is analytic proof data, not a finite raw-data certificate. -/
structure DominantTailData {ι : Type*} (D : ActualSpectralCalibration ι) where
  width : ℕ
  rate : Fin width → ℂ
  coefficient : Fin width → ℂ
  distinguished : Fin width
  rates_injective : Function.Injective rate
  coefficient_ne_zero : coefficient distinguished ≠ 0
  rates_radius : ∀ i, ‖rate i‖ = spectralRadius D.node
  phase : ℂ
  phase_norm : ‖phase‖ ≤ 1
  tail : ℕ → ℂ
  tailConstant : ℝ
  tailRate : ℝ
  tailConstant_nonneg : 0 ≤ tailConstant
  tailRate_one_le : 1 ≤ tailRate
  tailRate_lt : tailRate < spectralRadius D.node
  expansion : ∀ N,
    rowGenerating actualNormalizedMoment N phase =
      finiteExponentialSum rate coefficient N + tail N
  tail_bound : ∀ N, ‖tail N‖ ≤ tailConstant * tailRate ^ N

/-- The infinite-spectrum extraction obligation, needed only in the case R>1. -/
def DominantExtraction {ι : Type*} (D : ActualSpectralCalibration ι) : Prop :=
  1 < spectralRadius D.node → Nonempty (DominantTailData D)

theorem DominantTailData.envelope {ι : Type*} {D : ActualSpectralCalibration ι}
    (T : DominantTailData D) (N : ℕ) :
    ‖finiteExponentialSum T.rate T.coefficient N + T.tail N‖ ≤ actualVariation N := by
  rw [← T.expansion N]
  exact norm_rowGenerating_le actualNormalizedMoment N T.phase_norm

/-- The nontrivial-rate case: the full ordinary limit follows from the
explicit finite decomposition, not from a limit premise. -/
theorem actual_root_tendsto_of_dominant_tail {ι : Type*}
    (D : ActualSpectralCalibration ι) (T : DominantTailData D) :
    Tendsto (rootScale actualVariation) atTop (𝓝 (spectralRadius D.node)) := by
  have hupper : ∀ᶠ N in atTop,
      actualVariation N ≤ (∑' i, ‖D.node i‖) * ‖T.rate T.distinguished‖ ^ N := by
    filter_upwards with N
    rw [T.rates_radius]
    exact D.variation_upper N
  have htail : T.tailRate < ‖T.rate T.distinguished‖ := by
    rw [T.rates_radius]
    exact T.tailRate_lt
  have h := root_tendsto_of_finite_dominant_tail
    T.rates_injective T.distinguished T.coefficient_ne_zero
    ActualSpectralCalibration.variation_monotone
    T.tailConstant_nonneg D.total_norm_pos T.tailRate_one_le htail
    T.tail_bound T.envelope hupper
  simpa only [T.rates_radius] using h

/-- Main ordinary-limit endpoint.  Both open analytic constructions are
visible parameters.  A compiled instance-free theorem is conditional. -/
theorem actual_root_tendsto_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    Tendsto (rootScale actualVariation) atTop (𝓝 (spectralRadius D.node)) := by
  by_cases hR : spectralRadius D.node = 1
  · have hV : actualVariation = fun _ : ℕ => (1 : ℝ) :=
      funext (D.variation_eq_one_of_radius_one hR)
    have hfun : rootScale actualVariation = fun _ : ℕ => (1 : ℝ) := by
      funext n
      simp only [rootScale, hV, Real.rpow_eq_pow, Real.one_rpow]
    rw [hfun, hR]
    exact tendsto_const_nhds
  · have hgt : 1 < spectralRadius D.node :=
      lt_of_le_of_ne (one_le_spectralRadius D.bounded) (Ne.symm hR)
    obtain ⟨T⟩ := hExtract hgt
    exact actual_root_tendsto_of_dominant_tail D T

theorem exists_actual_root_limit_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    ∃ R : ℝ, 1 ≤ R ∧
      Tendsto (rootScale actualVariation) atTop (𝓝 R) :=
  ⟨spectralRadius D.node, one_le_spectralRadius D.bounded,
    actual_root_tendsto_of_analytic_inputs D hExtract⟩

/-- The value-one criterion is exactly the native Mathlib RH proposition. -/
theorem actual_root_one_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    Tendsto (rootScale actualVariation) atTop (𝓝 1) ↔ _root_.RiemannHypothesis := by
  have hlimit := actual_root_tendsto_of_analytic_inputs D hExtract
  constructor
  · intro hunit
    exact D.radius_one_iff_nativeRH.mp (tendsto_nhds_unique hlimit hunit)
  · intro hRH
    simpa only [D.radius_one_iff_nativeRH.mpr hRH] using hlimit

theorem actual_subexponential_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    Subexponential actualVariation ↔ _root_.RiemannHypothesis := by
  exact (subexponential_iff_rootScale_one
    (Eventually.of_forall D.variation_one_le)).trans
    (actual_root_one_iff_nativeRH_of_analytic_inputs D hExtract)

theorem actual_logScale_zero_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    Tendsto (logScale actualVariation) atTop (𝓝 0) ↔ _root_.RiemannHypothesis := by
  exact (subexponential_iff_logScale_zero
    (Eventually.of_forall D.variation_one_le)).symm.trans
    (actual_subexponential_iff_nativeRH_of_analytic_inputs D hExtract)

theorem actual_all_variation_one_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    (∀ N, actualVariation N = 1) ↔ _root_.RiemannHypothesis := by
  constructor
  · intro hV
    apply (actual_subexponential_iff_nativeRH_of_analytic_inputs D hExtract).mp
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro N
    rw [hV N, one_mul]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Nat.cast_nonneg N))
  · exact D.variation_eq_one_of_nativeRH

theorem actual_weights_nonnegative_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    (∀ N j, j ≤ N → 0 ≤ actualWeight N j) ↔ _root_.RiemannHypothesis := by
  exact (all_rowVariation_eq_one_iff actualNormalizedMoment
    (actualNormalizedMoment_zero (ne_of_gt D.kappa_pos))).symm.trans
    (actual_all_variation_one_iff_nativeRH_of_analytic_inputs D hExtract)

theorem actual_bounded_variation_iff_nativeRH_of_analytic_inputs {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D) :
    (∃ B : ℝ, ∀ N, actualVariation N ≤ B) ↔ _root_.RiemannHypothesis := by
  constructor
  · rintro ⟨B, hB⟩
    apply (actual_subexponential_iff_nativeRH_of_analytic_inputs D hExtract).mp
    have hB1 : 1 ≤ B := (D.variation_one_le 0).trans (hB 0)
    have hBpos : 0 < B := zero_lt_one.trans_le hB1
    intro ε hε
    refine ⟨B, hBpos, ?_⟩
    intro N
    have he : 1 ≤ Real.exp (ε * (N : ℝ)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Nat.cast_nonneg N))
    exact (hB N).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hBpos.le)
  · intro hRH
    exact ⟨1, fun N => (D.variation_eq_one_of_nativeRH hRH N).le⟩

/-- The additional, still open estimate needed for an RH proof. -/
def ActualSubexponentialBound : Prop := Subexponential actualVariation

theorem nativeRH_of_actual_subexponential_bound {ι : Type*}
    (D : ActualSpectralCalibration ι) (hExtract : DominantExtraction D)
    (hbound : ActualSubexponentialBound) : _root_.RiemannHypothesis :=
  (actual_subexponential_iff_nativeRH_of_analytic_inputs D hExtract).mp hbound

end RH_HilbertLimit
