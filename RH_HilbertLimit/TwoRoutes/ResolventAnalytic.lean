import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Analytic compact-interval resolvents

The measure is an arbitrary finite positive measure on `[0,1]`.  No RH statement,
zero location statement, or representation identity is assumed in this module.
The differentiation argument uses a uniform positive denominator bound obtained
from compactness, and a constant integrable majorant on a complex neighborhood.

Source construction: this module has not been submitted to a Lean kernel.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace RH_HilbertLimit.TwoRoutes.MeasureResolvent

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def denominator (k : ℝ) (z : ℂ) (q : UnitInterval) : ℂ :=
  1 + (k : ℂ) * z * ((q : ℝ) : ℂ)

def kernel (k : ℝ) (n : ℕ) (z : ℂ) (q : UnitInterval) : ℂ :=
  ((q : ℝ) : ℂ) ^ n / denominator k z q ^ (n + 1)

def transform (k : ℝ) (σ : Measure UnitInterval) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ q, kernel k n z q ∂σ

def domain (k : ℝ) : Set ℂ := {z | ∀ q, denominator k z q ≠ 0}

theorem norm_coe_le_one (q : UnitInterval) : ‖((q : ℝ) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg q.property.1]
    using q.property.2

theorem continuous_denominator (k : ℝ) (z : ℂ) :
    Continuous (denominator k z) := by
  unfold denominator
  fun_prop

theorem continuous_kernel {k : ℝ} {z : ℂ} (hz : z ∈ domain k) (n : ℕ) :
    Continuous (kernel k n z) := by
  exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow n |>.div
    ((continuous_denominator k z).pow (n + 1)) (fun q => pow_ne_zero _ (hz q))

/-- Compactness makes the denominator lower bound uniform in the parameter. -/
theorem exists_local_lower_bound {k : ℝ} (hk : 0 < k) {z₀ : ℂ}
    (hz₀ : z₀ ∈ domain k) :
    ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball z₀ ε, ∀ q : UnitInterval,
      c ≤ ‖denominator k z q‖ := by
  obtain ⟨a, ha, hbound⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set UnitInterval)).exists_forall_le'
      (continuous_denominator k z₀).norm.continuousOn
      (fun q _ => norm_pos_iff.mpr (hz₀ q))
  refine ⟨a / 2, by positivity, a / (2 * k), by positivity, ?_⟩
  intro z hz q
  have hdist : ‖z - z₀‖ < a / (2 * k) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hvar : k * ‖z - z₀‖ < a / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * k)).mp hdist
    nlinarith
  have hsub : ‖denominator k z₀ q - denominator k z q‖ ≤ k * ‖z - z₀‖ := by
    have heq : denominator k z₀ q - denominator k z q =
        (k : ℂ) * (z₀ - z) * ((q : ℝ) : ℂ) := by
      unfold denominator
      ring
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hk, norm_sub_rev]
    exact mul_le_of_le_one_right (by positivity) (norm_coe_le_one q)
  have htri : ‖denominator k z₀ q‖ ≤
      ‖denominator k z₀ q - denominator k z q‖ + ‖denominator k z q‖ :=
    norm_le_norm_sub_add _ _
  have hb := hbound q (Set.mem_univ q)
  linarith

theorem isOpen_domain {k : ℝ} (hk : 0 < k) : IsOpen (domain k) := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨c, hc, ε, hε, hbound⟩ := exists_local_lower_bound hk hz
  refine ⟨ε, hε, ?_⟩
  intro w hw q
  exact norm_pos_iff.mp (lt_of_lt_of_le hc (hbound w hw q))

theorem kernel_norm_le {k c : ℝ} {z : ℂ} (hc : 0 < c)
    (hbound : ∀ q : UnitInterval, c ≤ ‖denominator k z q‖) (n : ℕ)
    (q : UnitInterval) : ‖kernel k n z q‖ ≤ 1 / c ^ (n + 1) := by
  rw [kernel, norm_div, norm_pow, norm_pow]
  calc
    ‖((q : ℝ) : ℂ)‖ ^ n / ‖denominator k z q‖ ^ (n + 1)
        ≤ 1 / ‖denominator k z q‖ ^ (n + 1) :=
      div_le_div_of_nonneg_right
        (pow_le_one₀ (norm_nonneg _) (norm_coe_le_one q)) (by positivity)
    _ ≤ 1 / c ^ (n + 1) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hc _)
        (pow_le_pow_left₀ hc.le (hbound q) _)

theorem hasDerivAt_kernel {k : ℝ} {z : ℂ} {q : UnitInterval}
    (hz : denominator k z q ≠ 0) (n : ℕ) :
    HasDerivAt (fun w => kernel k n w q)
      (-((n + 1 : ℕ) : ℂ) * (k : ℂ) * kernel k (n + 1) z q) z := by
  have hd : HasDerivAt (fun w : ℂ => denominator k w q)
      ((k : ℂ) * ((q : ℝ) : ℂ)) z := by
    simpa only [denominator, mul_one] using!
      (((hasDerivAt_id z).const_mul (k : ℂ)).mul_const ((q : ℝ) : ℂ)).const_add 1
  have h := (hasDerivAt_const z (((q : ℝ) : ℂ) ^ n)).div
    (hd.pow (n + 1)) (pow_ne_zero _ hz)
  refine h.congr_deriv ?_
  simp only [kernel, Pi.pow_apply, Nat.add_sub_cancel, zero_mul, zero_sub]
  field_simp [pow_succ, hz]
  <;> ring

variable {k : ℝ} {σ : Measure UnitInterval} [IsFiniteMeasure σ] {z : ℂ}

theorem integrable_kernel (hz : z ∈ domain k) (n : ℕ) :
    Integrable (kernel k n z) σ := by
  have h := ContinuousOn.integrableOn_compact
    (μ := σ) (isCompact_univ : IsCompact (Set.univ : Set UnitInterval))
    (continuous_kernel hz n).continuousOn
  simpa only [integrableOn_univ] using h

theorem hasDerivAt_transform (hk : 0 < k) (hz : z ∈ domain k) (n : ℕ) :
    HasDerivAt (transform k σ n)
      (-((n + 1 : ℕ) : ℂ) * (k : ℂ) * transform k σ (n + 1) z) z := by
  obtain ⟨c, hc, ε, hε, hbound⟩ := exists_local_lower_bound hk hz
  let C : ℂ := -((n + 1 : ℕ) : ℂ) * (k : ℂ)
  let B : ℝ := ‖C‖ * (1 / c ^ ((n + 1) + 1))
  have hdom : ∀ w ∈ Metric.ball z ε, w ∈ domain k := by
    intro w hw q
    exact norm_pos_iff.mp (lt_of_lt_of_le hc (hbound w hw q))
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (kernel k n w) σ := by
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    exact (continuous_kernel (hdom w hw) n).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun q => C * kernel k (n + 1) z q) σ :=
    (continuous_const.mul (continuous_kernel hz (n + 1))).aestronglyMeasurable
  have hb : ∀ᵐ q ∂σ, ∀ w ∈ Metric.ball z ε,
      ‖C * kernel k (n + 1) w q‖ ≤ B := by
    exact Filter.Eventually.of_forall fun q w hw => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (kernel_norm_le hc (hbound w hw) (n + 1) q) (norm_nonneg C)
  have hdiff : ∀ᵐ q ∂σ, ∀ w ∈ Metric.ball z ε,
      HasDerivAt (fun w => kernel k n w q) (C * kernel k (n + 1) w q) w := by
    exact Filter.Eventually.of_forall fun q w hw => hasDerivAt_kernel (hdom w hw q) n
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := σ) (F := fun w q => kernel k n w q)
    (F' := fun w q => C * kernel k (n + 1) w q) (bound := fun _ => B)
    (Metric.ball_mem_nhds z hε) hmeas (integrable_kernel hz n) hmeas' hb
    (integrable_const B) hdiff
  simpa only [transform, integral_const_mul, C] using! h.2

theorem deriv_transform (hk : 0 < k) (hz : z ∈ domain k) (n : ℕ) :
    deriv (transform k σ n) z =
      -((n + 1 : ℕ) : ℂ) * (k : ℂ) * transform k σ (n + 1) z :=
  (hasDerivAt_transform hk hz n).deriv

theorem analyticAt_transform (hk : 0 < k) (hz : z ∈ domain k) (n : ℕ) :
    AnalyticAt ℂ (transform k σ n) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_domain hk).mem_nhds hz] with w hw
  exact (hasDerivAt_transform hk hw n).differentiableAt

theorem analyticOnNhd_transform (hk : 0 < k) (n : ℕ) :
    AnalyticOnNhd ℂ (transform k σ n) (domain k) :=
  fun _ hz => analyticAt_transform hk hz n

theorem zero_mem_domain (k : ℝ) : (0 : ℂ) ∈ domain k := by
  intro q
  simp [denominator]

theorem upperHalfPlane_subset_domain (hk : 0 < k) :
    {z : ℂ | 0 < z.im} ⊆ domain k := by
  intro z hz q hzero
  by_cases hq : (q : ℝ) = 0
  · simpa [denominator, hq] using hzero
  · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq)
    have him := congrArg Complex.im hzero
    have himpos : 0 < k * z.im * (q : ℝ) := mul_pos (mul_pos hk hz) hqpos
    simp only [denominator, Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
      Complex.zero_im] at him
    linarith

end RH_HilbertLimit.TwoRoutes.MeasureResolvent
