import RH_HilbertLimit.TwoRoutes.ResolventAnalytic
import RH_HilbertLimit.TwoRoutes.ActualResolventContinuation
import RH_HilbertLimit.TwoRoutes.HausdorffMeasure
import RH_HilbertLimit.ActualMomentReality
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Closing the actual positive-measure route

The Hausdorff measure is turned into a complex resolvent. Compact support
gives holomorphy near zero and in the upper half-plane. Its exact moments
give every derivative of the *unchanged* actual logarithmic derivative.
Equality of the convergent Taylor germs then feeds analytic ODE continuation
and the actual nonreal-pole exclusion theorem.

This is the compressed measure--resolvent closure. It does not claim a
formalization of the longer Widder/angular-PDE construction. It does not
invoke the first route's spectral extraction or RH conclusion.

Source prepared without running Lean, Lake, a compiler, or an axiom audit.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace RH_HilbertLimit.TwoRoutes.MeasureResolvent

/-- The probability measure's Stieltjes resolvent, with the actual scaling
retained explicitly. -/
def resolvent (k : ℝ) (σ : Measure UnitInterval) (z : ℂ) : ℂ :=
  (k : ℂ) * transform k σ 0 z

theorem transform_zero (k : ℝ) (σ : Measure UnitInterval) (n : ℕ) :
    transform k σ n 0 = ((∫ q, (q : ℝ) ^ n ∂σ) : ℂ) := by
  unfold transform
  simp only [kernel, denominator, mul_zero, zero_mul, add_zero, one_pow, div_one]

/-- Differentiating the compact kernel tower computes every resolvent
derivative throughout its denominator domain. -/
theorem iteratedDeriv_resolvent (k : ℝ) (σ : Measure UnitInterval)
    [IsFiniteMeasure σ] (hk : 0 < k) (n : ℕ) :
    ∀ z : ℂ, z ∈ domain k →
      iteratedDeriv n (resolvent k σ) z =
        (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (k : ℂ) ^ (n + 1)) *
          transform k σ n z := by
  induction n with
  | zero =>
      intro z hz
      simp only [iteratedDeriv_zero, resolvent, pow_zero, Nat.factorial_zero,
        Nat.cast_one, one_mul, Nat.zero_add, pow_one]
  | succ n ih =>
      intro z hz
      have heq : iteratedDeriv n (resolvent k σ) =ᶠ[𝓝 z]
          (fun w => (((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
            (k : ℂ) ^ (n + 1)) * transform k σ n w) := by
        filter_upwards [(isOpen_domain hk).mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field,
        deriv_transform hk hz n]
      simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

theorem analyticAt_resolvent (k : ℝ) (σ : Measure UnitInterval)
    [IsFiniteMeasure σ] (hk : 0 < k) {z : ℂ} (hz : z ∈ domain k) :
    AnalyticAt ℂ (resolvent k σ) z :=
  analyticAt_const.mul (analyticAt_transform hk hz 0)

/-- The positive kernel agrees algebraically with the compact-kernel tower. -/
theorem resolvent_eq_integral_positiveKernel (k : ℝ)
    (σ : Measure UnitInterval) (z : ℂ) :
    resolvent k σ z =
      ∫ q, positiveResolventKernel k (q : ℝ) z ∂σ := by
  unfold resolvent transform
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  have hd : denominator k z q = 1 + ((k * (q : ℝ) : ℝ) : ℂ) * z := by
    simp only [denominator, Complex.ofReal_mul]
    ring
  simp only [kernel, Nat.zero_add, pow_one, pow_zero, hd,
    positiveResolventKernel, div_eq_mul_inv, one_mul]

theorem resolvent_im_nonpos (k : ℝ) (σ : Measure UnitInterval)
    [IsFiniteMeasure σ] (hk : 0 < k) {z : ℂ} (hz : 0 < z.im) :
    (resolvent k σ z).im ≤ 0 := by
  have hdom : z ∈ domain k := upperHalfPlane_subset_domain hk hz
  have hint : Integrable (fun q : UnitInterval =>
      positiveResolventKernel k (q : ℝ) z) σ := by
    have h := (integrable_kernel hdom 0 (σ := σ)).const_mul (k : ℂ)
    convert h using 1
    funext q
    have hd : denominator k z q = 1 + ((k * (q : ℝ) : ℝ) : ℂ) * z := by
      simp only [denominator, Complex.ofReal_mul]
      ring
    simp only [kernel, Nat.zero_add, pow_one, pow_zero, hd,
      positiveResolventKernel, div_eq_mul_inv, one_mul]
  have him :
      (∫ q : UnitInterval, positiveResolventKernel k (q : ℝ) z ∂σ).im =
        ∫ q : UnitInterval, (positiveResolventKernel k (q : ℝ) z).im ∂σ := by
    simpa only [RCLike.im_to_complex] using! (integral_im hint).symm
  rw [resolvent_eq_integral_positiveKernel, him]
  apply integral_nonpos
  intro q
  exact positiveResolventKernel_im_nonpos hk.le q.property.1 hz

end RH_HilbertLimit.TwoRoutes.MeasureResolvent

namespace RH_HilbertLimit.TwoRoutes

open MeasureResolvent

/-- Reading the derivative from the exact definitions. Reality is the
previously proved Schwarz-reflection identity, not an RH assumption. -/
theorem actual_iteratedDeriv_logDerivative_zero (n : ℕ) :
    iteratedDeriv n actualLogDerivative 0 =
      (((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        (actualKappa : ℂ) ^ (n + 1)) * (actualNormalizedMoment n : ℂ) := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hk : (actualKappa : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt actualKappa_pos
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hm := actualComplexMoment_eq_ofReal_actualMoment n
  rw [actualComplexMoment] at hm
  have hmul := (div_eq_iff hfac).mp hm
  have hd : iteratedDeriv n actualLogDerivative 0 =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (actualMoment n : ℂ) := by
    calc
      iteratedDeriv n actualLogDerivative 0 =
          ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
            iteratedDeriv n actualLogDerivative 0 := by rw [hsign, one_mul]
      _ = (-1 : ℂ) ^ n *
          ((-1 : ℂ) ^ n * iteratedDeriv n actualLogDerivative 0) := by ring
      _ = (-1 : ℂ) ^ n * ((actualMoment n : ℂ) * (n.factorial : ℂ)) := by
        rw [hmul]
      _ = _ := by ring
  have hnorm : (actualMoment n : ℂ) =
      (actualKappa : ℂ) ^ (n + 1) * (actualNormalizedMoment n : ℂ) := by
    rw [actualNormalizedMoment, Complex.ofReal_div, Complex.ofReal_pow]
    field_simp [hk]
    <;> ring
  rw [hd, hnorm]
  ring

/-- Equal Taylor derivatives of analytic functions give equality of germs.
This uses convergent formal power series, not equality of merely formal
coefficient lists. -/
theorem analytic_eventuallyEq_of_iteratedDeriv_eq
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hderiv : ∀ n : ℕ, iteratedDeriv n f z = iteratedDeriv n g z) :
    f =ᶠ[𝓝 z] g := by
  have hseries :
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n f z / (n.factorial : ℂ))) =
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n g z / (n.factorial : ℂ))) := by
    congr 1
    funext n
    rw [hderiv n]
  have hfs := hf.hasFPowerSeriesAt
  rw [hseries] at hfs
  filter_upwards [hfs.eventually_hasSum_sub,
    hg.hasFPowerSeriesAt.eventually_hasSum_sub] with w hwf hwg
  exact hwf.unique hwg

/-- The actual moment identities fix the origin germ of the integral
resolvent without any appeal to spectral location. -/
theorem actual_logDerivative_resolvent_germ
    (σ : Measure UnitInterval) [IsFiniteMeasure σ]
    (hmoment : ∀ n : ℕ,
      (∫ q, (q : ℝ) ^ n ∂σ) = actualNormalizedMoment n) :
    actualLogDerivative =ᶠ[𝓝 (0 : ℂ)] resolvent actualKappa σ := by
  have hR : AnalyticAt ℂ actualLogDerivative (0 : ℂ) := by
    exact (AWPIRH.theta_analyticAt 0).deriv.div
      (AWPIRH.theta_analyticAt 0) AngularMaster.actual_theta_zero_ne_zero
  apply analytic_eventuallyEq_of_iteratedDeriv_eq hR
    (analyticAt_resolvent actualKappa σ actualKappa_pos (zero_mem_domain actualKappa))
  intro n
  have hcomplex : (∫ q : UnitInterval, ((q : ℝ) : ℂ) ^ n ∂σ) =
      (actualNormalizedMoment n : ℂ) := by
    calc
      _ = Complex.ofReal ((∫ q : UnitInterval, (q : ℝ) ^ n ∂σ) : ℝ) := by
        simpa only [Complex.ofReal_pow] using!
          (integral_complex_ofReal (μ := σ)
            (f := fun q : UnitInterval => (q : ℝ) ^ n))
      _ = _ := congrArg Complex.ofReal (hmoment n)
  rw [actual_iteratedDeriv_logDerivative_zero,
    iteratedDeriv_resolvent actualKappa σ actualKappa_pos n 0
      (zero_mem_domain actualKappa), transform_zero, hcomplex]

/-- A genuine finite positive measure with the exact actual moments implies
literal Mathlib RH by analytic continuation and nonreal-pole exclusion. -/
theorem nativeRH_of_actual_hausdorff_moments
    (σ : Measure UnitInterval) [IsFiniteMeasure σ]
    (hmoment : ∀ n : ℕ,
      (∫ q, (q : ℝ) ^ n ∂σ) = actualNormalizedMoment n) :
    _root_.RiemannHypothesis := by
  apply nativeRH_of_analytic_positive_resolvent_germ
    (S := resolvent actualKappa σ)
  · intro z hz
    exact analyticAt_resolvent actualKappa σ actualKappa_pos
      (upperHalfPlane_subset_domain actualKappa_pos hz)
  · intro z hz
    exact resolvent_im_nonpos actualKappa σ actualKappa_pos hz
  · exact actual_logDerivative_resolvent_germ σ hmoment

/-- The second route's endpoint. The Hausdorff measure is constructed from
H00, and all downstream analytic hypotheses are proved above. -/
theorem nativeRH_of_H00_via_measure_resolvent (h : H00) :
    _root_.RiemannHypothesis := by
  exact nativeRH_of_actual_hausdorff_moments (actualHausdorffMeasure h)
    (actualHausdorffMeasure_moment h)

end RH_HilbertLimit.TwoRoutes
