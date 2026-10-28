import RH_HilbertLimit.TwoRoutes.ActualPositivePrefix
import RiemannHypothesis.RealZeros.EntireFunctions

/-!
# Actual RH from the positive-resolvent sign

This is the nonreal-pole closure for the second, positive-measure route.
It reuses the constructed entire-function local-pole engine, not the first
route's spectral extraction or RH conclusion. In particular, no local-pole
existence premise is left at the actual RH endpoint.

The Stieltjes/resolvent construction must supply the displayed sign law.
The finite Bernstein resolvents are shown to satisfy it directly from H00.

Prepared without running Lean, Lake, a compiler, or a native axiom audit.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology BigOperators
open Filter ComplexConjugate

namespace RH_HilbertLimit.TwoRoutes

/-- The normalized Stieltjes kernel, including the harmless q=0 endpoint. -/
def positiveResolventKernel (κ q : ℝ) (z : ℂ) : ℂ :=
  (κ : ℂ) / (1 + ((κ * q : ℝ) : ℂ) * z)

theorem positiveResolventKernel_im_nonpos
    {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 0 ≤ q)
    {z : ℂ} (hz : 0 < z.im) :
    (positiveResolventKernel κ q z).im ≤ 0 := by
  unfold positiveResolventKernel
  rw [Complex.div_im]
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, zero_mul, zero_add, add_zero,
    zero_div, zero_sub, neg_div]
  exact neg_nonpos.mpr (div_nonneg
    (mul_nonneg hκ (mul_nonneg (mul_nonneg hκ hq) hz.le))
    (Complex.normSq_nonneg _))

/-- A finite actual Bernstein approximation to the complex Stieltjes resolvent. -/
def actualResolventApproximation (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (actualWeight N j : ℂ) *
    positiveResolventKernel actualKappa ((j : ℝ) / N) z

/-- This is a direct sign consequence of the common zero-budget hypothesis. -/
theorem actualResolventApproximation_im_nonpos
    (h : H00) (N : ℕ) {z : ℂ} (hz : 0 < z.im) :
    (actualResolventApproximation N z).im ≤ 0 := by
  unfold actualResolventApproximation
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro j hj
  have hjN : j ≤ N := by
    have hj' := Finset.mem_range.mp hj
    omega
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos
    (actual_weights_nonnegative_of_H00 h N j hjN)
    (positiveResolventKernel_im_nonpos actualKappa_pos.le
      (bernsteinGrid_mem_Icc N j hjN).1 hz)

/-- The complete existing entire-function engine constructs the necessary
local pole internally. No off-axis zero-location premise is assumed. -/
theorem actual_theta_no_upper_zeros_of_logDerivative_im_nonpos
    (hSign : ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 →
      (actualLogDerivative z).im ≤ 0) :
    ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 := by
  apply OverflowResidueRH.entire_function_no_upper_zeros_of_analytic_nontrivial
    AWPIRH.theta AWPIRH.theta_entire
    ⟨0, AngularMaster.actual_theta_zero_ne_zero⟩
  intro z hz hne
  exact hSign z hz hne

/-- Conjugate-zero symmetry upgrades upper-half-plane exclusion to reality
of every actual theta zero. Only zero symmetry, not a Schwarz formula for the
entire function, is required here. -/
theorem actual_theta_zero_real_of_logDerivative_im_nonpos
    (hSign : ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 →
      (actualLogDerivative z).im ≤ 0)
    {z : ℂ} (hzero : AWPIRH.theta z = 0) : z.im = 0 := by
  have hUpper := actual_theta_no_upper_zeros_of_logDerivative_im_nonpos hSign
  by_contra him
  by_cases hz : 0 < z.im
  · exact hUpper z hz hzero
  · have hneg : z.im < 0 := by
      by_contra hn
      exact him (le_antisymm (le_of_not_gt hz) (le_of_not_gt hn))
    have hconj : 0 < (conj z).im := by
      simpa only [Complex.conj_im] using neg_pos.mpr hneg
    exact hUpper (conj z) hconj (AngularMaster.theta_zero_conj hzero)

/-- Literal Mathlib RH from the actual Stieltjes/anti-Herglotz sign.

This endpoint uses the actual xi/theta binding and the unconditional nonzero
height of xi zeros. Its proof never invokes route one's RH equivalence.
Positive-real theta zero exclusion is unnecessary in this formulation: for
an actual xi zero, reality of its centered square and nonzero height force
its real part to be exactly 1/2. -/
theorem nativeRH_of_actual_logDerivative_im_nonpos
    (hSign : ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 →
      (actualLogDerivative z).im ≤ 0) : _root_.RiemannHypothesis := by
  apply nativeRH_iff_xiZerosCritical.mpr
  intro s hs
  have hheight := AngularMaster.actual_xi_zero_one_lt_abs_im hs
  have him : s.im ≠ 0 := by
    intro himzero
    rw [himzero, abs_zero] at hheight
    norm_num at hheight
  have htheta : AWPIRH.theta ((s - (1 / 2 : ℂ)) ^ 2) = 0 := by
    rw [AWPIRH.theta_square]
    change AWPIRH.xi ((1 / 2 : ℂ) + (s - (1 / 2 : ℂ))) = 0
    have heq : (1 / 2 : ℂ) + (s - (1 / 2 : ℂ)) = s := by ring
    rw [heq]
    exact hs
  have hreal := actual_theta_zero_real_of_logDerivative_im_nonpos hSign htheta
  have himsquare : ((s - (1 / 2 : ℂ)) ^ 2).im =
      2 * (s.re - (1 / 2 : ℝ)) * s.im := by
    simp [pow_two, Complex.mul_im]
    <;> ring
  rw [himsquare] at hreal
  have hmul : (s.re - (1 / 2 : ℝ)) * s.im = 0 := by
    nlinarith [hreal]
  have hre : s.re - (1 / 2 : ℝ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_right him
  linarith

/-- A limit of the actual finite positive resolvents has the required sign.
The supplied convergence is an explicit analytic premise of this transfer
lemma; it is not asserted by definition or by an axiom. -/
theorem actual_logDerivative_im_nonpos_of_resolvent_limit
    (h : H00) {z : ℂ} (hz : 0 < z.im)
    (hlimit : Tendsto (fun N : ℕ => actualResolventApproximation N z)
      atTop (𝓝 (actualLogDerivative z))) :
    (actualLogDerivative z).im ≤ 0 := by
  have himlimit := Complex.continuous_im.continuousAt.tendsto.comp hlimit
  apply le_of_tendsto himlimit
  exact Filter.Eventually.of_forall
    (fun N => actualResolventApproximation_im_nonpos h N hz)

end RH_HilbertLimit.TwoRoutes
