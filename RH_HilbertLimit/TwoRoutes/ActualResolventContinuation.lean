import RH_HilbertLimit.TwoRoutes.ActualHerglotzClosure
import Mathlib.Analysis.Convex.PathConnected

/-!
# Continuing the positive-measure resolvent without assuming zero-freeness

The continuation is applied to the analytic defect `F' - S F`, not to a
quotient across possible zeros. An origin germ is transferred to a small
upper-half-plane seed, and the analytic identity theorem propagates it over
that connected half-plane. Actual pole exclusion is downstream.

This avoids an assumption that the unknown nonreal zeros are already absent.
Prepared without running Lean, Lake, compiler, or native axiom audit.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Metric
open scoped Topology

namespace RH_HilbertLimit.TwoRoutes

def resolventUpperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

theorem resolventUpperHalfPlane_convex : Convex ℝ resolventUpperHalfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y).im
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  change 0 < x.im at hx
  change 0 < y.im at hy
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy
  · have hap : 0 < a := by
      by_contra hn
      exact ha0 (le_antisymm (le_of_not_gt hn) ha)
    exact add_pos_of_pos_of_nonneg (mul_pos hap hx) (mul_nonneg hb hy.le)

theorem resolventUpperHalfPlane_preconnected :
    IsPreconnected resolventUpperHalfPlane :=
  resolventUpperHalfPlane_convex.isPreconnected

/-- Analytic ODE continuation from an origin germ to the whole open upper
half-plane. The local analytic resolvent need not be presumed to agree with
the logarithmic derivative outside that germ. -/
theorem entire_ode_on_upperHalfPlane_of_origin_germ
    {F S : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hS : AnalyticOnNhd ℂ S resolventUpperHalfPlane)
    (hgerm : ∀ᶠ z : ℂ in 𝓝 0, deriv F z = S z * F z) :
    ∀ z : ℂ, 0 < z.im → deriv F z = S z * F z := by
  let defect : ℂ → ℂ := fun z => deriv F z - S z * F z
  have hdefect : AnalyticOnNhd ℂ defect resolventUpperHalfPlane := by
    intro z hz
    exact (hF z (Set.mem_univ z)).deriv.sub
      ((hS z hz).mul (hF z (Set.mem_univ z)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgerm
  let seed : ℂ := ((ε / 2 : ℝ) : ℂ) * Complex.I
  have hseed_im : seed.im = ε / 2 := by simp [seed]
  have hseed_norm : ‖seed‖ = ε / 2 := by
    simp only [seed, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  have hseed : seed ∈ resolventUpperHalfPlane := by
    change 0 < seed.im
    rw [hseed_im]
    exact half_pos hε
  have hseed_ball : seed ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, hseed_norm]
    linarith
  have hlocal : defect =ᶠ[𝓝 seed] 0 := by
    have hnbhd : Metric.ball (0 : ℂ) ε ∈ 𝓝 seed :=
      isOpen_ball.mem_nhds hseed_ball
    filter_upwards [hnbhd] with z hz
    change deriv F z - S z * F z = 0
    exact sub_eq_zero.mpr (hball hz)
  have hzeroOn : Set.EqOn defect 0 resolventUpperHalfPlane :=
    hdefect.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      resolventUpperHalfPlane_preconnected hseed hlocal
  intro z hz
  have h := hzeroOn hz
  exact sub_eq_zero.mp h

/-- A complex resolvent matching the actual logarithmic derivative near the
origin matches it at every upper-half-plane point with nonzero denominator.
No global zero-free hypothesis is used for the continuation. -/
theorem actual_logDerivative_eq_of_analytic_resolvent_germ
    {S : ℂ → ℂ}
    (hS : AnalyticOnNhd ℂ S resolventUpperHalfPlane)
    (hgerm : actualLogDerivative =ᶠ[𝓝 (0 : ℂ)] S) :
    ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 →
      actualLogDerivative z = S z := by
  have hopen : IsOpen {z : ℂ | AWPIRH.theta z ≠ 0} :=
    (isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl.preimage
      AWPIRH.theta_continuous
  have hnonzero : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), AWPIRH.theta z ≠ 0 :=
    hopen.mem_nhds AngularMaster.actual_theta_zero_ne_zero
  have hodeGerm : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      deriv AWPIRH.theta z = S z * AWPIRH.theta z := by
    filter_upwards [hgerm, hnonzero] with z heq hne
    change deriv AWPIRH.theta z / AWPIRH.theta z = S z at heq
    exact (div_eq_iff hne).mp heq
  have hode := entire_ode_on_upperHalfPlane_of_origin_germ
    AWPIRH.theta_entire hS hodeGerm
  intro z hz hne
  change deriv AWPIRH.theta z / AWPIRH.theta z = S z
  exact (div_eq_iff hne).mpr (hode z hz)

/-- Closed actual analytic endpoint for the independent positive-measure
route: only the analytic Stieltjes resolvent, its sign and its origin germ
are needed. The local pole and the native RH binding are constructed. -/
theorem nativeRH_of_analytic_positive_resolvent_germ
    {S : ℂ → ℂ}
    (hS : AnalyticOnNhd ℂ S resolventUpperHalfPlane)
    (hSign : ∀ z : ℂ, 0 < z.im → (S z).im ≤ 0)
    (hgerm : actualLogDerivative =ᶠ[𝓝 (0 : ℂ)] S) :
    _root_.RiemannHypothesis := by
  apply nativeRH_of_actual_logDerivative_im_nonpos
  intro z hz hne
  rw [actual_logDerivative_eq_of_analytic_resolvent_germ hS hgerm z hz hne]
  exact hSign z hz

end RH_HilbertLimit.TwoRoutes
