import RH_HilbertLimit.CanonicalBridge
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# All canonical power sums from the actual theta product

Source-only candidate for the user's pinned Mathlib v4.33.0 native compiler.
No Lean compiler has been run locally.

The summable inverse scales already proved in `OriginTrace` control every
resolvent power uniformly on an explicit open neighborhood of zero. Mathlib's
holomorphic derivative-interchange theorem then supplies all derivative
orders. The actual product, the existing reality theorem, and the literal
kappa normalization identify those derivatives with the canonical power sums.

The final theorem has no calibration, RH, power-sum, or derivative-interchange
premise. It does not construct the separate dominant-tail extraction and does
not assert finite-checker completeness or RH.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
open Filter Metric Set

namespace RH_HilbertLimit.CanonicalPowerSumAnalysis

variable {ι : Type*}

/-- A positive bound for every norm in an absolutely summable family. -/
def massBound (b : ι → ℂ) : ℝ := 1 + ∑' i, ‖b i‖

/-- The unit ball is retained for the existing locally uniform product theorem. -/
def resolventDomain (b : ι → ℂ) : Set ℂ :=
  ball 0 1 ∩ {z : ℂ | ‖z‖ * massBound b < (1 / 2 : ℝ)}

def resolvent (b : ι → ℂ) (i : ι) (z : ℂ) : ℂ :=
  b i / (1 + z * b i)

def resolventSeries (b : ι → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' i, resolvent b i z ^ (n + 1)

theorem one_le_massBound (b : ι → ℂ) : 1 ≤ massBound b := by
  have hs : 0 ≤ ∑' i, ‖b i‖ := tsum_nonneg (fun i => norm_nonneg (b i))
  dsimp [massBound]
  linarith

theorem norm_le_massBound {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (i : ι) : ‖b i‖ ≤ massBound b := by
  have hi := hb.le_tsum i (fun j _ => norm_nonneg (b j))
  dsimp [massBound]
  linarith

theorem isOpen_resolventDomain (b : ι → ℂ) : IsOpen (resolventDomain b) := by
  exact isOpen_ball.inter
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const)

theorem zero_mem_resolventDomain (b : ι → ℂ) :
    (0 : ℂ) ∈ resolventDomain b := by
  norm_num [resolventDomain]

theorem norm_mul_lt_half {b : ι → ℂ} (hb : Summable (fun i => ‖b i‖))
    {z : ℂ} (hz : z ∈ resolventDomain b) (i : ι) :
    ‖z * b i‖ < (1 / 2 : ℝ) := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_le_massBound hb i) (norm_nonneg z)).trans_lt
    hz.2

theorem half_lt_norm_denominator {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) :
    (1 / 2 : ℝ) < ‖1 + z * b i‖ := by
  have ht : (1 : ℝ) ≤ ‖1 + z * b i‖ + ‖z * b i‖ := by
    calc
      1 = ‖((1 : ℂ) + z * b i) - z * b i‖ := by simp
      _ ≤ ‖1 + z * b i‖ + ‖z * b i‖ := norm_sub_le _ _
  have hi := norm_mul_lt_half hb hz i
  linarith

theorem denominator_ne_zero {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) : 1 + z * b i ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans
    (half_lt_norm_denominator hb hz i)

theorem norm_resolvent_le {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) :
    ‖resolvent b i z‖ ≤ 2 * ‖b i‖ := by
  have hden := half_lt_norm_denominator hb hz i
  have hdenpos : 0 < ‖1 + z * b i‖ := by linarith
  rw [resolvent, norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  nlinarith [norm_nonneg (b i)]

/-- Every positive integral power has a summable majorant on the same domain. -/
theorem norm_resolvent_pow_le {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) :
    ‖resolvent b i z ^ (n + 1)‖ ≤
      ‖b i‖ * (2 * (2 * massBound b) ^ n) := by
  have hbase := norm_resolvent_le hb hz i
  have htotal : ‖resolvent b i z‖ ≤ 2 * massBound b := by
    exact hbase.trans
      (mul_le_mul_of_nonneg_left (norm_le_massBound hb i) (by norm_num))
  have hmass : 0 ≤ massBound b := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_massBound b)
  calc
    ‖resolvent b i z ^ (n + 1)‖ =
        ‖resolvent b i z‖ ^ n * ‖resolvent b i z‖ := by rw [norm_pow, pow_succ]
    _ ≤ (2 * massBound b) ^ n * (2 * ‖b i‖) := by
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) htotal n) hbase
        (norm_nonneg _) (by positivity)
    _ = ‖b i‖ * (2 * (2 * massBound b) ^ n) := by ring

theorem summable_resolvent_pow {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) {z : ℂ}
    (hz : z ∈ resolventDomain b) :
    Summable (fun i => resolvent b i z ^ (n + 1)) := by
  exact (hb.mul_right (2 * (2 * massBound b) ^ n)).of_norm_bounded
    (norm_resolvent_pow_le hb n hz)

/-- The local product identity is proved from convergence and nonvanishing. -/
theorem logDeriv_affineProduct_hasSum {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) {z : ℂ}
    (hz : z ∈ resolventDomain b) :
    HasSum (fun i => resolvent b i z)
      (logDeriv (fun w : ℂ => ∏' i, (1 + w * b i)) z) := by
  have hfactor (i : ι) :
      logDeriv (fun w : ℂ => 1 + w * b i) z = resolvent b i z := by
    have hd : HasDerivAt (fun w : ℂ => 1 + w * b i) (b i) z := by
      simpa using ((hasDerivAt_id z).mul_const (b i)).const_add 1
    rw [logDeriv_apply, hd.deriv]
    rfl
  have hsum : Summable (fun i => resolvent b i z) := by
    simpa only [Nat.zero_add, pow_one] using summable_resolvent_pow hb 0 hz
  have hm : Summable (fun i => logDeriv (fun w : ℂ => 1 + w * b i) z) := by
    simpa only [hfactor] using hsum
  have hnorm : Summable (fun i => ‖z * b i‖) := by
    simpa only [norm_mul] using hb.mul_left ‖z‖
  have hnez : (∏' i, (1 + z * b i)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (denominator_ne_zero hb hz) hnorm
  have hprod := AngularMaster.affineProduct_hasProdLocallyUniformlyOn_origin hb
  have h := logDeriv_tprod_eq_tsum
    (f := fun i (w : ℂ) => 1 + w * b i) isOpen_ball hz.1
    (denominator_ne_zero hb hz) (fun i => by fun_prop) hm
    hprod.multipliableLocallyUniformlyOn hnez
  have heq : logDeriv (fun w : ℂ => ∏' i, (1 + w * b i)) z =
      ∑' i, resolvent b i z := by
    simpa only [hfactor] using h
  rw [heq]
  exact hsum.hasSum

theorem hasDerivAt_resolvent {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) :
    HasDerivAt (resolvent b i) (-((resolvent b i z) ^ 2)) z := by
  have hd : HasDerivAt (fun w : ℂ => 1 + w * b i) (b i) z := by
    simpa using ((hasDerivAt_id z).mul_const (b i)).const_add 1
  have hne := denominator_ne_zero hb hz i
  have h := (hasDerivAt_const z (b i)).fun_div hd hne
  have hscalar :
      ((0 : ℂ) * (1 + z * b i) - b i * b i) / (1 + z * b i) ^ 2 =
        -((resolvent b i z) ^ 2) := by
    simp only [resolvent, zero_mul, zero_sub, neg_div, div_pow, ← pow_two]
  rw [hscalar] at h
  exact h

theorem hasDerivAt_resolvent_pow {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) {z : ℂ}
    (hz : z ∈ resolventDomain b) (i : ι) :
    HasDerivAt (fun w : ℂ => resolvent b i w ^ (n + 1))
      (-((n + 1 : ℕ) : ℂ) * resolvent b i z ^ (n + 2)) z := by
  have h := (hasDerivAt_resolvent hb hz i).fun_pow (n + 1)
  have hscalar :
      ((n + 1 : ℕ) : ℂ) * resolvent b i z ^ (n + 1 - 1) *
          (-((resolvent b i z) ^ 2)) =
        -((n + 1 : ℕ) : ℂ) * resolvent b i z ^ (n + 2) := by
    simp only [Nat.add_sub_cancel, pow_add, mul_neg, neg_mul, mul_assoc]
  rw [hscalar] at h
  exact h

/-- The derivative recurrence is obtained from Mathlib's holomorphic M-test. -/
theorem deriv_resolventSeries {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) {z : ℂ}
    (hz : z ∈ resolventDomain b) :
    deriv (resolventSeries b n) z =
      -((n + 1 : ℕ) : ℂ) * resolventSeries b (n + 1) z := by
  have hdiff : ∀ i : ι,
      DifferentiableOn ℂ (fun w : ℂ => resolvent b i w ^ (n + 1))
        (resolventDomain b) := by
    intro i w hw
    exact (hasDerivAt_resolvent_pow hb n hw i).differentiableAt.differentiableWithinAt
  have hd := Complex.hasSum_deriv_of_summable_norm
    (hb.mul_right (2 * (2 * massBound b) ^ n)) hdiff
    (isOpen_resolventDomain b)
    (fun i w hw => norm_resolvent_pow_le hb n hw i) hz
  have hderiv : HasSum
      (fun i => -((n + 1 : ℕ) : ℂ) * resolvent b i z ^ (n + 2))
      (deriv (resolventSeries b n) z) := by
    apply hd.congr_fun
    intro i
    exact (hasDerivAt_resolvent_pow hb n hz i).deriv.symm
  have hseries : HasSum
      (fun i => -((n + 1 : ℕ) : ℂ) * resolvent b i z ^ (n + 2))
      (-((n + 1 : ℕ) : ℂ) * resolventSeries b (n + 1) z) := by
    exact (summable_resolvent_pow hb (n + 1) hz).hasSum.mul_left _
  exact hderiv.unique hseries

theorem iteratedDeriv_resolventSeries {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) :
    ∀ z ∈ resolventDomain b,
      iteratedDeriv n (resolventSeries b 0) z =
        ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * resolventSeries b n z := by
  induction n with
  | zero =>
      intro z hz
      simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  | succ n ih =>
      intro z hz
      have heq : iteratedDeriv n (resolventSeries b 0) =ᶠ[𝓝 z]
          (fun w => ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * resolventSeries b n w) := by
        filter_upwards [(isOpen_resolventDomain b).mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field,
        deriv_resolventSeries hb n hz]
      simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- All logarithmic derivatives of an absolutely convergent affine product. -/
theorem iteratedDeriv_logDeriv_affineProduct_zero {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) :
    iteratedDeriv n (logDeriv (fun z : ℂ => ∏' i, (1 + z * b i))) 0 =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * ∑' i, b i ^ (n + 1) := by
  have hlocal : logDeriv (fun z : ℂ => ∏' i, (1 + z * b i)) =ᶠ[𝓝 (0 : ℂ)]
      resolventSeries b 0 := by
    filter_upwards [(isOpen_resolventDomain b).mem_nhds
      (zero_mem_resolventDomain b)] with z hz
    simpa only [resolventSeries, Nat.zero_add, pow_one] using
      (logDeriv_affineProduct_hasSum hb hz).tsum_eq.symm
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hlocal]
  simpa only [resolventSeries, resolvent, zero_mul, add_zero, div_one] using
    iteratedDeriv_resolventSeries hb n 0 (zero_mem_resolventDomain b)

theorem summable_positive_powers {b : ι → ℂ}
    (hb : Summable (fun i => ‖b i‖)) (n : ℕ) :
    Summable (fun i => b i ^ (n + 1)) := by
  simpa only [resolvent, zero_mul, add_zero, div_one] using
    summable_resolvent_pow hb n (zero_mem_resolventDomain b)

end RH_HilbertLimit.CanonicalPowerSumAnalysis

namespace RH_HilbertLimit

open AngularMaster CanonicalPowerSumAnalysis

theorem actualLogDerivative_eq_canonical_product_logDeriv :
    actualLogDerivative = logDeriv
      (fun z : ℂ => ∏' i : ActualPairIndex,
        (1 + z * (actualComplexScale i)⁻¹)) := by
  have hfun : AWPIRH.theta = fun z : ℂ => AWPIRH.theta 0 *
      ∏' i : ActualPairIndex, (1 + z * (actualComplexScale i)⁻¹) := by
    funext z
    simpa only [div_eq_mul_inv] using actual_theta_normalized_complex_factorization z
  funext z
  change logDeriv AWPIRH.theta z = _
  rw [hfun, logDeriv_const_mul _ _ actual_theta_zero_ne_zero]

/-- A local resolvent series for the literal, unchanged theta logarithmic derivative. -/
theorem actualLogDerivative_resolvent_hasSum {z : ℂ}
    (hz : z ∈ resolventDomain
      (fun i : ActualPairIndex => (actualComplexScale i)⁻¹)) :
    HasSum (fun i : ActualPairIndex =>
      (actualComplexScale i)⁻¹ / (1 + z * (actualComplexScale i)⁻¹))
      (actualLogDerivative z) := by
  rw [actualLogDerivative_eq_canonical_product_logDeriv]
  exact logDeriv_affineProduct_hasSum actualComplexScale_norm_inv_summable hz

/-- The unnormalized moments are the inverse-scale power sums at every order. -/
theorem actualComplexMoment_eq_canonical_powerSum (n : ℕ) :
    actualComplexMoment n =
      ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹) ^ (n + 1) := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [actualComplexMoment, actualLogDerivative_eq_canonical_product_logDeriv,
    iteratedDeriv_logDeriv_affineProduct_zero actualComplexScale_norm_inv_summable n]
  calc
    (-1 : ℂ) ^ n *
        (((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
          ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹) ^ (n + 1)) /
        (n.factorial : ℂ) =
      ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
        ((n.factorial : ℂ) *
          ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹) ^ (n + 1)) /
        (n.factorial : ℂ) := by ring
    _ = ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹) ^ (n + 1) := by
      rw [hsign, one_mul]
      field_simp [hfac] <;> ring

theorem actualComplexMoment_hasSum_canonical_powers (n : ℕ) :
    HasSum (fun i : ActualPairIndex => ((actualComplexScale i)⁻¹) ^ (n + 1))
      (actualComplexMoment n) := by
  rw [actualComplexMoment_eq_canonical_powerSum]
  exact (summable_positive_powers actualComplexScale_norm_inv_summable n).hasSum

/-- The exact normalized canonical nodes supply every actual normalized moment. -/
theorem canonicalNode_power_sum (n : ℕ) :
    HasSum (fun i : ActualPairIndex => canonicalNode i ^ (n + 1))
      (actualNormalizedMoment n : ℂ) := by
  have h := (actualComplexMoment_hasSum_canonical_powers n).mul_left
    (((actualKappa : ℂ)⁻¹) ^ (n + 1))
  have htarget : (((actualKappa : ℂ)⁻¹) ^ (n + 1)) * actualComplexMoment n =
      (actualNormalizedMoment n : ℂ) := by
    rw [actualComplexMoment_eq_ofReal_actualMoment, actualNormalizedMoment,
      Complex.ofReal_div, Complex.ofReal_pow, inv_pow, div_eq_mul_inv]
    exact mul_comm _ _
  rw [htarget] at h
  apply h.congr_fun
  intro i
  rw [canonicalNode_eq_inverseScale_mul, mul_pow]

/-- The previously explicit all-order calibration input is derived here. -/
theorem canonicalPowerSums : CanonicalPowerSums := canonicalNode_power_sum

end RH_HilbertLimit
