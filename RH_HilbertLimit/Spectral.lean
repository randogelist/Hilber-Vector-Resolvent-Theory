import RH_HilbertLimit.ActualXi
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.GCongr

/-!
# Spectral expansion, exact positive rows, and the geometric upper bound

All results in `ActualSpectralCalibration` have the classical actual-xi
calibration as an explicit parameter.  This module proves the finite/series
transfers from that parameter; it does not declare an instance of it.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter

namespace RH_HilbertLimit

def spectralTerm (N j : ℕ) (z : ℂ) : ℂ :=
  (Nat.choose N j : ℂ) * z ^ (j + 1) * (1 - z) ^ (N - j)

theorem norm_spectralTerm (N j : ℕ) (z : ℂ) :
    ‖spectralTerm N j z‖ =
      (Nat.choose N j : ℝ) * ‖z‖ ^ (j + 1) * ‖1 - z‖ ^ (N - j) := by
  simp only [spectralTerm, norm_mul, norm_pow, Complex.norm_natCast]

theorem sum_norm_spectralTerm (N : ℕ) (z : ℂ) :
    (∑ j ∈ Finset.range (N + 1), ‖spectralTerm N j z‖) =
      ‖z‖ * ellipseRadius z ^ N := by
  calc
    _ = ‖z‖ * ∑ j ∈ Finset.range (N + 1),
        ‖z‖ ^ j * ‖1 - z‖ ^ (N - j) * (Nat.choose N j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_spectralTerm, pow_succ]
      ring
    _ = ‖z‖ * ellipseRadius z ^ N := by rw [← add_pow]; rfl

theorem norm_spectralTerm_le {N j : ℕ} (hj : j ∈ Finset.range (N + 1))
    (z : ℂ) {R : ℝ} (hR : ellipseRadius z ≤ R) :
    ‖spectralTerm N j z‖ ≤ ‖z‖ * R ^ N := by
  have ht : ‖spectralTerm N j z‖ ≤
      ∑ k ∈ Finset.range (N + 1), ‖spectralTerm N k z‖ :=
    Finset.single_le_sum
      (fun k _ => norm_nonneg (spectralTerm N k z)) hj
  rw [sum_norm_spectralTerm] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  exact pow_le_pow_left₀ (by dsimp [ellipseRadius]; positivity) hR N

theorem spectralTerm_re_nonneg {z : ℂ} (hz : InUnitSegment z) (N j : ℕ) :
    0 ≤ (spectralTerm N j z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
  have ht : spectralTerm N j z =
      (((Nat.choose N j : ℝ) * z.re ^ (j + 1) *
        (1 - z.re) ^ (N - j) : ℝ) : ℂ) := by
    rw [he]
    simp only [spectralTerm]
    push_cast <;> rfl
  rw [ht, Complex.ofReal_re]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.2.1 _))
    (pow_nonneg (sub_nonneg.mpr hz.2.2) _)

def rowGenerating (u : ℕ → ℝ) (N : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (bernsteinWeight u N j : ℂ) * x ^ j

theorem norm_rowGenerating_le (u : ℕ → ℝ) (N : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖rowGenerating u N x‖ ≤ rowVariation u N := by
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), ‖(bernsteinWeight u N j : ℂ) * x ^ j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), |bernsteinWeight u N j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hp : ‖x‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg x) hx
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hp (abs_nonneg (bernsteinWeight u N j))
    _ = rowVariation u N := rfl

namespace ActualSpectralCalibration

variable {ι : Type*} (D : ActualSpectralCalibration ι)

theorem weight_hasSum (N j : ℕ) :
    HasSum (fun i => spectralTerm N j (D.node i)) (actualWeight N j : ℂ) := by
  exact bernsteinWeight_hasSum actualNormalizedMoment D.node D.power_sums N j

include D in
theorem variation_one_le (N : ℕ) : 1 ≤ actualVariation N :=
  one_le_rowVariation actualNormalizedMoment
    (actualNormalizedMoment_zero (ne_of_gt D.kappa_pos)) N

theorem variation_monotone : Monotone actualVariation :=
  rowVariation_monotone actualNormalizedMoment

theorem term_norm_summable {N j : ℕ} (hj : j ∈ Finset.range (N + 1)) :
    Summable (fun i => ‖spectralTerm N j (D.node i)‖) := by
  apply (D.norm_summable.mul_right (spectralRadius D.node ^ N)).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_spectralTerm_le hj (D.node i) (ellipseRadius_le_spectralRadius D.bounded i)

theorem variation_upper (N : ℕ) :
    actualVariation N ≤ (∑' i, ‖D.node i‖) * spectralRadius D.node ^ N := by
  classical
  have hs : HasSum
      (fun i => ∑ j ∈ Finset.range (N + 1), ‖spectralTerm N j (D.node i)‖)
      (∑ j ∈ Finset.range (N + 1), ∑' i, ‖spectralTerm N j (D.node i)‖) :=
    hasSum_sum (fun j hj => (D.term_norm_summable hj).hasSum)
  have hs' : HasSum (fun i => ‖D.node i‖ * ellipseRadius (D.node i) ^ N)
      (∑ j ∈ Finset.range (N + 1), ∑' i, ‖spectralTerm N j (D.node i)‖) := by
    simpa only [sum_norm_spectralTerm] using hs
  have hb : (∑ j ∈ Finset.range (N + 1), ∑' i, ‖spectralTerm N j (D.node i)‖) ≤
      (∑' i, ‖D.node i‖) * spectralRadius D.node ^ N := by
    apply hasSum_le _ hs' (D.norm_summable.hasSum.mul_right (spectralRadius D.node ^ N))
    intro i
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact pow_le_pow_left₀ (by dsimp [ellipseRadius]; positivity)
      (ellipseRadius_le_spectralRadius D.bounded i) N
  apply le_trans _ hb
  change
    (∑ j ∈ Finset.range (N + 1), |actualWeight N j|) ≤
      ∑ j ∈ Finset.range (N + 1), ∑' i, ‖spectralTerm N j (D.node i)‖
  apply Finset.sum_le_sum
  intro j hj
  have h := (D.weight_hasSum N j).norm_le_of_bounded
    (D.term_norm_summable hj).hasSum (fun i => le_rfl)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem total_norm_pos : 0 < ∑' i, ‖D.node i‖ := by
  have h : 1 ≤ ∑' i, ‖D.node i‖ := by
    simpa using D.mass_one.norm_le_of_bounded D.norm_summable.hasSum (fun i => le_rfl)
  exact zero_lt_one.trans_le h

include D in
theorem weights_nonneg_of_nativeRH (hRH : _root_.RiemannHypothesis)
    (N j : ℕ) : 0 ≤ actualWeight N j := by
  have hn := D.nodes_segment_iff_nativeRH.mpr hRH
  have hs : HasSum (fun i => (spectralTerm N j (D.node i)).re) (actualWeight N j) := by
    simpa using Complex.hasSum_re (D.weight_hasSum N j)
  rw [← hs.tsum_eq]
  exact tsum_nonneg (fun i => spectralTerm_re_nonneg (hn i) N j)

include D in
theorem variation_eq_one_of_nativeRH (hRH : _root_.RiemannHypothesis) (N : ℕ) :
    actualVariation N = 1 := by
  apply (rowVariation_eq_one_iff actualNormalizedMoment
    (actualNormalizedMoment_zero (ne_of_gt D.kappa_pos)) N).mpr
  exact fun j _ => D.weights_nonneg_of_nativeRH hRH N j

theorem variation_eq_one_of_radius_one (hR : spectralRadius D.node = 1) (N : ℕ) :
    actualVariation N = 1 :=
  D.variation_eq_one_of_nativeRH (D.radius_one_iff_nativeRH.mp hR) N

end ActualSpectralCalibration

end RH_HilbertLimit
