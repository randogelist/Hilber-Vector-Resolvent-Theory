import RH_HilbertLimit.Spectral
import RH_HilbertLimit.SpectralTail
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Exact spectral generating series and finite-complement remainder

UNCOMPILED CANDIDATE for the user's native Lean 4.33.0 target.
No Lean, Lake, native compiler, or CI process was run to prepare this file.

The generating identity is derived from the existing power-sum calibration
and the finite binomial formula.  It is not an additional analytic premise.
It holds for every complex phase; the unit-disk hypothesis is needed only
when the ellipse-radius localization is used to bound the remainder.

The remainder is an absolutely convergent sum over the complement of a
finite set.  Its estimate accepts a direct affine-factor bound, so a later
finite-head construction may supply its own strictly subdominant rate.
Repeated nodes remain distinct indices at this stage.  No finite-support
assumption, positivity assumption, or RH assumption is introduced.

API references inspected at mathlib tag `v4.33.0`:
* `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`: `hasSum_sum`.
* `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean`: `HasSum.mul_right`.
* `Mathlib/Topology/Algebra/InfiniteSum/Group.lean`:
  `Summable.subtype`, `Summable.sum_add_tsum_subtype_compl`.
* `Mathlib/Analysis/Normed/Group/InfiniteSum.lean`:
  `Summable.of_norm_bounded`, `tsum_of_norm_bounded`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit

/-- The finite binomial identity at one spectral node. -/
theorem sum_spectralTerm_mul_pow (N : ℕ) (z x : ℂ) :
    (∑ j ∈ Finset.range (N + 1), spectralTerm N j z * x ^ j) =
      z * (1 + (x - 1) * z) ^ N := by
  calc
    _ = z * ∑ j ∈ Finset.range (N + 1),
        (z * x) ^ j * (1 - z) ^ (N - j) * (Nat.choose N j : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [spectralTerm, mul_pow, pow_succ]
      ring
    _ = z * (z * x + (1 - z)) ^ N := by rw [← add_pow]
    _ = z * (1 + (x - 1) * z) ^ N := by
      have hbase : z * x + (1 - z) = 1 + (x - 1) * z := by ring
      rw [hbase]

/-- All complex phases are allowed.  Only finitely many calibrated weight
series are added, so no infinite rearrangement is assumed. -/
theorem rowGenerating_hasSum {ι : Type*} (u : ℕ → ℝ) (q : ι → ℂ)
    (hpower : ∀ n : ℕ, HasSum (fun i => q i ^ (n + 1)) (u n : ℂ))
    (N : ℕ) (x : ℂ) :
    HasSum (fun i => q i * (1 + (x - 1) * q i) ^ N)
      (rowGenerating u N x) := by
  classical
  have hs : HasSum
      (fun i => ∑ j ∈ Finset.range (N + 1), spectralTerm N j (q i) * x ^ j)
      (rowGenerating u N x) := by
    unfold rowGenerating
    apply hasSum_sum
    intro j hj
    simpa only [spectralTerm] using
      (bernsteinWeight_hasSum u q hpower N j).mul_right (x ^ j)
  simpa only [sum_spectralTerm_mul_pow] using hs

theorem rowGenerating_eq_tsum {ι : Type*} (u : ℕ → ℝ) (q : ι → ℂ)
    (hpower : ∀ n : ℕ, HasSum (fun i => q i ^ (n + 1)) (u n : ℂ))
    (N : ℕ) (x : ℂ) :
    rowGenerating u N x = ∑' i, q i * (1 + (x - 1) * q i) ^ N :=
  (rowGenerating_hasSum u q hpower N x).tsum_eq.symm

/-- The actual infinite complement, with repeated nodes kept as separate
indices.  The associated lemmas establish summability before it is used. -/
def spectralRemainder {ι : Type*} (q : ι → ℂ) (s : Finset ι)
    (x : ℂ) (N : ℕ) : ℂ :=
  ∑' i : {i : ι // i ∉ s}, q i * (1 + (x - 1) * q i) ^ N

/-- Exact finite-head plus infinite-complement splitting. -/
theorem rowGenerating_eq_sum_add_remainder {ι : Type*}
    (u : ℕ → ℝ) (q : ι → ℂ)
    (hpower : ∀ n : ℕ, HasSum (fun i => q i ^ (n + 1)) (u n : ℂ))
    (s : Finset ι) (N : ℕ) (x : ℂ) :
    rowGenerating u N x =
      (∑ i ∈ s, q i * (1 + (x - 1) * q i) ^ N) +
        spectralRemainder q s x N := by
  classical
  have hs := rowGenerating_hasSum u q hpower N x
  calc
    _ = ∑' i, q i * (1 + (x - 1) * q i) ^ N := hs.tsum_eq.symm
    _ = _ := (hs.summable.sum_add_tsum_subtype_compl s).symm

/-- Pointwise domination for a phase whose affine factor has norm at most r. -/
theorem norm_node_affine_pow_le (z x : ℂ) (r : ℝ)
    (hfactor : ‖1 + (x - 1) * z‖ ≤ r) (N : ℕ) :
    ‖z * (1 + (x - 1) * z) ^ N‖ ≤ ‖z‖ * r ^ N := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hfactor N) (norm_nonneg z)

/-- The direct affine-factor hypothesis proves convergence of the complement,
independently of the calibrated generating identity. -/
theorem spectralRemainder_summable {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (s : Finset ι) (x : ℂ) (r : ℝ)
    (hfactor : ∀ i, i ∉ s → ‖1 + (x - 1) * q i‖ ≤ r) (N : ℕ) :
    Summable (fun i : {i : ι // i ∉ s} =>
      q i * (1 + (x - 1) * q i) ^ N) := by
  have hsub : Summable (fun i : {i : ι // i ∉ s} => ‖q i‖) :=
    hq.subtype (fun i => i ∉ s)
  apply (hsub.mul_right (r ^ N)).of_norm_bounded
  intro i
  exact norm_node_affine_pow_le (q i) x r (hfactor i i.property) N

/-- The same comparison also proves absolute summability explicitly. -/
theorem spectralRemainder_norm_summable {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (s : Finset ι) (x : ℂ) (r : ℝ)
    (hfactor : ∀ i, i ∉ s → ‖1 + (x - 1) * q i‖ ≤ r) (N : ℕ) :
    Summable (fun i : {i : ι // i ∉ s} =>
      ‖q i * (1 + (x - 1) * q i) ^ N‖) := by
  have hsub : Summable (fun i : {i : ι // i ∉ s} => ‖q i‖) :=
    hq.subtype (fun i => i ∉ s)
  apply (hsub.mul_right (r ^ N)).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_node_affine_pow_le (q i) x r (hfactor i i.property) N

/-- The sharper bound uses only the norm mass of the complement. -/
theorem norm_spectralRemainder_le_tailMass {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (s : Finset ι) (x : ℂ) (r : ℝ)
    (hfactor : ∀ i, i ∉ s → ‖1 + (x - 1) * q i‖ ≤ r) (N : ℕ) :
    ‖spectralRemainder q s x N‖ ≤
      (∑' i : {i : ι // i ∉ s}, ‖q i‖) * r ^ N := by
  have hsub : Summable (fun i : {i : ι // i ∉ s} => ‖q i‖) :=
    hq.subtype (fun i => i ∉ s)
  exact tsum_of_norm_bounded (hsub.hasSum.mul_right (r ^ N))
    (fun i => norm_node_affine_pow_le (q i) x r (hfactor i i.property) N)

/-- A uniform constant independent of the finite set.  This form can be
supplied directly to the tail field of `DominantTailData`. -/
theorem norm_spectralRemainder_le {ι : Type*} (q : ι → ℂ)
    (hq : Summable (fun i => ‖q i‖)) (s : Finset ι) (x : ℂ) (r : ℝ)
    (hr : 0 ≤ r)
    (hfactor : ∀ i, i ∉ s → ‖1 + (x - 1) * q i‖ ≤ r) (N : ℕ) :
    ‖spectralRemainder q s x N‖ ≤ (∑' i, ‖q i‖) * r ^ N := by
  classical
  have hmass : (∑' i : {i : ι // i ∉ s}, ‖q i‖) ≤ ∑' i, ‖q i‖ := by
    rw [← hq.sum_add_tsum_subtype_compl s]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => norm_nonneg (q i)))
  exact (norm_spectralRemainder_le_tailMass q hq s x r hfactor N).trans
    (mul_le_mul_of_nonneg_right hmass (pow_nonneg hr N))

namespace ActualSpectralCalibration

variable {ι : Type*} (D : ActualSpectralCalibration ι)

/-- The actual row identity is derived from the supplied calibration fields. -/
theorem rowGenerating_hasSum (N : ℕ) (x : ℂ) :
    HasSum (fun i => D.node i * (1 + (x - 1) * D.node i) ^ N)
      (rowGenerating actualNormalizedMoment N x) :=
  RH_HilbertLimit.rowGenerating_hasSum actualNormalizedMoment D.node D.power_sums N x

theorem rowGenerating_eq_tsum (N : ℕ) (x : ℂ) :
    rowGenerating actualNormalizedMoment N x =
      ∑' i, D.node i * (1 + (x - 1) * D.node i) ^ N :=
  (D.rowGenerating_hasSum N x).tsum_eq.symm

theorem rowGenerating_eq_sum_add_remainder (s : Finset ι) (N : ℕ) (x : ℂ) :
    rowGenerating actualNormalizedMoment N x =
      (∑ i ∈ s, D.node i * (1 + (x - 1) * D.node i) ^ N) +
        spectralRemainder D.node s x N :=
  RH_HilbertLimit.rowGenerating_eq_sum_add_remainder
    actualNormalizedMoment D.node D.power_sums s N x

theorem norm_remainder_le (s : Finset ι) (x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hfactor : ∀ i, i ∉ s → ‖1 + (x - 1) * D.node i‖ ≤ r) (N : ℕ) :
    ‖spectralRemainder D.node s x N‖ ≤ (∑' i, ‖D.node i‖) * r ^ N :=
  norm_spectralRemainder_le D.node D.norm_summable s x r hr hfactor N

/-- One finite set and one rate work simultaneously for every phase in the
closed unit disk and every natural degree.  The finite head still needs
grouping and separation of its dominant rates. -/
theorem exists_uniform_finite_remainder_bound (hR : 1 < spectralRadius D.node) :
    ∃ r : ℝ, 1 < r ∧ r < spectralRadius D.node ∧
      ∃ s : Finset ι, ∀ x : ℂ, ‖x‖ ≤ 1 → ∀ N : ℕ,
        ‖spectralRemainder D.node s x N‖ ≤ (∑' i, ‖D.node i‖) * r ^ N := by
  obtain ⟨r, hr, hrR, s, hs⟩ := D.finite_tail_below_radius hR
  refine ⟨r, hr, hrR, s, ?_⟩
  intro x hx N
  apply D.norm_remainder_le s x r (zero_le_one.trans hr.le) _ N
  intro i hi
  exact (norm_affine_le_ellipseRadius (D.node i) x hx).trans (hs i hi).le

end ActualSpectralCalibration

end RH_HilbertLimit
