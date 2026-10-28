import RH_HilbertLimit.TwoRoutes.PositiveMomentBridge
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The monomial limit of the literal Bernstein row measures

An exact shifted-row identity reduces degree `k + 1` to degrees at most `k`.
This proves moment convergence for every real sequence, without a positivity,
representing-measure, or RH hypothesis. Prepared without running Lean or Lake.
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators Topology

namespace RH_HilbertLimit.TwoRoutes

def shiftedMoments (u : ℕ → ℝ) (n : ℕ) : ℝ := u (n + 1)

theorem bernsteinWeight_shift (u : ℕ → ℝ) (N j : ℕ) :
    ((j : ℝ) + 1) * bernsteinWeight u (N + 1) (j + 1) =
      ((N : ℝ) + 1) * bernsteinWeight (shiftedMoments u) N j := by
  have hchooseNat :
      (j + 1) * Nat.choose (N + 1) (j + 1) = (N + 1) * Nat.choose N j := by
    simpa only [Nat.mul_comm] using (Nat.add_one_mul_choose_eq N j).symm
  have hchoose :
      ((j : ℝ) + 1) * (Nat.choose (N + 1) (j + 1) : ℝ) =
        ((N : ℝ) + 1) * (Nat.choose N j : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ℝ)) hchooseNat
  have hsub : N + 1 - (j + 1) = N - j := by omega
  have hsum :
      (∑ r ∈ Finset.range (N - j + 1),
        (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + 1 + r)) =
      ∑ r ∈ Finset.range (N - j + 1),
        (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * shiftedMoments u (j + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [shiftedMoments, show j + 1 + r = j + r + 1 by omega]
  simp only [bernsteinWeight, hsub]
  rw [hsum, ← mul_assoc, hchoose, mul_assoc]

theorem bernsteinAverage_monomial_succ (u : ℕ → ℝ) (N k : ℕ) :
    bernsteinAverage u (N + 1) (fun q => q ^ (k + 1)) =
      ∑ j ∈ Finset.range (N + 1), bernsteinWeight (shiftedMoments u) N j *
        (((j : ℝ) + 1) / ((N : ℝ) + 1)) ^ k := by
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  unfold bernsteinAverage
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_div, zero_pow (Nat.succ_ne_zero k), mul_zero,
    add_zero, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hlinear : bernsteinWeight u (N + 1) (j + 1) *
      (((j : ℝ) + 1) / ((N : ℝ) + 1)) =
      bernsteinWeight (shiftedMoments u) N j := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hN).mpr
    simpa only [mul_comm] using bernsteinWeight_shift u N j
  rw [pow_succ]
  calc
    _ = (bernsteinWeight u (N + 1) (j + 1) *
          (((j : ℝ) + 1) / ((N : ℝ) + 1))) *
          (((j : ℝ) + 1) / ((N : ℝ) + 1)) ^ k := by ring
    _ = _ := by rw [hlinear]

def bernsteinMomentTransition (N k i : ℕ) : ℝ :=
  (Nat.choose k i : ℝ) * ((N : ℝ) / ((N : ℝ) + 1)) ^ i *
    (1 / ((N : ℝ) + 1)) ^ (k - i)

theorem bernsteinGrid_affine_pow (N j k : ℕ) (hN : N ≠ 0) :
    (((j : ℝ) + 1) / ((N : ℝ) + 1)) ^ k =
      ∑ i ∈ Finset.range (k + 1),
        bernsteinMomentTransition N k i * ((j : ℝ) / N) ^ i := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNs : (N : ℝ) + 1 ≠ 0 := by positivity
  have haffine : ((j : ℝ) + 1) / ((N : ℝ) + 1) =
      ((j : ℝ) / N) * ((N : ℝ) / ((N : ℝ) + 1)) +
        1 / ((N : ℝ) + 1) := by
    field_simp [hNr, hNs]
    <;> ring
  rw [haffine, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [bernsteinMomentTransition, mul_pow]
  ring

theorem bernsteinAverage_monomial_recursion (u : ℕ → ℝ) (N k : ℕ)
    (hN : N ≠ 0) :
    bernsteinAverage u (N + 1) (fun q => q ^ (k + 1)) =
      ∑ i ∈ Finset.range (k + 1), bernsteinMomentTransition N k i *
        bernsteinAverage (shiftedMoments u) N (fun q => q ^ i) := by
  rw [bernsteinAverage_monomial_succ]
  simp_rw [bernsteinGrid_affine_pow N _ k hN, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [bernsteinAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bernsteinMomentTransition_tendsto (k i : ℕ) (hi : i ≤ k) :
    Tendsto (fun N => bernsteinMomentTransition N k i) atTop
      (𝓝 (if i = k then (1 : ℝ) else 0)) := by
  have h := ((tendsto_const_nhds (x := (Nat.choose k i : ℝ))).mul
    ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow i)).mul
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (k - i))
  by_cases hik : i = k
  · subst i
    simpa [bernsteinMomentTransition] using h
  · have hsub : k - i ≠ 0 := by omega
    simpa [bernsteinMomentTransition, hik, zero_pow hsub] using h

/-- The atom measures on the finite Bernstein grids have the required moment
limits. Positivity is only needed later, to construct a positive limit measure. -/
theorem bernsteinAverage_monomial_tendsto (u : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N => bernsteinAverage u N (fun q => q ^ k))
      atTop (𝓝 (u k)) := by
  induction k using Nat.strong_induction_on generalizing u with
  | h k ih =>
    cases k with
    | zero =>
      have heq : (fun N => bernsteinAverage u N (fun q => q ^ 0)) =
          fun _ : ℕ => u 0 := by
        funext N
        simp only [bernsteinAverage, pow_zero, mul_one, sum_bernsteinWeight_eq]
      rw [heq]
      exact tendsto_const_nhds
    | succ k =>
      apply (tendsto_add_atTop_iff_nat 1).mp
      have hsum : Tendsto
          (fun N => ∑ i ∈ Finset.range (k + 1), bernsteinMomentTransition N k i *
            bernsteinAverage (shiftedMoments u) N (fun q => q ^ i))
          atTop (𝓝 (∑ i ∈ Finset.range (k + 1),
            (if i = k then (1 : ℝ) else 0) * shiftedMoments u i)) := by
        apply tendsto_finsetSum (Finset.range (k + 1))
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (bernsteinMomentTransition_tendsto k i hik).mul
          (ih i (by omega) (shiftedMoments u))
      have hlimit : (∑ i ∈ Finset.range (k + 1),
          (if i = k then (1 : ℝ) else 0) * shiftedMoments u i) = u (k + 1) := by
        simp [ite_mul, shiftedMoments]
      rw [hlimit] at hsum
      apply hsum.congr'
      filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
      exact (bernsteinAverage_monomial_recursion u N k (by omega)).symm

end RH_HilbertLimit.TwoRoutes
