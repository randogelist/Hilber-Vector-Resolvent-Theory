import RH_HilbertLimit.Bernstein

/-!
# Adjacent cancellation in Bernstein rows

The cancellation quantity is the literal finite sum of triangle-inequality
defects between adjacent entries of the next row. Its equality with the
scaled variation increment is proved from the existing coarsening identity.

This module contains finite row identities and a local telescoping bound.
It does not define or assert completeness of a finite raw-witness checker.
Source candidate prepared without running Lean, Lake, or CI.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit

/-- The literal weighted triangle defect of two adjacent next-row entries. -/
def cancellationDefect (u : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ((n : ℝ) + 1 - j) * |bernsteinWeight u (n + 1) j| +
    ((j : ℝ) + 1) * |bernsteinWeight u (n + 1) (j + 1)| -
    |((n : ℝ) + 1 - j) * bernsteinWeight u (n + 1) j +
      ((j : ℝ) + 1) * bernsteinWeight u (n + 1) (j + 1)|

/-- The sum of the adjacent weighted cancellation defects in one refinement. -/
def rowCancellation (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), cancellationDefect u n j

/-- Coarsening with the positive common denominator cleared. -/
theorem bernsteinWeight_coarsening_scaled (u : ℕ → ℝ) (n j : ℕ)
    (hj : j ≤ n) :
    ((n : ℝ) + 1) * bernsteinWeight u n j =
      ((n : ℝ) + 1 - j) * bernsteinWeight u (n + 1) j +
        ((j : ℝ) + 1) * bernsteinWeight u (n + 1) (j + 1) := by
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  have hquot : bernsteinWeight u n j =
      (((n : ℝ) + 1 - j) * bernsteinWeight u (n + 1) j +
        ((j : ℝ) + 1) * bernsteinWeight u (n + 1) (j + 1)) /
        ((n : ℝ) + 1) := by
    rw [bernsteinWeight_coarsening u n j hj]
    ring
  exact (mul_comm ((n : ℝ) + 1) (bernsteinWeight u n j)).trans
    ((eq_div_iff hden).mp hquot)

/-- Each in-range adjacent cancellation defect is nonnegative. -/
theorem cancellationDefect_nonneg (u : ℕ → ℝ) (n j : ℕ)
    (hj : j ≤ n) : 0 ≤ cancellationDefect u n j := by
  have hjR : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj
  have ha : 0 ≤ (n : ℝ) + 1 - j := by linarith
  have hb : 0 ≤ (j : ℝ) + 1 := by positivity
  unfold cancellationDefect
  apply sub_nonneg.mpr
  calc
    _ ≤ |((n : ℝ) + 1 - j) * bernsteinWeight u (n + 1) j| +
        |((j : ℝ) + 1) * bernsteinWeight u (n + 1) (j + 1)| :=
      abs_add_le _ _
    _ = _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

private theorem sum_coarsening_numerators (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (((n : ℝ) + 1 - j) * f j + ((j : ℝ) + 1) * f (j + 1))) =
      ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 2), f j := by
  let A : ℕ → ℝ := fun j => ((n : ℝ) + 1 - j) * f j
  let B : ℕ → ℝ := fun j => (j : ℝ) * f j
  have hA : (∑ j ∈ Finset.range (n + 1), A j) =
      ∑ j ∈ Finset.range (n + 2), A j := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      Finset.sum_range_succ A (n + 1)]
    simp only [A, Nat.cast_add, Nat.cast_one, sub_self, zero_mul, add_zero]
  have hB : (∑ j ∈ Finset.range (n + 1), B (j + 1)) =
      ∑ j ∈ Finset.range (n + 2), B j := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      Finset.sum_range_succ' B (n + 1)]
    simp only [B, Nat.cast_zero, zero_mul, add_zero, zero_add]
  calc
    _ = (∑ j ∈ Finset.range (n + 1), A j) +
        ∑ j ∈ Finset.range (n + 1), B (j + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [A, B, Nat.cast_add, Nat.cast_one]
    _ = (∑ j ∈ Finset.range (n + 2), A j) +
        ∑ j ∈ Finset.range (n + 2), B j := by rw [hA, hB]
    _ = ∑ j ∈ Finset.range (n + 2), (A j + B j) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.range (n + 2), ((n : ℝ) + 1) * f j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [A, B]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- Exact adjacent cancellation equals the scaled total-variation increment. -/
theorem rowCancellation_eq (u : ℕ → ℝ) (n : ℕ) :
    rowCancellation u n =
      ((n : ℝ) + 1) * (rowVariation u (n + 1) - rowVariation u n) := by
  have hden : 0 ≤ (n : ℝ) + 1 := by positivity
  have hdef (j : ℕ) (hj : j ≤ n) :
      cancellationDefect u n j =
        ((n : ℝ) + 1 - j) * |bernsteinWeight u (n + 1) j| +
          ((j : ℝ) + 1) * |bernsteinWeight u (n + 1) (j + 1)| -
          ((n : ℝ) + 1) * |bernsteinWeight u n j| := by
    unfold cancellationDefect
    rw [← bernsteinWeight_coarsening_scaled u n j hj, abs_mul,
      abs_of_nonneg hden]
  unfold rowCancellation
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        (((n : ℝ) + 1 - j) * |bernsteinWeight u (n + 1) j| +
          ((j : ℝ) + 1) * |bernsteinWeight u (n + 1) (j + 1)| -
          ((n : ℝ) + 1) * |bernsteinWeight u n j|) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      exact hdef j hjn
    _ = (∑ j ∈ Finset.range (n + 1),
        (((n : ℝ) + 1 - j) * |bernsteinWeight u (n + 1) j| +
          ((j : ℝ) + 1) * |bernsteinWeight u (n + 1) (j + 1)|)) -
        ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1),
          |bernsteinWeight u n j| := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ((n : ℝ) + 1) *
        (∑ j ∈ Finset.range (n + 2), |bernsteinWeight u (n + 1) j|) -
        ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1),
          |bernsteinWeight u n j| := by
      rw [sum_coarsening_numerators (fun j => |bernsteinWeight u (n + 1) j|) n]
    _ = _ := by
      change ((n : ℝ) + 1) * rowVariation u (n + 1) -
        ((n : ℝ) + 1) * rowVariation u n =
        ((n : ℝ) + 1) * (rowVariation u (n + 1) - rowVariation u n)
      ring

theorem rowCancellation_nonneg (u : ℕ → ℝ) (n : ℕ) :
    0 ≤ rowCancellation u n := by
  unfold rowCancellation
  apply Finset.sum_nonneg
  intro j hj
  have hjn : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  exact cancellationDefect_nonneg u n j hjn

theorem rowCancellation_eq_zero_of_rowVariation_eq (u : ℕ → ℝ) (n : ℕ)
    (h : rowVariation u (n + 1) = rowVariation u n) :
    rowCancellation u n = 0 := by
  rw [rowCancellation_eq, h, sub_self, mul_zero]

theorem rowCancellation_eq_zero_of_rowVariation_constant (u : ℕ → ℝ) (c : ℝ)
    (h : ∀ n : ℕ, rowVariation u n = c) (n : ℕ) :
    rowCancellation u n = 0 := by
  apply rowCancellation_eq_zero_of_rowVariation_eq
  exact (h (n + 1)).trans (h n).symm

private theorem sum_forward_differences (H : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (H (j + 1) - H j)) = H n - H 0 := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A local inequality with a telescoping auxiliary term gives the row budget. -/
theorem rowCancellation_le_of_local_flux (u : ℕ → ℝ) (n : ℕ) (K : ℝ)
    (H : ℕ → ℝ)
    (hlocal : ∀ j : ℕ, j ≤ n →
      cancellationDefect u n j ≤
        K * |bernsteinWeight u n j| + (H (j + 1) - H j))
    (hboundary : H (n + 1) ≤ H 0) :
    rowCancellation u n ≤ K * rowVariation u n := by
  calc
    rowCancellation u n ≤ ∑ j ∈ Finset.range (n + 1),
        (K * |bernsteinWeight u n j| + (H (j + 1) - H j)) := by
      unfold rowCancellation
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      exact hlocal j hjn
    _ = K * rowVariation u n + (H (n + 1) - H 0) := by
      rw [rowVariation, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_forward_differences]
    _ ≤ K * rowVariation u n := by linarith

end RH_HilbertLimit
