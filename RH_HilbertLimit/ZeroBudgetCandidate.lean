import RH_HilbertLimit.ActualCancellationWitness

/-!
# The explicit zero cancellation-budget candidate

This module names the data pair (0, 0), expands its first two cancellation
checks, and states the exact induction obligation for all-order admissibility.
The degree-zero row is normalized unconditionally, but that is not yet the
first cancellation check: cancellation at index zero uses the degree-one row.

The first check is exactly the interval condition on normalized moment one.
Given that interval condition, the second check is exactly three displayed
inequalities involving normalized moment two. No all-order sign assertion,
admissible witness, or finite Bool-checker acceptance is asserted here.

Source-reviewed candidate only. No Lean, Lake, native compiler, or CI was
executed while preparing this module.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RH_HilbertLimit

/-- The concrete finite data requested for the zero-budget attempt. -/
def zeroBudgetCandidate : CancellationBudget := ⟨0, 0⟩

/-- The normalization is already unconditional in the actual-xi construction. -/
theorem actualNormalizedMoment_zero_unconditional :
    actualNormalizedMoment 0 = 1 :=
  actualNormalizedMoment_zero (ne_of_gt actualKappa_pos)

/-- The sole degree-zero weight is one. This does not evaluate cancellation. -/
theorem actualWeight_zero_zero : actualWeight 0 0 = 1 := by
  change bernsteinWeight actualNormalizedMoment 0 0 = 1
  rw [bernsteinWeight_zero_zero, actualNormalizedMoment_zero_unconditional]

/-- Degree-zero variation is one independently of RH. -/
theorem actualVariation_zero : actualVariation 0 = 1 := by
  change rowVariation actualNormalizedMoment 0 = 1
  rw [rowVariation_zero, actualNormalizedMoment_zero_unconditional, abs_one]

theorem actualWeight_one_zero :
    actualWeight 1 0 = 1 - actualNormalizedMoment 1 := by
  norm_num [actualWeight, bernsteinWeight, Finset.sum_range_succ,
    actualNormalizedMoment_zero_unconditional] <;> ring

theorem actualWeight_one_one :
    actualWeight 1 1 = actualNormalizedMoment 1 := by
  simp [actualWeight, bernsteinWeight]

/-- Exact first-row variation; no sign of moment one is assumed. -/
theorem actualVariation_one_eq :
    actualVariation 1 =
      |1 - actualNormalizedMoment 1| + |actualNormalizedMoment 1| := by
  change (∑ j ∈ Finset.range (1 + 1), |actualWeight 1 j|) = _
  simp [Finset.sum_range_succ, actualWeight_one_zero, actualWeight_one_one]

/-- Vanishing cancellation is exactly equality of two successive variations. -/
theorem rowCancellation_eq_zero_iff_rowVariation_eq
    (u : ℕ → ℝ) (n : ℕ) :
    rowCancellation u n = 0 ↔ rowVariation u (n + 1) = rowVariation u n := by
  have hfactor : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [rowCancellation_eq]
  simp only [mul_eq_zero, hfactor, false_or, sub_eq_zero]

/-- The actual first cancellation check, as a literal expression in moment one. -/
theorem actual_rowCancellation_zero_eq :
    rowCancellation actualNormalizedMoment 0 =
      |1 - actualNormalizedMoment 1| + |actualNormalizedMoment 1| - 1 := by
  calc
    rowCancellation actualNormalizedMoment 0 =
        rowVariation actualNormalizedMoment 1 - rowVariation actualNormalizedMoment 0 := by
      simpa only [Nat.cast_zero, zero_add, one_mul] using
        rowCancellation_eq actualNormalizedMoment 0
    _ = _ := by
      change actualVariation 1 - actualVariation 0 = _
      rw [actualVariation_one_eq, actualVariation_zero]

/-- Checking cancellation at zero is exactly checking this moment interval. -/
theorem actual_rowCancellation_zero_eq_zero_iff :
    rowCancellation actualNormalizedMoment 0 = 0 ↔
      0 ≤ actualNormalizedMoment 1 ∧ actualNormalizedMoment 1 ≤ 1 := by
  constructor
  · intro h
    rw [actual_rowCancellation_zero_eq] at h
    constructor
    · have ha := le_abs_self (1 - actualNormalizedMoment 1)
      have hb := neg_le_abs (actualNormalizedMoment 1)
      linarith
    · have ha := neg_le_abs (1 - actualNormalizedMoment 1)
      have hb := le_abs_self (actualNormalizedMoment 1)
      linarith
  · rintro ⟨hlo, hhi⟩
    rw [actual_rowCancellation_zero_eq, abs_of_nonneg (sub_nonneg.mpr hhi),
      abs_of_nonneg hlo]
    ring

theorem actualVariation_one_eq_one_iff :
    actualVariation 1 = 1 ↔
      0 ≤ actualNormalizedMoment 1 ∧ actualNormalizedMoment 1 ≤ 1 := by
  have hfirst : rowCancellation actualNormalizedMoment 0 = 0 ↔
      actualVariation 1 = 1 := by
    rw [rowCancellation_eq_zero_iff_rowVariation_eq]
    change actualVariation 1 = actualVariation 0 ↔ actualVariation 1 = 1
    rw [actualVariation_zero]
  exact hfirst.symm.trans actual_rowCancellation_zero_eq_zero_iff

theorem actualWeight_two_zero :
    actualWeight 2 0 =
      1 - 2 * actualNormalizedMoment 1 + actualNormalizedMoment 2 := by
  norm_num [actualWeight, bernsteinWeight, Finset.sum_range_succ,
    actualNormalizedMoment_zero_unconditional] <;> ring

theorem actualWeight_two_one :
    actualWeight 2 1 = 2 * (actualNormalizedMoment 1 - actualNormalizedMoment 2) := by
  norm_num [actualWeight, bernsteinWeight, Finset.sum_range_succ] <;> ring

theorem actualWeight_two_two :
    actualWeight 2 2 = actualNormalizedMoment 2 := by
  simp [actualWeight, bernsteinWeight]

/-- Exact second-row positivity, reduced to the next normalized moment. -/
theorem actualVariation_two_eq_one_iff :
    actualVariation 2 = 1 ↔
      0 ≤ actualNormalizedMoment 2 ∧
      actualNormalizedMoment 2 ≤ actualNormalizedMoment 1 ∧
      2 * actualNormalizedMoment 1 ≤ 1 + actualNormalizedMoment 2 := by
  have hrow := rowVariation_eq_one_iff actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional 2
  constructor
  · intro hV
    have hsign := hrow.mp hV
    have h0 : 0 ≤ actualWeight 2 0 := hsign 0 (by simp)
    have h1 : 0 ≤ actualWeight 2 1 := hsign 1 (by simp)
    have h2 : 0 ≤ actualWeight 2 2 := hsign 2 (by simp)
    rw [actualWeight_two_zero] at h0
    rw [actualWeight_two_one] at h1
    rw [actualWeight_two_two] at h2
    exact ⟨h2, by linarith, by linarith⟩
  · rintro ⟨hlo, hhi, hleft⟩
    apply hrow.mpr
    intro j hj
    change 0 ≤ actualWeight 2 j
    have hjlt := Finset.mem_range.mp hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with rfl | rfl | rfl
    · rw [actualWeight_two_zero]
      linarith
    · rw [actualWeight_two_one]
      linarith
    · rw [actualWeight_two_two]
      exact hlo

/-- Once the first check holds, this is the exact next cancellation check. -/
theorem actual_rowCancellation_one_eq_zero_iff
    (hfirst : 0 ≤ actualNormalizedMoment 1 ∧ actualNormalizedMoment 1 ≤ 1) :
    rowCancellation actualNormalizedMoment 1 = 0 ↔
      0 ≤ actualNormalizedMoment 2 ∧
      actualNormalizedMoment 2 ≤ actualNormalizedMoment 1 ∧
      2 * actualNormalizedMoment 1 ≤ 1 + actualNormalizedMoment 2 := by
  have hV1 := actualVariation_one_eq_one_iff.mpr hfirst
  rw [rowCancellation_eq_zero_iff_rowVariation_eq]
  change actualVariation 2 = actualVariation 1 ↔ _
  rw [hV1]
  exact actualVariation_two_eq_one_iff

/-- The data pair (0,0) is admissible exactly when every cancellation vanishes. -/
theorem zeroBudgetCandidate_admissible_iff_all_cancellation_zero :
    zeroBudgetCandidate.Admissible ↔
      ∀ n : ℕ, rowCancellation actualNormalizedMoment n = 0 := by
  constructor
  · intro h n
    have hn : rowCancellation actualNormalizedMoment n ≤
        ((0 : ℕ) : ℝ) * actualVariation n := h n (Nat.zero_le n)
    have hle : rowCancellation actualNormalizedMoment n ≤ 0 := by
      simpa only [Nat.cast_zero, zero_mul] using hn
    exact le_antisymm hle (rowCancellation_nonneg actualNormalizedMoment n)
  · intro h n _hn
    change rowCancellation actualNormalizedMoment n ≤
      ((0 : ℕ) : ℝ) * actualVariation n
    rw [h n]
    simp

/-- The exact logical status of the named candidate; no admissibility is asserted. -/
theorem zeroBudgetCandidate_admissible_iff_nativeRH :
    zeroBudgetCandidate.Admissible ↔ _root_.RiemannHypothesis := by
  constructor
  · exact nativeRH_of_admissible_cancellationBudget zeroBudgetCandidate
  · intro hRH
    exact zero_cancellationBudget_admissible_of_nativeRH hRH

/-- A first check plus this universal propagation law would prove admissibility.
The propagation law is an explicit remaining mathematical obligation, not a
finite check or a theorem supplied by this module. -/
theorem zeroBudgetCandidate_admissible_iff_seed_and_propagation :
    zeroBudgetCandidate.Admissible ↔
      rowCancellation actualNormalizedMoment 0 = 0 ∧
      ∀ n : ℕ, rowCancellation actualNormalizedMoment n = 0 →
        rowCancellation actualNormalizedMoment (n + 1) = 0 := by
  rw [zeroBudgetCandidate_admissible_iff_all_cancellation_zero]
  constructor
  · intro h
    exact ⟨h 0, fun n _hn => h (n + 1)⟩
  · rintro ⟨hzero, hstep⟩ n
    induction n with
    | zero => exact hzero
    | succ n ih => exact hstep n ih

end RH_HilbertLimit
