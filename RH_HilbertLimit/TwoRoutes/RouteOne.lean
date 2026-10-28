import RH_HilbertLimit.ZeroBudgetCandidate

/-!
# First route from the zero-budget hypothesis to actual RH

`H00` is exactly semantic admissibility of the existing finite data pair `(0, 0)`.
The finite identities below derive constant variation and row positivity directly
from `H00`, before any invocation of an RH closure theorem.

The first RH endpoint then uses the existing constructed actual spectral closure.
No admissibility proof, finite checker or accepted certificate is asserted here.

Source prepared without local Lean, Lake, compiler, axiom-audit or CI execution.
The new declarations require the user's native compilation and axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit.TwoRoutes

/-- The exact common hypothesis for the two constructions. -/
def H00 : Prop := zeroBudgetCandidate.Admissible

/-- Expand the semantic zero budget without using any RH implication. -/
theorem H00_iff_all_cancellation_zero :
    H00 ↔ ∀ n : ℕ, rowCancellation actualNormalizedMoment n = 0 := by
  exact zeroBudgetCandidate_admissible_iff_all_cancellation_zero

theorem actual_cancellation_zero_of_H00 (h : H00) (n : ℕ) :
    rowCancellation actualNormalizedMoment n = 0 :=
  H00_iff_all_cancellation_zero.mp h n

/-- The cancellation identity makes every successive variation equal. -/
theorem actual_variation_succ_eq_of_H00 (h : H00) (n : ℕ) :
    actualVariation (n + 1) = actualVariation n := by
  exact (rowCancellation_eq_zero_iff_rowVariation_eq
    actualNormalizedMoment n).mp (actual_cancellation_zero_of_H00 h n)

/-- Constant variation follows by induction from the unconditional degree-zero row. -/
theorem actual_variation_one_of_H00 (h : H00) (n : ℕ) :
    actualVariation n = 1 := by
  induction n with
  | zero => exact actualVariation_zero
  | succ n ih =>
      exact (actual_variation_succ_eq_of_H00 h n).trans ih

theorem H00_of_all_variation_one (h : ∀ n : ℕ, actualVariation n = 1) :
    H00 := by
  apply H00_iff_all_cancellation_zero.mpr
  intro n
  apply rowCancellation_eq_zero_of_rowVariation_eq
  exact (h (n + 1)).trans (h n).symm

theorem H00_iff_all_variation_one :
    H00 ↔ ∀ n : ℕ, actualVariation n = 1 :=
  ⟨actual_variation_one_of_H00, H00_of_all_variation_one⟩

/-- This direct positivity consequence is available to the second construction.
Its proof uses normalization and the finite row identity, not RH. -/
theorem actual_weights_nonnegative_of_H00 (h : H00)
    (N j : ℕ) (hj : j ≤ N) :
    0 ≤ actualWeight N j := by
  exact (all_rowVariation_eq_one_iff actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional).mp
      (actual_variation_one_of_H00 h) N j hj

theorem H00_of_actual_weights_nonnegative
    (h : ∀ N j : ℕ, j ≤ N → 0 ≤ actualWeight N j) : H00 := by
  apply H00_of_all_variation_one
  exact (all_rowVariation_eq_one_iff actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional).mpr h

theorem H00_iff_actual_weights_nonnegative :
    H00 ↔ ∀ N j : ℕ, j ≤ N → 0 ≤ actualWeight N j :=
  ⟨actual_weights_nonnegative_of_H00, H00_of_actual_weights_nonnegative⟩

/-- Constant variation supplies the exponential upper bound with constant one. -/
theorem actual_subexponential_of_H00 (h : H00) :
    Subexponential actualVariation := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro n
  rw [actual_variation_one_of_H00 h n, one_mul]
  exact Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Nat.cast_nonneg n))

/-- Route one: zero cancellation -> constant variation -> subexponential
variation -> the retained actual spectral closure. -/
theorem nativeRH_of_H00_route_one (h : H00) : _root_.RiemannHypothesis := by
  exact canonical_actual_subexponential_iff_nativeRH.mp
    (actual_subexponential_of_H00 h)

/-- Retained converse, used only in the reverse direction of equivalences. -/
theorem H00_of_nativeRH (hRH : _root_.RiemannHypothesis) : H00 := by
  exact zero_cancellationBudget_admissible_of_nativeRH hRH

theorem H00_iff_nativeRH_route_one : H00 ↔ _root_.RiemannHypothesis :=
  ⟨nativeRH_of_H00_route_one, H00_of_nativeRH⟩

end RH_HilbertLimit.TwoRoutes
