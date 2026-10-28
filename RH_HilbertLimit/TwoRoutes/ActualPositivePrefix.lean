import RH_HilbertLimit.TwoRoutes.RouteOne
import RH_HilbertLimit.TwoRoutes.PositiveMomentBridge

/-!
# Actual positive Bernstein approximants under `H00`

This is a direct prefix of route two. Its proofs use the finite row consequences
of `H00`, actual normalization, and actual kappa positivity. They never invoke
the RH conclusion or the spectral-closure endpoint.

The quantities below are finite Bernstein approximants. They are not silently
identified with the actual angular/Widder coefficients. Constructing the
Hausdorff limit and proving that all-order identification remain separate tasks.

Prepared without local Lean, Lake, compiler, axiom-audit, or CI execution.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit.TwoRoutes

theorem actual_bernsteinPositive_of_H00 (h : H00) :
    BernsteinPositive actualNormalizedMoment := by
  intro N j hj
  exact actual_weights_nonnegative_of_H00 h N j hj

theorem H00_iff_actual_bernsteinPositive :
    H00 ↔ BernsteinPositive actualNormalizedMoment := by
  constructor
  · exact actual_bernsteinPositive_of_H00
  · intro h
    exact H00_of_actual_weights_nonnegative h

/-- The actual finite positive average, at one Bernstein depth. -/
def actualBernsteinAverage (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  bernsteinAverage actualNormalizedMoment N f

theorem actualBernsteinAverage_const (N : ℕ) (c : ℝ) :
    actualBernsteinAverage N (fun _ => c) = c := by
  exact bernsteinAverage_const actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional N c

theorem actualBernsteinAverage_nonneg (h : H00) (N : ℕ) (f : ℝ → ℝ)
    (hf : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f q) :
    0 ≤ actualBernsteinAverage N f := by
  exact bernsteinAverage_nonneg actualNormalizedMoment
    (actual_bernsteinPositive_of_H00 h) N f hf

theorem actualBernsteinAverage_mono (h : H00) (N : ℕ) (f g : ℝ → ℝ)
    (hfg : ∀ q ∈ Set.Icc (0 : ℝ) 1, f q ≤ g q) :
    actualBernsteinAverage N f ≤ actualBernsteinAverage N g := by
  exact bernsteinAverage_mono actualNormalizedMoment
    (actual_bernsteinPositive_of_H00 h) N f g hfg

theorem actualBernsteinAverage_abs_le (h : H00) (N : ℕ) (f : ℝ → ℝ) (M : ℝ)
    (hf : ∀ q ∈ Set.Icc (0 : ℝ) 1, |f q| ≤ M) :
    |actualBernsteinAverage N f| ≤ M := by
  exact bernsteinAverage_abs_le actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional
    (actual_bernsteinPositive_of_H00 h) N f M hf

/-- Finite approximant to the normalized measure formula for the Widder tower.
This definition is not the actual Widder tower. -/
def actualKernelApproximation (a : ℝ) (N n : ℕ) : ℝ :=
  actualBernsteinAverage N
    (fun q => kernelWeight actualKappa a q *
      kernelMultiplier (actualKappa * a * q) ^ n)

@[simp] theorem actualKernelApproximation_zero (a : ℝ) (N : ℕ) :
    actualKernelApproximation a N 0 =
      actualBernsteinAverage N (kernelWeight actualKappa a) := by
  simp only [actualKernelApproximation, pow_zero, mul_one]

/-- The actual `H00` premise supplies the all-depth, all-order finite bounds. -/
theorem actualKernelApproximation_bounds (h : H00) {a : ℝ} (ha : 0 < a)
    (N n : ℕ) :
    0 ≤ actualKernelApproximation a N n ∧
      actualKernelApproximation a N n ≤ actualKernelApproximation a N 0 := by
  have hb := bernsteinAverage_kernel_bounds actualNormalizedMoment
    (actual_bernsteinPositive_of_H00 h) actualKappa_pos ha N n
  simpa only [actualKernelApproximation, actualBernsteinAverage,
    pow_zero, mul_one] using hb

theorem actualKernelApproximation_abs_le_zero (h : H00) {a : ℝ} (ha : 0 < a)
    (N n : ℕ) :
    |actualKernelApproximation a N n| ≤ actualKernelApproximation a N 0 := by
  have hb := actualKernelApproximation_bounds h ha N n
  rw [abs_of_nonneg hb.1]
  exact hb.2

theorem actual_kernelWeight_le {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    kernelWeight actualKappa a q ≤ 4 * actualKappa * a := by
  have hx : 0 ≤ actualKappa * a * q :=
    mul_nonneg (mul_nonneg actualKappa_pos.le ha.le) hq
  have hd : (1 : ℝ) ≤ (1 + actualKappa * a * q) ^ 2 := by
    nlinarith [sq_nonneg (actualKappa * a * q)]
  have hdpos : (0 : ℝ) < (1 + actualKappa * a * q) ^ 2 := by
    linarith
  change 4 * actualKappa * a / (1 + actualKappa * a * q) ^ 2 ≤
    4 * actualKappa * a
  apply (div_le_iff₀ hdpos).mpr
  have hn : 0 ≤ 4 * actualKappa * a :=
    mul_nonneg (mul_nonneg (by positivity) actualKappa_pos.le) ha.le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hn

/-- The finite mass bound is uniform in the Bernstein depth. -/
theorem actualKernelApproximation_zero_le (h : H00) {a : ℝ} (ha : 0 < a)
    (N : ℕ) :
    actualKernelApproximation a N 0 ≤ 4 * actualKappa * a := by
  rw [actualKernelApproximation_zero]
  calc
    actualBernsteinAverage N (kernelWeight actualKappa a) ≤
        actualBernsteinAverage N (fun _ => 4 * actualKappa * a) := by
      apply actualBernsteinAverage_mono h N
      intro q hq
      exact actual_kernelWeight_le ha hq.1
    _ = 4 * actualKappa * a := actualBernsteinAverage_const N _

theorem actualKernelApproximation_uniform_abs_bound (h : H00) {a : ℝ}
    (ha : 0 < a) (N n : ℕ) :
    |actualKernelApproximation a N n| ≤ 4 * actualKappa * a := by
  exact (actualKernelApproximation_abs_le_zero h ha N n).trans
    (actualKernelApproximation_zero_le h ha N)

end RH_HilbertLimit.TwoRoutes
