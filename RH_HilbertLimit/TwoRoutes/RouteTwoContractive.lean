import Derivations.BKQR.HardyCoefficientTransfer

/-!
# Route two: the contractive segment and normalized kernel estimates

Source-only preparation for the user's native compiler. No local Lean, Lake,
native compiler, or axiom-audit execution was performed.

This module proves genuine generic components of the second route. It does not
assert that an actual orbit has already been constructed from `H00`, and it does
not assume or manufacture the missing actual angular-jet identification.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit.TwoRoutes

open NativeSolobolo
open NativeSolobolo.Derivations.BKQR

section ContractiveSegment

variable {Vec : Type} {Q : RealGramGeometry Vec} {mu : ℝ → ℕ → ℝ}

/-- The base coefficient of a genuine BKQR orbit is nonnegative. -/
theorem contractiveOrbit_base_nonnegative
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) : 0 ≤ mu a 0 := by
  rw [M.base_moment a]
  exact Q.normSq_nonnegative_real (M.u a)

/-- The defect-square identity bounds the actual represented coefficient. -/
theorem contractiveOrbit_abs_le_base
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : ℕ) :
    |mu a n| ≤ mu a 0 := by
  have hsq := MOMENT_SQ_LE_BASE_SQ M a n
  have habs : |mu a n| ≤ |mu a 0| := (sq_le_sq).mp hsq
  simpa only [abs_of_nonneg (contractiveOrbit_base_nonnegative M a)] using habs

/-- Every represented coefficient series is absolutely summable at each real
radius strictly inside the unit disk. This uses the already-proved geometric
majorant transfer, specialized to outer radius one. -/
theorem contractiveOrbit_absolute_summability
    (M : BKQRContractiveOrbit Q mu) (a : ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => |mu a n| * r ^ n) := by
  apply WEIGHTED_COEFF_BOUND_IMPLIES_SUMMABLE_AT_SMALLER_RADIUS
    (fun n => mu a n) (R := 1) (C := mu a 0) hr0 (by norm_num) hr1
    (contractiveOrbit_base_nonnegative M a)
  intro n
  simpa only [one_pow, mul_one] using contractiveOrbit_abs_le_base M a n

end ContractiveSegment

/-- The normalized positive weight furnished by a Hausdorff measure. -/
def normalizedWeight (kappa a q : ℝ) : ℝ :=
  (4 * kappa * a) / (1 + kappa * a * q) ^ 2

/-- The normalized contraction multiplier; its range is contained in [0,1]. -/
def normalizedMultiplier (kappa a q : ℝ) : ℝ :=
  (4 * kappa * a * q) / (1 + kappa * a * q) ^ 2

theorem normalizedMultiplier_eq_mul_weight (kappa a q : ℝ) :
    normalizedMultiplier kappa a q = q * normalizedWeight kappa a q := by
  unfold normalizedMultiplier normalizedWeight
  ring

theorem normalizedWeight_pos {kappa a q : ℝ}
    (hkappa : 0 < kappa) (ha : 0 < a) (hq : 0 ≤ q) :
    0 < normalizedWeight kappa a q := by
  unfold normalizedWeight
  positivity

theorem normalizedMultiplier_nonnegative {kappa a q : ℝ}
    (hkappa : 0 < kappa) (ha : 0 < a) (hq : 0 ≤ q) :
    0 ≤ normalizedMultiplier kappa a q := by
  unfold normalizedMultiplier
  positivity

theorem normalizedMultiplier_le_one {kappa a q : ℝ}
    (hkappa : 0 < kappa) (ha : 0 < a) (hq : 0 ≤ q) :
    normalizedMultiplier kappa a q ≤ 1 := by
  have hden : 0 < (1 + kappa * a * q) ^ 2 := by positivity
  unfold normalizedMultiplier
  apply (div_le_one hden).2
  nlinarith [sq_nonneg (1 - kappa * a * q)]

/-- The integrand-level bound needed for every actual Widder order. It is
valid even at q=0 and uses no regularity or density of a representing measure. -/
theorem normalizedKernel_between_zero_and_base {kappa a q : ℝ}
    (hkappa : 0 < kappa) (ha : 0 < a) (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ normalizedWeight kappa a q * normalizedMultiplier kappa a q ^ n ∧
      normalizedWeight kappa a q * normalizedMultiplier kappa a q ^ n ≤
        normalizedWeight kappa a q := by
  have hw : 0 ≤ normalizedWeight kappa a q :=
    le_of_lt (normalizedWeight_pos hkappa ha hq)
  have hl0 := normalizedMultiplier_nonnegative hkappa ha hq
  have hl1 := normalizedMultiplier_le_one hkappa ha hq
  constructor
  · exact mul_nonneg hw (pow_nonneg hl0 n)
  · calc
      normalizedWeight kappa a q * normalizedMultiplier kappa a q ^ n
          ≤ normalizedWeight kappa a q * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hl0 hl1) hw
      _ = normalizedWeight kappa a q := mul_one _

/-- The endpoint atom has the exact expected value at order zero. -/
theorem normalizedWeight_zero (kappa a : ℝ) :
    normalizedWeight kappa a 0 = 4 * kappa * a := by
  simp [normalizedWeight]

/-- An endpoint atom contributes zero at every positive order. -/
theorem normalizedKernel_zero_succ (kappa a : ℝ) (n : ℕ) :
    normalizedWeight kappa a 0 * normalizedMultiplier kappa a 0 ^ (n + 1) = 0 := by
  simp [normalizedMultiplier]

end RH_HilbertLimit.TwoRoutes
