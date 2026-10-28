import RH_HilbertLimit.Geometry
import Mathlib.Tactic.FieldSimp

/-!
# Exact interior-disk geometry for the angular closure

This file proves the location and quadratic identity of the proposed pole.
It does not assert the missing actual logarithmic-derivative germ identity.
No Lean, Lake, native compiler, or axiom audit was run during preparation.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit.TwoRoutes

/-- The angular disk coordinate at the radius of a nonzero complex point. -/
def angularZeroCoordinate (z : ℂ) : ℝ :=
  (1 - z.re / ‖z‖) / 2

theorem norm_pos_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) : 0 < ‖z‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact him (congrArg Complex.im hz)

theorem abs_re_lt_norm_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) :
    |z.re| < ‖z‖ := by
  by_contra h
  have heq : |z.re| = ‖z‖ :=
    le_antisymm (Complex.abs_re_le_norm z) (le_of_not_gt h)
  exact him (Complex.abs_re_eq_norm.mp heq)

/-- Every nonreal point maps strictly inside the real diameter of the disk. -/
theorem angularZeroCoordinate_mem_Ioo {z : ℂ} (him : z.im ≠ 0) :
    angularZeroCoordinate z ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn := norm_pos_of_im_ne_zero him
  have hb := abs_lt.mp (abs_re_lt_norm_of_im_ne_zero him)
  have hu : z.re / ‖z‖ < 1 := by
    apply (div_lt_iff₀ hn).mpr
    simpa only [one_mul] using hb.2
  have hl : -1 < z.re / ‖z‖ := by
    apply (lt_div_iff₀ hn).mpr
    simpa only [neg_one_mul] using hb.1
  change 0 < (1 - z.re / ‖z‖) / 2 ∧ (1 - z.re / ‖z‖) / 2 < 1
  constructor <;> linarith

theorem norm_mul_angle_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) :
    ‖z‖ * (1 - 2 * angularZeroCoordinate z) = z.re := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (norm_pos_of_im_ne_zero him)
  unfold angularZeroCoordinate
  field_simp [hn]
  <;> ring

/-- The elementary quadratic with roots z and its conjugate. -/
theorem complex_point_quadratic (z : ℂ) :
    z ^ 2 - ((2 * z.re : ℝ) : ℂ) * z + ((‖z‖ ^ 2 : ℝ) : ℂ) = 0 := by
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  apply Complex.ext
  · simp [pow_two, Complex.mul_re]
    <;> nlinarith [hnorm]
  · simp [pow_two, Complex.mul_im]
    <;> ring

/-- At a=norm z and h=angularZeroCoordinate z, the angular quadratic
has the original point z as a root. -/
theorem angular_quadratic_at_nonreal_point {z : ℂ} (him : z.im ≠ 0) :
    z ^ 2 -
      ((2 * ‖z‖ * (1 - 2 * angularZeroCoordinate z) : ℝ) : ℂ) * z +
      ((‖z‖ ^ 2 : ℝ) : ℂ) = 0 := by
  have hc : 2 * ‖z‖ * (1 - 2 * angularZeroCoordinate z) = 2 * z.re := by
    calc
      _ = 2 * (‖z‖ * (1 - 2 * angularZeroCoordinate z)) := by ring
      _ = 2 * z.re := by rw [norm_mul_angle_of_im_ne_zero him]
  rw [hc]
  exact complex_point_quadratic z

end RH_HilbertLimit.TwoRoutes
