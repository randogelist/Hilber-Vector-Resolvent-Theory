import RH_HilbertLimit.ActualXi
import AngularMaster.ComplexScaleProduct
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Unconditional reality of the actual logarithmic moments

The archived Schwarz-reflection theorem concerns the same `AWPIRH.theta`
as the frozen actual-moment definitions. Conjugation symmetry is preserved
by Mathlib's total derivative, by totalized division, and by every iterated
derivative. Evaluating at zero therefore proves reality of the exact
`actualComplexMoment` at every order.

No RH, zero-location, calibration, or power-sum premise is used here.
In particular, this proof does not assume a logarithmic-derivative identity.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate

namespace RH_HilbertLimit

/-- Schwarz reflection is preserved by the total complex derivative. -/
theorem deriv_conj_of_schwarz {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  have hfun : conj ∘ f ∘ conj = f := by
    funext w
    change conj (f (conj w)) = f w
    rw [hf w]
    simp
  have hd := deriv_conj_conj (f := f)
  rw [hfun] at hd
  simpa [Function.comp_apply] using congrFun hd (conj z)

/-- Every total iterated derivative preserves the same reflection. -/
theorem iteratedDeriv_conj_of_schwarz {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, f (conj z) = conj (f z)) (n : ℕ) :
    ∀ z : ℂ, iteratedDeriv n f (conj z) = conj (iteratedDeriv n f z) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
      intro z
      simpa only [iteratedDeriv_succ] using deriv_conj_of_schwarz ih z

/-- The literal theta logarithmic derivative has Schwarz reflection. -/
theorem actualLogDerivative_conj (z : ℂ) :
    actualLogDerivative (conj z) = conj (actualLogDerivative z) := by
  unfold actualLogDerivative
  rw [deriv_conj_of_schwarz AngularMaster.actual_theta_conj z,
    AngularMaster.actual_theta_conj z]
  simp only [map_div₀]

/-- The exact iterated derivatives defining the moments have reflection. -/
theorem actualLogDerivative_iteratedDeriv_conj (n : ℕ) (z : ℂ) :
    iteratedDeriv n actualLogDerivative (conj z) =
      conj (iteratedDeriv n actualLogDerivative z) :=
  iteratedDeriv_conj_of_schwarz actualLogDerivative_conj n z

/-- Every literal complex moment is fixed by complex conjugation. -/
theorem actualComplexMoment_conj (n : ℕ) :
    conj (actualComplexMoment n) = actualComplexMoment n := by
  have hd : conj (iteratedDeriv n actualLogDerivative 0) =
      iteratedDeriv n actualLogDerivative 0 := by
    simpa using (actualLogDerivative_iteratedDeriv_conj n 0).symm
  unfold actualComplexMoment
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one,
    Complex.conj_natCast, hd]

/-- Unconditional all-order reality for the current actual moments. -/
theorem actualComplexMoment_im_eq_zero (n : ℕ) :
    (actualComplexMoment n).im = 0 :=
  Complex.conj_eq_iff_im.mp (actualComplexMoment_conj n)

/-- The real coordinate already used in `ActualXi` is the full moment. -/
theorem actualComplexMoment_eq_ofReal_actualMoment (n : ℕ) :
    actualComplexMoment n = (actualMoment n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using actualComplexMoment_im_eq_zero n

end RH_HilbertLimit
