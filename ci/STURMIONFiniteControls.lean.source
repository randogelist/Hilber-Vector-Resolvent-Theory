import Lean
set_option autoImplicit false

/-! Finite Boolean scalar acceptance and rejection controls only.
    These do not certify the actual Riemann xi function or RH. -/
namespace STURMIONFiniteControls

def checkInterval (lower actual upper : Int) : Bool :=
  decide (lower ≤ actual ∧ actual ≤ upper)

def checkExclusion (lower actual upper : Int) : Bool :=
  decide (actual < lower ∨ upper < actual)

theorem checkInterval_sound (lower actual upper : Int)
    (h : checkInterval lower actual upper = true) :
    lower ≤ actual ∧ actual ≤ upper := by
  simpa [checkInterval] using h

theorem checkInterval_complete (lower actual upper : Int)
    (h : lower ≤ actual ∧ actual ≤ upper) :
    checkInterval lower actual upper = true := by
  simpa [checkInterval] using h

example : checkInterval 1 2 3 = true := by decide
example : checkInterval 1 0 3 = false := by decide
example : checkExclusion 1 0 3 = true := by decide

end STURMIONFiniteControls

#print axioms STURMIONFiniteControls.checkInterval_sound
#print axioms STURMIONFiniteControls.checkInterval_complete
