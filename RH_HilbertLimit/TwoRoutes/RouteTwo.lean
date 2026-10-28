import RH_HilbertLimit.TwoRoutes.MeasureResolvent

/-!
# The second H00 implication: positive measure and analytic resolvent

The forward proof constructs its measure, derives the actual origin germ,
continues the analytic ODE, and excludes nonreal poles. It never calls the
first route's spectral closure or RH conclusion. The reverse implication is
the retained RH-to-H00 direction, common to both equivalences.

This completes the compressed measure--resolvent construction in source.
The longer Widder/angular-PDE construction remains separately unformalized.
Native Lean compilation and the exact axiom audit have not been run here.
-/

set_option autoImplicit false

namespace RH_HilbertLimit.TwoRoutes

/-- The only mathematical premise is the original semantic H00 witness. -/
theorem nativeRH_of_H00_route_two (h : H00) : _root_.RiemannHypothesis :=
  nativeRH_of_H00_via_measure_resolvent h

/-- Route two proves the forward direction independently; the converse is
the common, previously supplied RH-to-H00 construction. -/
theorem H00_iff_nativeRH_route_two : H00 ↔ _root_.RiemannHypothesis :=
  ⟨nativeRH_of_H00_route_two, H00_of_nativeRH⟩

end RH_HilbertLimit.TwoRoutes
