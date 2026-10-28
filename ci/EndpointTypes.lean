import RH_HilbertLimit.TwoRoutes.RouteOne
import RH_HilbertLimit.TwoRoutes.RouteTwo

/- The exported statements must retain the exact semantic premise and literal RH. -/
#check (RH_HilbertLimit.TwoRoutes.nativeRH_of_H00_route_one :
  RH_HilbertLimit.TwoRoutes.H00 → _root_.RiemannHypothesis)
#check (RH_HilbertLimit.TwoRoutes.nativeRH_of_H00_route_two :
  RH_HilbertLimit.TwoRoutes.H00 → _root_.RiemannHypothesis)
#check (RH_HilbertLimit.TwoRoutes.H00_iff_nativeRH_route_one :
  RH_HilbertLimit.TwoRoutes.H00 ↔ _root_.RiemannHypothesis)
#check (RH_HilbertLimit.TwoRoutes.H00_iff_nativeRH_route_two :
  RH_HilbertLimit.TwoRoutes.H00 ↔ _root_.RiemannHypothesis)
