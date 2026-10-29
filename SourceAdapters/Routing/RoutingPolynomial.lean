import SourceAdapters.Routing.RoutingPolynomialHosts
import SourceAdapters.Routing.RoutingDisjoint

/-! Exact polynomial/local-equation equivalence for the routing polynomial. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

variable {F : Type} [Field F] [CharP F 2]

/-- The actual normalized routing polynomial vanishes on the entire affine cube
iff the table satisfies all five local routing families. Once coordinate
polynomials are supplied, this equivalence needs no further basis assumption. -/
theorem routingPolynomialCorrect (l : Layout) (e : Fin l.m → F)
    (coords : Coordinates l.m e) : RoutingPolynomialCorrect l e coords := by
  intro a
  exact (emission_iff_guarded l e coords (routingTerms_disjoint l) a).trans
    ((guarded_iff_host l e a).trans (host_equations_iff l e a))

end NearCubicGates.Adapters.Routing.RoutingPolynomial
