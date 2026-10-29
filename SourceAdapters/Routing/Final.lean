import SourceAdapters.Routing.CoordinateJoin
import SourceAdapters.Routing.NormalizedEmission
import SourceAdapters.Routing.ResourceArithmetic
import SourceAdapters.Routing.RoutingDegree
import SourceAdapters.Routing.CircuitFinal
import SourceAdapters.Routing.InputEmbedding
import SourceAdapters.Routing.FieldCompletion
import SourceAdapters.Routing.RoutingPolynomial

/-! Complete supplier for the AffineRouting interface.

All fifteen fields are proved on their literal definitions. The definite
coordinate array and generic circuit compiler are exposed in the imports.
Ordinary-machine generation and the RAM event-trace embedding are separate
assembly interfaces; neither is a premise of this routing theorem.
-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing

theorem contract {F : Type} [Field F] [CharP F 2] : Contract (F := F) where
  benes_complete := Completeness.benesCompleteness
  benes_sound := Soundness.benesSoundness
  coordinates := coordinateExistence
  interpolation := tableInterpolation
  normalized_emission := Selectors.normalizedEmission
  resource_arithmetic := Resources.resourceArithmetic
  layout := LayoutFacts.layoutCorrect
  access := LayoutFacts.accessCoverage
  translations := fun l e _ => LayoutFacts.translationLanding l e
  input := LayoutFacts.inputEmbedding
  circuit := fun l e _ coords => circuitCorrect l e coords
  routing_degree := fun l e _ coords => Selectors.routingDegree l e coords
  polynomial := fun l e _ coords => RoutingPolynomial.routingPolynomialCorrect l e coords
  soundness := fun l e _ => FieldSoundness.fieldRoutingSoundness l e
  completion := FieldCompletion.fieldRoutingCompletion

/-- Public all-field supplier, with no assumed reduction or routing premise. -/
theorem affineRouting : Joins.AffineRouting := by
  intro F instField instChar
  exact contract

end NearCubicGates.Adapters.Routing
