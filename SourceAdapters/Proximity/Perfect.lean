import SourceAdapters.Proximity.HonestPreparation
import SourceAdapters.Proximity.TrimHonestFinal

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the literal half-soundness source theorem supplies the
full perfect three-query proximity interface. This includes every real
proximity parameter in (0,1), exact signed three-query semantics, polynomial
proof and coin bounds, and both actual polynomial-time TM2 machines. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

theorem perfect_three_query_proximity :
    NearCubicGates.Published.CW19Proximity.Lemma22Half →
      NearCubicGates.PublishedSources.PCPP.PerfectThreeQueryProximityLiteral :=
  perfect_from_honest_restriction TrimHonest.honestRestriction_join

end NearCubicGates.Adapters.Proximity
