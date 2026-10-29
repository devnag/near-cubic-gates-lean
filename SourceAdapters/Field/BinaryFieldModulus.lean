import SourceAdapters.Joins.BinaryFieldModulus
import SourceAdapters.Field.BinaryField

/-!
# Join X3′ proved by citation

`binaryFieldModulus : BinaryFieldModulus`: the representation facts need only `GF.ModulusOk`, the field property
only irreducibility; the two machine conjuncts are the join's (they never used the certificate).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Field

open NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins

/-- **Join X3′ holds** (by citation of the released field machinery). -/
theorem binaryFieldModulus : BinaryFieldModulus := by
  obtain ⟨_, _, _, hxor, hpass, hmul⟩ := binaryFieldArithmetic
  refine ⟨?_, ?_, hxor, hpass, hmul⟩
  · intro p ℓ hp
    exact ⟨GF.toPoly_monic p ℓ hp, GF.natDegree_toPoly p ℓ hp, GF.natCard_ref p ℓ hp,
      (GF.encEquiv p ℓ hp).bijective⟩
  · intro p hirr
    haveI : Fact (Irreducible (GF.toPoly p)) := ⟨hirr⟩
    exact Field.toIsField _

end NearCubicGates.Adapters.Field
