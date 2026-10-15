import Proof.Wire_3_5.PrimAsmHashLeafIface4
import Proof.Wire_3_5.PrimThrWRadSetup2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

abbrev ThrLeafOf4 (l : Literals) : Type :=
  ThrData.ThrStage4U l → (W : PrimT.WalkBank.WalkBankProducer) → FiltSetup.FiltSetupSpec5 W →
    BudgetIface.FiltPipeLe2 → BudgetIface.ThrNumsPoly l →
    ((F : GateFree l) → PrimThrW.RadSetup2.RadSetupSpec2 W.x l F) → WritersJoin.ThrLeafJ2 l

end NearCubicWires.WireExponent3_5.PrimAsm.ThrLeaf
