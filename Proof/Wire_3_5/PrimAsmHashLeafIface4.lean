import Proof.Wire_3_5.PrimAsmHashLeafIface
import Proof.Wire_3_5.PrimTThrDataIface4

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

abbrev HashLeafOf4 (l : Literals) : Type :=
  ThrData.ThrStage4U l → (W : PrimT.WalkBank.WalkBankProducer) → FiltSetup.FiltSetupSpec5 W →
    BudgetIface.FiltPipeLe2 → BudgetIface.ThrNumsPoly l → WritersJoin.HashLeafJ2 l

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
