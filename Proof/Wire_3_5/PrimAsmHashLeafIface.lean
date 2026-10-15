import Proof.Wire_3_5.PrimAsmBudgetIface
import Proof.Wire_3_5.PrimAsmBudgetIface2
import Proof.Wire_3_5.PrimAsmWritersJoin
import Proof.Wire_3_5.FinalPassSeamsUni

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **T's v3 data stage at the gate's call families, uniform constants** (StageU order). -/
abbrev ThrStage3U (l : Literals) : Type :=
  FinalPass.Seams.StageU l
    (fun F kclk coef A a ha => ThrData.ThrDataStage3 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
    (fun S => max S.Dc3 S.Dn) (fun S => S.Cc3 + S.Kn)

abbrev HashLeafOf (l : Literals) : Type :=
  ThrStage3U l → (W : PrimT.WalkBank.WalkBankProducer) → FiltSetup.FiltSetupSpec5 W →
    BudgetIface.FiltPipeLe2 → BudgetIface.ThrNumsPoly l → WritersJoin.HashLeafJ2 l

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
