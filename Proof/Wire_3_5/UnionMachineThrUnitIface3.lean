import Proof.Wire_3_5.UnionMachineThrUnitIface2
import Proof.Wire_3_5.UnionMachineRadSetupB5

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

/-- The RADIX setup v5's exponents and coefficients. -/
def radDeg5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ :=
  max (max R.Dn R.Db) R.Dp

def radCf5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ := R.Kn + R.Kb + R.Kp

/-- **C6b's producer statement, v3** (over `RadSetupSpecB5`). -/
abbrev ThrUnitOf3 (l : Literals) : Type :=
  ∀ (W : PrimT.WalkBank.WalkBankProducer) (xF : GateFree l → ℕ), (∀ F, W.x ≤ xF F) →
    FiltSetup.FiltSetupSpec5 W → BudgetIface.FiltPipeLe2 →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => decDeg D)
      (fun D => decCf D) →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB5.RadSetupSpecB5 (xF F) l F) (fun R => radDeg5 R)
      (fun R => radCf5 R) →
    ThrUnitU2 l

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
