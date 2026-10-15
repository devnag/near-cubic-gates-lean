import Proof.Wire_3_5.UnionMachineThrDecIface
import Proof.Wire_3_5.PrimAsmThrLeafIface4
import Proof.Wire_3_5.FinalPassSeamsUni
import Proof.Wire_3_5.PrimThrWShellIface

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-- **The THR unit machine at a gate**: on the cell layout `LNS x`, capacity `need`, unit budget `nU` (both
quasi-bounded in `n`); at every THR call, output `out`, unit `j` and capacity `cap ≥ need n + j`, the shell's
`UnitOK` with the call's request word, counts and the units' emission. -/
structure ThrUnitSpec (l : Literals) (F : GateFree l) where
  x : ℕ
  sU : ℕ
  U : Machine (PrimAsm.CellLoop.TT x) sU
  need : ℕ → ℕ
  nU : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  Kn : ℕ
  need_q : ∀ n, QuasiBounded (need n) n Cn Dn Kn
  Cu : ℕ
  Du : ℕ
  Ku : ℕ
  nU_q : ∀ n, QuasiBounded (nU n) n Cu Du Ku
  ok : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need n + j ≤ cap →
    PrimThrW.Shell.UnitOK cap x U (nU n) (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out

/-- The unit's exponents (with the envelope: from `(l, fe)` only). -/
def ThrUnitSpec.deg {l : Literals} {F : GateFree l} (U : ThrUnitSpec l F) : ℕ := max (max U.Dn U.Kn) (max U.Du U.Ku)

/-- The unit's coefficients (after `F`). -/
def ThrUnitSpec.cf {l : Literals} {F : GateFree l} (U : ThrUnitSpec l F) : ℕ := U.Cn + U.Cu

/-- **The unit machines in `ThrLeafJ2`'s order of choice** (`Seams.StageU`). -/
abbrev ThrUnitU (l : Literals) : Type :=
  FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrUnitSpec l F) (fun U => U.deg) (fun U => U.cf)

abbrev ThrLeafOfU (l : Literals) : Type :=
  ThrData.ThrStage4U l → ThrUnitU l → WritersJoin.ThrLeafJ2 l

/-- The decode front's exponents and coefficients. -/
def decDeg {x : ℕ} {l : Literals} {F : GateFree l} (D : ThrDec.ThrDecFront x l F) : ℕ :=
  max (max D.Dn D.Kn) (max D.Db D.Kb)

def decCf {x : ℕ} {l : Literals} {F : GateFree l} (D : ThrDec.ThrDecFront x l F) : ℕ := D.Cn + D.Cb

/-- The RADIX setup's exponents and coefficients. -/
def radDeg {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB3.RadSetupSpecB3 x l F) : ℕ :=
  max (max (max R.Dn R.Kn) (max R.Db R.Kb)) (max R.Dp R.Kp)

def radCf {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB3.RadSetupSpecB3 x l F) : ℕ := R.Cn + R.Cb + R.Cp

/-- **C6b's producer statement**: the uniform decode fronts and RADIX setups on the unit cells `xF F`
(`W.x ≤ xF F`: T3's DockW lift of the FILTER setup), the FILTER setup `FiltSetupSpec5 W` and its pipe bound give the
unit machines in `ThrLeafJ2`'s order of choice. -/
abbrev ThrUnitOf (l : Literals) : Type :=
  ∀ (W : PrimT.WalkBank.WalkBankProducer) (xF : GateFree l → ℕ), (∀ F, W.x ≤ xF F) →
    FiltSetup.FiltSetupSpec5 W → BudgetIface.FiltPipeLe2 →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => decDeg D)
      (fun D => decCf D) →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB3.RadSetupSpecB3 (xF F) l F) (fun R => radDeg R)
      (fun R => radCf R) →
    ThrUnitU l

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
