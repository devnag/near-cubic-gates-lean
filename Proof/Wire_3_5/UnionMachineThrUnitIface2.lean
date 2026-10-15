import Proof.Wire_3_5.UnionMachineThrUnitIface
import Proof.Wire_3_5.UnionMachineRadSetupB4

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-- **The THR unit machine at a gate, v2**: `need`, `nU` polynomial in the per-call measure `meas`, which the THR load
absorbs (`meas_le`). -/
structure ThrUnitSpec2 (l : Literals) (F : GateFree l) where
  x : ℕ
  sU : ℕ
  U : Machine (PrimAsm.CellLoop.TT x) sU
  meas : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ), ℕ
  need : ℕ → ℕ
  nU : ℕ → ℕ
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ X, need X ≤ Kn * (X + 1) ^ Dn
  Ku : ℕ
  Du : ℕ
  nU_le : ∀ X, nU X ≤ Ku * (X + 1) ^ Du
  Km : ℕ
  Dm : ℕ
  meas_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤
      Km * (n + 2) ^ Dm * 2 ^ (Km * ((gate0 l F).budget kclk coef A a ha).psiOf n)
  ok : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need (meas kclk coef A a ha n hs a' ha' Cs carriers translation) + j ≤ cap →
    PrimThrW.Shell.UnitOK cap x U (nU (meas kclk coef A a ha n hs a' ha' Cs carriers translation))
      (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out

/-- The unit's exponents (with the envelope: from `(l, fe)` only). -/
def ThrUnitSpec2.deg2 {l : Literals} {F : GateFree l} (U : ThrUnitSpec2 l F) : ℕ :=
  max (max U.Dn U.Du) (max U.Dm U.Km)

/-- The unit's coefficients (after `F`). -/
def ThrUnitSpec2.cf2 {l : Literals} {F : GateFree l} (U : ThrUnitSpec2 l F) : ℕ := U.Kn + U.Ku

/-- **The unit machines v2 in `ThrLeafJ2`'s order of choice** (`Seams.StageU`). -/
abbrev ThrUnitU2 (l : Literals) : Type :=
  FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrUnitSpec2 l F) (fun U => U.deg2) (fun U => U.cf2)

abbrev ThrLeafOfU2 (l : Literals) : Type :=
  ThrData.ThrStage4U l → ThrUnitU2 l → WritersJoin.ThrLeafJ2 l

/-- The RADIX setup v4's exponents and coefficients. -/
def radDeg4 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB4.RadSetupSpecB4 x l F) : ℕ :=
  max (max R.Dn R.Db) R.Dp

def radCf4 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB4.RadSetupSpecB4 x l F) : ℕ := R.Kn + R.Kb + R.Kp

/-- **C6b's producer statement, v2**: the uniform decode fronts and RADIX setups (v4) on the unit cells `xF F`, the
FILTER setup and its pipe bound give the unit machines v2. -/
abbrev ThrUnitOf2 (l : Literals) : Type :=
  ∀ (W : PrimT.WalkBank.WalkBankProducer) (xF : GateFree l → ℕ), (∀ F, W.x ≤ xF F) →
    FiltSetup.FiltSetupSpec5 W → BudgetIface.FiltPipeLe2 →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => decDeg D)
      (fun D => decCf D) →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB4.RadSetupSpecB4 (xF F) l F) (fun R => radDeg4 R)
      (fun R => radCf4 R) →
    ThrUnitU2 l

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
