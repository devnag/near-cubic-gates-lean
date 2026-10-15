import Proof.Gates.Succinct.SubstitutionMain
import Proof.Gates.Succinct.SubstitutionRunSpec

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

def PreSpec : Prop :=
  ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) (cap : ℕ), capH o B ≤ cap →
    ∃ σ1 σ2 σ3 σ4 : WState 4 nrH,
      WExec cap header (start o.word (PCPPNative.descriptor B)) σ1 (headCost (sizeS o B)) ∧
      WExec cap countPass σ1 σ2 (cntCost (sizeS o B)) ∧
      WXExec cap sizes σ2 σ3 (sizesCost (sizeS o B)) ∧
      WExec cap emStart σ3 σ4 (1000000 * (sizeS o B + 2) ^ 3) ∧
      MInv o B 0 σ4

def PostSpec : Prop :=
  ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) (cap : ℕ) (σ : WState 4 nrH), capH o B ≤ cap →
    MInv o B o.circuit.nodes.length σ →
    ∃ τ, WExec cap emissionEnd σ τ (2 * cIter (sizeS o B)) ∧
      τ.st sO = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity) ∧
      τ.st sW = o.word ∧ τ.st sD = PCPPNative.descriptor B

def CostSpec : Prop :=
  ∀ (S n : ℕ), n ≤ S →
    headCost S + cntCost S + sizesCost S + 1000000 * (S + 2) ^ 3 + n * (readCost 5 + nIter S + 20 + 4) +
      2 * cIter S + 100 ≤ substCostClass S

end NearCubicGates.Close.Succinct.SubstMachine
