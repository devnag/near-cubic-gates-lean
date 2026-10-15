import Proof.Gates.Succinct.SubstitutionPhaseSpecs

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

def LoopSpec : Prop :=
  ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) (σ : WState 4 nrH), MInv o B 0 σ →
    ∃ (τ : WState 4 nrH) (c : ℕ),
      WExec (capH o B) (.whr (regH .iC) (.seq (.dec (regH .iC)) nodeBody)) σ τ c ∧
      c ≤ o.circuit.nodes.length * (readCost 5 + nIter (sizeS o B) + 20 + 4) + 1 ∧
      MInv o B o.circuit.nodes.length τ

def EndOutSpec : Prop :=
  ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q),
    marks (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native ++
        PCPPRequestNodeSchema.native
          (BooleanNode.not (posF (ofl o.circuit) o.circuit.output.val (B.nodes.length - 1) B.output.val) :
            BooleanNode q) ++
        (List.replicate (q - (szv o B + 1)) (BooleanNode.const false : BooleanNode q)).flatMap
          PCPPRequestNodeSchema.native ++
        natWord (szv o B)) ++ [false] =
      RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity)

end NearCubicGates.Close.Succinct.SubstMachine
