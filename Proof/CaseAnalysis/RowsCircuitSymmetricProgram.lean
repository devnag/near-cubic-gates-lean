import Proof.CaseAnalysis.RowsCircuitWholeBudget

/-! Freeze the full symmetric controller as one named machine/state pair.
Its body and public semantic fields are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricRun
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsGatePairHeads CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def test (b : Fin 1703 → Bool):=b 638 && b 1676
noncomputable def program : Σ s,Machine 1703 s:=
  ⟨_,CloseoutRowsGateColdPair.machine CloseoutRowsCircuitColdSymmetric.machine
    (CloseoutRowsCircuitBody.machine false) test⟩
noncomputable def machine : Machine 1703 program.1:=program.2
def top (bits : List Bool):=CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)
def native (core : ℕ) (bits : List Bool):=natWord (words bits).length++frame (top bits)++
  (List.range (words bits).length).flatMap (outputs false core 1 [] (words bits))
def passed (core W L : ℕ) (bits : List Bool) : Prop:=
  CloseoutRowsCircuitPrefix.valid false bits ∧
  CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3) ∧
  validity core true (words bits) (words bits).length=true ∧
  CloseoutRowsCircuitArithmeticDock.amount false (descriptions core (words bits) 0 (words bits).length)
    (words bits).length ≤ L ∧ wires false core 1 [] (words bits) 0 (words bits).length ≤ W

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricRun
