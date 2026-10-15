import Proof.Amplification.RecoveryTseitinNativeColdFormula
import Proof.Assembly.AppendOutputFrame

/-! Frame exactly the bytes emitted by the cold original circuit-formula
producer, measuring and returning the actual append cursor physically. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def framedMachine:=AppendOutputFrame.machine machine (1333 : Fin 1370)
def framedInput {n : Nat} (circuit : BooleanCircuit n):=AppendOutputFrame.input (circuitInput circuit)
def framedBudget (n count length : Nat):=2*budget n count+4*length+7

theorem framed_run {n : Nat} (circuit : BooleanCircuit n) : ∃ r,
    run framedMachine (framedBudget n circuit.nodes.length
      (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length)
      (framedInput circuit)=some r ∧
      r.final.tapes 1372=frame (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)) ∧
      (∀ i,r.final.heads i=0) ∧
      r.steps ≤ framedBudget n circuit.nodes.length
        (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length := by
  obtain ⟨base,hbase,bh,bt,bs⟩:=cold_run circuit
  obtain ⟨r,hr,rt,rh,rs⟩:=AppendOutputFrame.frame_run machine 1333 output_forward _ _ base hbase _ bt bh
  have hb : 2*base.steps+4*(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length+7 ≤
      framedBudget n circuit.nodes.length
        (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length := by
    unfold framedBudget
    omega
  have hm:=run_moreFuel framedMachine _
    (framedBudget n circuit.nodes.length
      (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length-
      (2*base.steps+4*(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length+7)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,rt,rh,rs.trans hb⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
