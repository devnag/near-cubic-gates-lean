import Proof.Amplification.RecoveryTseitinNodeRun
import Proof.Amplification.RecoveryTseitinWidth

/-! One common circuit-size capacity discharges every original node-plan
clause, including both equivalence directions and the final assertion. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (arity size : Nat) := 8388608*(natBitLength (arity+size)+1)^2

theorem references_bound {n : Nat} (index : Nat) (node : BooleanNode n)
    (hw : node.WellFormedAt index) (j : Fin 3) : references index node j≤n+index := by
  cases node with
  | const b=>fin_cases j <;> simp [references,circuitInputGateVariable,gateVariable]
  | input i=>have hi:=i.isLt; fin_cases j <;> simp [references,circuitInputGateVariable,gateVariable]; omega
  | not i=>change i < index at hw; fin_cases j <;> simp [references,circuitInputGateVariable,gateVariable]; omega
  | and left right=>rcases hw with ⟨hi,hj⟩; fin_cases j <;> simp [references,circuitInputGateVariable,gateVariable] <;> omega
  | or left right=>rcases hw with ⟨hi,hj⟩; fin_cases j <;> simp [references,circuitInputGateVariable,gateVariable] <;> omega

theorem plan_capacity {n : Nat} (index size : Nat) (node : BooleanNode n)
    (hw : node.WellFormedAt index) (hi : index ≤ size) (p : Plan) :
    RecoveryTseitin.capacity (Prepare.literals p.signs (indices (references index node) p))≤capacity n size := by
  apply RecoveryTseitin.capacity_bound _ (natBitLength (n+size))
  · unfold natBitLength
    omega
  · intro j
    have h:=(references_bound index node hw (p.sources j)).trans (Nat.add_le_add_left hi n)
    exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem plan_count (tag : Fin 6) : (plans tag).length≤3 := by fin_cases tag <;> decide

end NearCubicWires.RepairSource.RecoveryTseitinNode
