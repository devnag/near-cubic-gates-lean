import Proof.Amplification.RecoveryTseitinNativeNodeLoop

/-! The actual original Boolean circuit discharges all node-loop capacities
and well-formedness premises with one common physically supplied capacity. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_large (n count : Nat) : n+count+1 ≤ capacity n count := by
  let R:=n+count+1
  have h1 : 1 ≤ R := by dsimp [R]; omega
  have h2 : R ≤ R^2 := by nlinarith
  have h3 : R^2 ≤ R^3 := by nlinarith [Nat.mul_le_mul_left (R^2) h1]
  change R ≤ 2199023255552*R^3
  omega
theorem requirements_of_wellformed {n : Nat} (nodes : List (BooleanNode n)) (index total : Nat)
    (hsize : index+nodes.length ≤ total)
    (hw : ∀ j : Fin nodes.length,(nodes.get j).WellFormedAt (index+j.val)) :
    requirements index (capacity n total) nodes := by
  induction nodes generalizing index with
  | nil=>trivial
  | cons node nodes ih=>
    have hn : node.WellFormedAt index := by
      have h:=hw 0
      change node.WellFormedAt (index+0) at h
      simpa only [Nat.add_zero] using h
    refine ⟨hn,node_budget_bound total index (by simp only [List.length_cons] at hsize; omega) node hn,?_,?_⟩
    · have h:=capacity_large n total
      simp only [List.length_cons] at hsize
      omega
    · apply ih (index+1) (by simp only [List.length_cons] at hsize; omega)
      intro j
      have h:=hw j.succ
      change (nodes.get j).WellFormedAt (index+(j.val+1)) at h
      simpa only [Nat.add_assoc,Nat.add_comm 1 j.val] using h
theorem circuit_requirements {n : Nat} (circuit : BooleanCircuit n) :
    requirements 0 (capacity n circuit.nodes.length) circuit.nodes :=
  requirements_of_wellformed circuit.nodes 0 circuit.nodes.length (by omega)
    (by intro j; simpa only [Nat.zero_add] using circuit.wellFormed j)
theorem circuit_run {n : Nat} (circuit : BooleanCircuit n) (pre tail out : List Bool) :
    ∃ r,runFrom loopMachine
      (circuit.nodes.length*(stepBudget (capacity n circuit.nodes.length)+2)+circuit.nodes.length+3)
      (configuration 0 n 0 pre.length (source pre tail circuit.nodes) out
        (capacity n circuit.nodes.length) circuit.nodes.length 1)=some r ∧
      r.final=configuration 3 n circuit.nodes.length (pre.length+(nativeWords circuit.nodes).length)
        (source pre tail circuit.nodes)
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodesClausesFrom 0 circuit.nodes))
        (capacity n circuit.nodes.length) circuit.nodes.length 1 ∧
      r.steps ≤ circuit.nodes.length*(stepBudget (capacity n circuit.nodes.length)+2)+circuit.nodes.length+3 := by
  have h:=loop_run circuit.nodes pre tail out 0 (capacity n circuit.nodes.length) circuit.nodes.length 0
    (by omega) (circuit_requirements circuit)
  simpa only [Nat.zero_add,emitted_original] using h

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
