import Proof.Amplification.RecoveryFormulaSerializeFrame

/-! The exact existing balanced CNF payload is produced on a fresh framed
oracle output. Its sole input is the actual stream of ordinary clause codes;
the following formula emitter must produce that stream from the same PCP. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPayload
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization CanonicalBinary BalancedCNFSATEncoding OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports : Ports 133 := ⟨by decide,131,by decide,131,by decide⟩
noncomputable def program := ports.program (ordinary RecoveryFormulaFrame.machine)

theorem input_tapes (fields : List (List Bool)) :
    RecoveryFormulaFrame.input fields=(program.base.inputTapes (FieldList.stream fields)) := by
  funext i
  change Fin.addCases (RecoveryFormulaSerialize.input fields) (fun _ : Fin 2=>[]) i=
    (if i.val=0 then RepairOrdinary.frame (FieldList.stream fields) else [])
  refine Fin.addCases (m:=131) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,RecoveryFormulaSerialize.input]
    rfl
  · simp only [Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem field_runs (oracle : Nat→Bool) (fields : List (List Bool)) :
    OrdinaryOracleRuns oracle program (FieldList.stream fields) (PCPTraversal.code fields).bits
      (RecoveryFormulaFrame.budget fields) := by
  obtain ⟨r,hr,hout,hs⟩ := RecoveryFormulaFrame.raw_run fields
  rw [input_tapes] at hr
  exact ⟨r.steps,r.final,hs.trans (RecoveryFormulaFrame.budget_bound fields),
    ordinary_trace ports RecoveryFormulaFrame.machine _ _ r hr,
    (prefix_of_run _ _ _ r hr).2,hout⟩

def fields (formula : EncodedCNF) := formula.map (fun clause=>(Encodable.encode clause).bits)
def input (formula : EncodedCNF) := FieldList.stream (fields formula)
def budget (formula : EncodedCNF) := RecoveryFormulaFrame.budget (fields formula)

theorem exact_code (formula : EncodedCNF) : PCPTraversal.code (fields formula)=balancedCNFPayload formula := by
  have hf : fields formula=(formula.map Encodable.encode).map Nat.bits := by simp [fields]
  rw [hf,PCPTripleNative.code_values]
  rfl

theorem formula_runs (oracle : Nat→Bool) (formula : EncodedCNF) :
    OrdinaryOracleRuns oracle program (input formula) (balancedCNFPayload formula).bits (budget formula) := by
  have h := field_runs oracle (fields formula)
  rw [exact_code] at h
  exact h

noncomputable def wordFunction (oracle : Nat→Bool) : OrdinaryOracleWordFunction oracle EncodedCNF
    input (fun formula=>(balancedCNFPayload formula).bits) budget where
  program := program
  realizes := formula_runs oracle

end NearCubicWires.RepairSource.RecoveryFormulaPayload
