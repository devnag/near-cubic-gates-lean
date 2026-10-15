import Proof.Amplification.RecoveryFormulaCount

/-! The serializer count is now produced from its literal external field
stream, including both empty cases and a physical all-head rewind. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaCount
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem finish (pre tail : List Bool) (count : Nat) :
    step raw (cfg 1 (pre++false::tail) pre.length count)=
      some (cfg 5 (pre++false::tail) pre.length count) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

def source (fields : List (List Bool)) := frame (FieldList.stream fields)
def rawBudget (fields : List (List Bool)) := 2*(FieldList.stream fields).length+2

theorem whole_trace (fields : List (List Bool)) :
    Timed raw (rawBudget fields) (initialConfiguration raw ![source fields,[]])
      (cfg 5 (source fields) (2*(FieldList.stream fields).length) fields.length) := by
  have hbody := fields_trace fields [] [false] 0
  have hsource : Streaming.marks (FieldList.stream fields)++[false]=source fields :=
    (RecoveryPrefixMeasure.frame_marks _).symm
  simp only [List.nil_append,List.length_nil,Nat.zero_add,hsource] at hbody
  have hfinish := finish (Streaming.marks (FieldList.stream fields)) [] fields.length
  simp only [Streaming.marks_length,hsource] at hfinish
  have hlast := (Timed.single (by rfl) (boot (source fields))).trans
    (hbody.trans (Timed.single (by rfl) hfinish))
  rw [show 1+(2*(FieldList.stream fields).length+1)=rawBudget fields by unfold rawBudget; omega] at hlast
  exact hlast

theorem raw_run (fields : List (List Bool)) : ∃ r,
    run raw (rawBudget fields) ![source fields,[]]=some r ∧
      r.final.tapes=![source fields,VerifierDecoding.CompareMachine.word fields.length] ∧
      r.steps=rawBudget fields := by
  obtain ⟨r,hr,hf,hs⟩ := (whole_trace fields).run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def machine := Rewind.machine raw
def budget (fields : List (List Bool)) := 4*(FieldList.stream fields).length+6

theorem ready (fields : List (List Bool)) :
    ClockJoin.ReadyRun machine (budget fields) ![source fields,[],[]]
      ![source fields,VerifierDecoding.CompareMachine.word fields.length,
        List.replicate (rawBudget fields) false] := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run fields
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw (rawBudget fields)
    ![source fields,[]] base hbase 0
  have he : 2*base.steps+2=budget fields := by rw [hbs]; simp [rawBudget,budget]; omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,by omega⟩
  · convert hr using 2 <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt] using ht 0
    · simpa [hbt] using ht 1
    · simpa [hbs] using hcounter

end NearCubicWires.RepairSource.RecoveryFormulaCount
