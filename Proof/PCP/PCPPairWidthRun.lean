import Proof.PCP.PCPPairWidth

/-! Whole cold width producer, including both delimiters and a paid rewind. -/
namespace NearCubicWires.RepairOrdinary.PCPPairWidth
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem end_step (left : Bool) (pre other out : List Bool) (otherPos : ℕ) :
    step raw (cfg left (scanState left) (pre++[false]) other pre.length otherPos out)=some
      (cfg left (if left then 2 else 4) (pre++[false]) other pre.length otherPos (out++[true])) := by
  cases left <;> simp [step,raw,cfg,scanState,Configuration.scanned,Streaming.read_append]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

private theorem frame_end (bits : List Bool) : Streaming.marks bits++[false]=frame bits := by
  simpa [frame] using (Streaming.frame_append bits []).symm

theorem raw_run (left right : List Bool) :
    ∃ r : ExecutionReceipt 3 5,
      run raw (PCPPair.width left right) ![frame left,frame right,[]]=some r ∧
      r.final.tapes=![frame left,frame right,List.replicate (PCPPair.width left right) true] ∧
      r.steps=PCPPair.width left right := by
  have hl := scan_prefix true left [] (frame right) [] 0
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hl
  have hle := end_step true (Streaming.marks left) (frame right)
    (List.replicate (2*left.length) true) 0
  rw [frame_end,Streaming.marks_length] at hle
  let first := List.replicate (2*left.length) true++[true]
  have hr := scan_prefix false right [] (frame left) first (2*left.length)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr
  have hre := end_step false (Streaming.marks right) (frame left)
    (first++List.replicate (2*right.length) true) (2*left.length)
  rw [frame_end,Streaming.marks_length] at hre
  have h := hl.trans ((Timed.single (by rfl) hle).trans
    (hr.trans (Timed.single (by rfl) hre)))
  have he : 2*left.length+(1+(2*right.length+1))=PCPPair.width left right := by
    unfold PCPPair.width
    omega
  rw [he] at h
  have hi : cfg true (scanState true) (frame left) (frame right) 0 0 []=
      initialConfiguration raw ![frame left,frame right,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at h
  obtain ⟨r,hrun,hf,hs⟩ := h.run (by rfl)
  refine ⟨r,hrun,?_,hs⟩
  rw [hf]
  have hout : first++List.replicate (2*right.length) true++[true]=
      List.replicate (PCPPair.width left right) true := by
    dsimp only [first]
    rw [show [true]=List.replicate 1 true from rfl,←List.replicate_add,←List.replicate_add,←List.replicate_add]
    congr 1
    unfold PCPPair.width
    omega
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact hout

def machine : Machine 4 7 := Rewind.machine raw

theorem width_run (left right : List Bool) :
    ClockJoin.ReadyRun machine (2*PCPPair.width left right+2)
      ![frame left,frame right,[],[]]
      ![frame left,frame right,List.replicate (PCPPair.width left right) true,
        List.replicate (PCPPair.width left right) false] := by
  obtain ⟨base,hbase,htapes,hs⟩ := raw_run left right
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  have he : 2*base.steps+2=2*PCPPair.width left right+2 := by omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.le.trans_eq he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · exact (ht 0).trans (congrFun htapes 0)
    · exact (ht 1).trans (congrFun htapes 1)
    · exact (ht 2).trans (congrFun htapes 2)
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.PCPPairWidth
