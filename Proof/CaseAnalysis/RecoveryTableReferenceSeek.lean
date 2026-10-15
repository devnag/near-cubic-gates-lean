import Proof.CaseAnalysis.RecoveryUniversalNodeRun
import Proof.MachineModel.OrdinaryMatrixScoreSkipFields

/-! The original table's prior-count driver locates the end of its actual
framed live-reference stream. Reuse the checked counted field scanner;
neither a maintained stream-length field nor a graph-count prepass is needed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceSeek
open LocalBitMultitape RepairRepresentation
open RepairSource.VerifierDecoding RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MatrixScoreSkipFields.machine
def budget (refs : List ℕ):=(sourceWord refs).length+3*refs.length+3

theorem driver_run (total pos : ℕ) (refs : List ℕ) (pre tail : List Bool)
    (hpos : pos+refs.length=total) :
    ∃ r,runFrom machine ((sourceWord refs).length+2*refs.length+total+3)
      (RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
        (pre++sourceWord refs++tail) pre.length) total (pos+1))=some r ∧
      r.steps ≤ (sourceWord refs).length+2*refs.length+total+3 ∧
      r.final=RepeatMachine.cfg 3 (MatrixScoreSkipField.cfg 0
        (pre++sourceWord refs++tail) (pre.length+(sourceWord refs).length)) total 1 := by
  induction refs generalizing pos pre with
  | nil =>
    have hp : pos=total:=by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩:=(RepeatMachine.exhaust MatrixScoreSkipField.machine MatrixScoreSkipFields.accepted
      (MatrixScoreSkipField.cfg 0 (pre++sourceWord []++tail) pre.length) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa [machine,MatrixScoreSkipFields.machine,sourceWord] using hr,
      by simpa [sourceWord] using hs.le,by simpa [sourceWord] using hf⟩
  | cons ref refs ih =>
    let field:=frame (List.replicate ref true)
    obtain ⟨body,hbody,hbf,hbs⟩:=MatrixScoreSkipField.field_run (List.replicate ref true) pre (sourceWord refs++tail)
    have iteration:=RepeatMachine.iteration MatrixScoreSkipField.machine MatrixScoreSkipFields.accepted
      (MatrixScoreSkipField.cfg 0 (pre++field++(sourceWord refs++tail)) pre.length)
      total pos body rfl (by simp only [List.length_cons] at hpos;omega) hbody
    simp only [MatrixScoreSkipFields.accepted,if_true] at iteration
    rw [hbf] at iteration
    have he : RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 2
        (pre++field++(sourceWord refs++tail)) (pre.length+field.length)) total (pos+2)=
      RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
        ((pre++field)++sourceWord refs++tail) (pre++field).length) total (pos+2) := by
      simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixScoreSkipField.cfg,List.append_assoc]
    rw [he] at iteration
    obtain ⟨rest,hr,hs,hf⟩:=ih (pos+1) (pre++field) (by simp only [List.length_cons] at hpos;omega)
    have hr' : runFrom machine ((sourceWord refs).length+2*refs.length+total+3)
        (RepeatMachine.cfg 0 (MatrixScoreSkipField.cfg 0
          ((pre++field)++sourceWord refs++tail) (pre++field).length) total (pos+2))=some rest := by
      simpa only [Nat.add_assoc] using hr
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,rr,rf,rs,_⟩:=hprefix.followedBy rest hr'
    have hc : (body.steps+2)+((sourceWord refs).length+2*refs.length+total+3)=
        (sourceWord (ref::refs)).length+2*(ref::refs).length+total+3 := by
      rw [hbs]
      simp only [sourceWord,List.flatMap_cons,List.length_append,frame_length,List.length_replicate,List.length_cons]
      omega
    rw [hc] at rr
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,MatrixScoreSkipFields.machine,sourceWord,List.flatMap_cons,field,List.append_assoc] using rr
    · rw [rs]
      omega
    · rw [rf,hf]
      simp only [sourceWord,List.flatMap_cons,field,List.length_append,List.append_assoc,Nat.add_assoc]

noncomputable def cfg (phase : Fin 5) (refs : List ℕ) (tail : List Bool) (pos : ℕ):=
  RepeatMachine.cfg phase (MatrixScoreSkipField.cfg 0 (sourceWord refs++tail) pos) refs.length 1

theorem seek_run (refs : List ℕ) (tail : List Bool) :
    ∃ r,runFrom machine (budget refs) (cfg 0 refs tail 0)=some r ∧
      r.steps ≤ budget refs ∧ r.final=cfg 3 refs tail (sourceWord refs).length := by
  obtain ⟨r,hr,hs,hf⟩:=driver_run refs.length 0 refs [] tail (by omega)
  have he : (sourceWord refs).length+2*refs.length+refs.length+3=budget refs := by unfold budget;omega
  rw [he] at hr hs
  exact ⟨r,by simpa only [cfg,List.nil_append,List.length_nil,Nat.zero_add] using hr,hs,
    by simpa only [cfg,List.nil_append,List.length_nil,Nat.zero_add] using hf⟩

theorem cfg_heads (phase : Fin 5) (refs : List ℕ) (tail : List Bool) (pos : ℕ) :
    (cfg phase refs tail pos).heads=![pos,1] := by
  funext i
  fin_cases i <;> rfl
theorem cfg_tapes (phase : Fin 5) (refs : List ℕ) (tail : List Bool) (pos : ℕ) :
    (cfg phase refs tail pos).tapes=![sourceWord refs++tail,CompareMachine.word refs.length] := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceSeek
