import Proof.CaseAnalysis.RowsTouchingPascalMeaning
import Proof.CaseAnalysis.RowsTouchingFrameStream
import Proof.MachineModel.Runs

/-! One complete Pascal transition copies its existing leading one and
runs the q exact additions. The input rows remain untouched, and the new
row appends to the same complete table prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalNext
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch SignedSortKey
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=RecoveryFocus.machine (![1,2] : Fin 2→Fin 4) FrameStream.machine
noncomputable def machine:=Composition.machine first PascalRow.machine
def budget (q : ℕ):=2*(q+1)+2+PascalRow.budget (q+1) q

theorem next_run (q m : ℕ) (out : List Bool) (hm:m<q):
    ∃ r,runFrom machine (budget q)
      ⟨machine.start,![0,0,out.length,1],
        ![PascalRow.row (q+1) m q,PascalRow.row (q+1) m q,out,CompareMachine.word q]⟩=some r ∧
      r.steps≤budget q ∧
      r.final.heads=![q*(2*(q+1)+1),(q+1)*(2*(q+1)+1),(out++PascalRow.row (q+1) (m+1) q).length,1] ∧
      r.final.tapes=![PascalRow.row (q+1) m q,PascalRow.row (q+1) m q,
        out++PascalRow.row (q+1) (m+1) q,CompareMachine.word q]:=by
  let w:=q+1
  let oldRow:=PascalRow.row w m q
  let pairs:=PascalRow.pairs m q
  let one:=PascalRow.field w 1
  have pr:pairs.length=q:=by simp [pairs,PascalRow.pairs]
  have leftSplit:oldRow=pairs.flatMap (PascalRow.leftWord w)++PascalRow.field w (Nat.choose m q):=
    PascalRow.left_row w m q
  have rightSplit:oldRow=one++pairs.flatMap (PascalRow.rightWord w):=PascalRow.right_row w m q
  have sumSplit:PascalRow.row w (m+1) q=one++pairs.flatMap (PascalRow.sumWord w):=PascalRow.next_row w m q
  obtain ⟨copied,copyRun,cf,cs⟩:=FrameStream.copy_run [] (binary w 1) (pairs.flatMap (PascalRow.rightWord w)) out
  have copyStep:Step FrameStream.machine (2*w+1) ![0,out.length] ![oldRow,out]
      ![2*w+1,(out++one).length] ![oldRow,out++one]:=by
    rw [rightSplit]
    refine Step.of_run (r:=copied) ?_ ?_ ?_
    · simpa only [List.nil_append,List.length_nil,binary_length,Nat.zero_add,FrameStream.cfg,FrameStream.machine,one,PascalRow.field] using copyRun
    · rw [cf];simp only [FrameStream.cfg,List.length_nil,Nat.zero_add,binary_length];rfl
    · rw [cf];simp only [FrameStream.cfg,List.nil_append];rfl
  have focused:=copyStep.focus (![1,2] : Fin 2→Fin 4) (by decide)
    (![0,0,out.length,1] : Fin 4→ℕ) ![oldRow,oldRow,out,CompareMachine.word q]
  have inputHeads:dockH (![1,2] : Fin 2→Fin 4) ![0,0,out.length,1] ![0,out.length]=![0,0,out.length,1]:=by
    funext i;fin_cases i <;> first | rfl | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1
  have inputTapes:install (![1,2] : Fin 2→Fin 4) ![oldRow,oldRow,out,CompareMachine.word q] ![oldRow,out]=
      ![oldRow,oldRow,out,CompareMachine.word q]:=by
    funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1
  have outputHeads:dockH (![1,2] : Fin 2→Fin 4) ![0,0,out.length,1] ![2*w+1,(out++one).length]=
      ![0,2*w+1,(out++one).length,1]:=by
    funext i;fin_cases i <;> first | rfl | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1
  have outputTapes:install (![1,2] : Fin 2→Fin 4) ![oldRow,oldRow,out,CompareMachine.word q] ![oldRow,out++one]=
      ![oldRow,oldRow,out++one,CompareMachine.word q]:=by
    funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1
  obtain ⟨a,ar,ah,atapes,asteps⟩:=focused.congr_in inputHeads inputTapes |>.congr outputHeads outputTapes
  obtain ⟨b,br,bf,bsteps⟩:=PascalRow.row_run w pairs [] one (PascalRow.field w (Nat.choose m q)) [] (out++one)
    (PascalRow.pairs_fit q m hm)
  rw [pr] at br bf bsteps
  have inputRowHeads:(RepeatMachine.cfg 0
      (PascalRow.entry w pairs [] one (PascalRow.field w (Nat.choose m q)) [] 0 (out++one)) q 1).heads=
      ![0,2*w+1,(out++one).length,1]:=by
    simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PascalRow.entry,List.take_zero,List.flatMap_nil,
      List.length_nil,Nat.add_zero,List.length_append,one,PascalRow.field,frame_length,binary_length]
    funext i;fin_cases i <;> rfl
  have inputRowTapes:(RepeatMachine.cfg 0
      (PascalRow.entry w pairs [] one (PascalRow.field w (Nat.choose m q)) [] 0 (out++one)) q 1).tapes=
      ![oldRow,oldRow,out++one,CompareMachine.word q]:=by
    simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PascalRow.entry,List.nil_append,List.append_nil]
    rw [←leftSplit,←rightSplit]
    funext i;fin_cases i <;> rfl
  have next:runFrom PascalRow.machine (PascalRow.budget w q)
      ⟨PascalRow.machine.start,a.final.heads,a.final.tapes⟩=some b:=by
    rw [ah,atapes,←inputRowHeads,←inputRowTapes]
    exact br
  obtain ⟨r,run,rs,rh,rt⟩:=joined first PascalRow.machine (2*w+1) (PascalRow.budget w q)
    ![0,0,out.length,1] ![oldRow,oldRow,out,CompareMachine.word q] a b ar next asteps bsteps
  have leftLen:(pairs.flatMap (PascalRow.leftWord w)).length=q*(2*w+1):=by
    have h:oldRow.length=(q+1)*(2*w+1):=PascalRow.row_length w m q
    rw [leftSplit,List.length_append] at h
    simp only [PascalRow.field,frame_length,binary_length] at h
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  have rightLen:(pairs.flatMap (PascalRow.rightWord w)).length=q*(2*w+1):=by
    have h:oldRow.length=(q+1)*(2*w+1):=PascalRow.row_length w m q
    rw [rightSplit,List.length_append] at h
    simp only [one,PascalRow.field,frame_length,binary_length] at h
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  have takeAll:pairs.take q=pairs:=by rw [←pr,List.take_length]
  refine ⟨r,run,rs,?_,?_⟩
  · rw [rh,bf]
    simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PascalRow.entry,takeAll,
      List.length_nil,Nat.zero_add,leftLen,rightLen]
    rw [List.append_assoc,←sumSplit]
    have hOne:one.length=2*w+1:=by simp [one,PascalRow.field]
    rw [hOne]
    have hMul:2*w+1+q*(2*w+1)=(q+1)*(2*w+1):=by rw [Nat.add_mul,Nat.one_mul];omega
    rw [hMul]
    funext i;fin_cases i <;> rfl
  · rw [rt,bf]
    simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PascalRow.entry,List.nil_append,List.append_nil]
    rw [←leftSplit,←rightSplit,List.append_assoc,←sumSplit]
    funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalNext
