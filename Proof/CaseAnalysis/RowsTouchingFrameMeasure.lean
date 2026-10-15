import Proof.CaseAnalysis.RowsTouchingPascalTable
import Proof.MachineModel.FrameSkip

/-! Measure the actual bytes of a counted framed stream with the existing
marker scanner and counted loop. This obtains the row-width unary driver
from the produced row, avoiding a separate arithmetic product producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameMeasure
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsFamilyLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsDegreeLoop.machine FrameSkipMark.machine
def budget (w n : ℕ):=n*(2*w+4)+3
theorem marks (words : List (List Bool)):
    words.flatMap (fun bits=>List.replicate (frame bits).length true)=List.replicate (words.flatMap frame).length true:=by
  induction words with
  | nil=>rfl
  | cons bits words ih=>simp only [List.flatMap_cons,List.length_append,List.replicate_add,ih]

def entry (words : List (List Bool)) (pre tail : List Bool) (j : ℕ) (out : List Bool):=
  FrameSkipMark.cfg 0 (pre++words.flatMap frame++tail)
    (pre.length+((words.take j).flatMap frame).length) out.length

theorem measure_run (words : List (List Bool)) (pre tail : List Bool) (w : ℕ)
    (hw:∀ bits∈words,bits.length≤w):
    ∃ r,runFrom machine (budget w words.length)
      (RepeatMachine.cfg 0 (entry words pre tail 0 []) words.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (entry words pre tail words.length (List.replicate (words.flatMap frame).length true)) words.length 1 ∧
      r.steps≤budget w words.length:=by
  let source:=entry words pre tail
  let emit:=fun j=>List.replicate (frame (words.getD j [])).length true
  have supplier:∀ j<words.length,∀ out,∃ r,runFrom FrameSkipMark.machine (2*w+1) (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤2*w+1:=by
    intro j hj out
    let bits:=words.getD j []
    have mem:bits∈words:=by dsimp only [bits];rw [List.getD_eq_getElem words [] hj];exact List.getElem_mem hj
    let lp:=pre++(words.take j).flatMap frame
    let rt:=(words.drop (j+1)).flatMap frame++tail
    have split:lp++frame bits++rt=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [lp,rt,bits,List.append_assoc]
    obtain ⟨r,run,rf,rs⟩:=FrameSkipMark.skip_run lp bits rt out.length
    have more:=runFrom_moreFuel FrameSkipMark.machine _ (2*w+1-(2*bits.length+1)) _ r run
    have fit:2*bits.length+1≤2*w+1:=by have h:=hw bits mem;omega
    rw [Nat.add_sub_of_le fit] at more
    rw [split] at more rf
    refine ⟨r,?_,?_,?_,rs.le.trans fit⟩
    · simpa only [source,entry,lp,List.length_append] using more
    · rw [rf]
      simp only [source,entry,FrameSkipMark.cfg,next_word words [] frame j hj,lp,List.length_append,
        emit,bits,List.length_replicate,Nat.add_assoc]
    · rw [rf]
      simp only [source,entry,FrameSkipMark.cfg,emit,bits,List.length_append,List.length_replicate]
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run FrameSkipMark.machine source emit (2*w+1)
    words.length (by intro j hj out;rfl) supplier []
  have emitted:(List.range words.length).flatMap emit=List.replicate (words.flatMap frame).length true:=by
    rw [flatMap_index words [] (fun bits=>List.replicate (frame bits).length true)]
    exact marks words
  rw [emitted,List.nil_append] at rf
  rw [show 2*w+1+3=2*w+4 by omega] at run rs
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameMeasure
