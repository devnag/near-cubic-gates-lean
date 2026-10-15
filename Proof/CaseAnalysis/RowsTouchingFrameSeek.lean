import Proof.CaseAnalysis.RowsTouchingFrameMeasure

/-! A paid counted scan of framed fields. This is the existing one-tape
frame skipper under the existing DegreeLoop, with no address arithmetic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameSeek
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsFamilyLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsDegreeLoop.machine FrameSkip.machine
def budget (w n : ℕ):=n*(2*w+4)+3
def entry (words : List (List Bool)) (pre tail : List Bool) (j : ℕ) (_out : List Bool):=
  FrameSkip.cfg 0 (pre++words.flatMap frame++tail) (pre.length+((words.take j).flatMap frame).length)

theorem seek_run (words : List (List Bool)) (pre tail : List Bool) (w : ℕ)
    (hw:∀ bits∈words,bits.length≤w):
    ∃ r,runFrom machine (budget w words.length)
      (RepeatMachine.cfg 0 (entry words pre tail 0 []) words.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry words pre tail words.length []) words.length 1 ∧
      r.steps≤budget w words.length:=by
  let source:=entry words pre tail
  have supplier:∀ j<words.length,∀ out,∃ r,runFrom FrameSkip.machine (2*w+1) (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++[])).heads ∧
      r.final.tapes=(source (j+1) (out++[])).tapes ∧ r.steps≤2*w+1:=by
    intro j hj out
    let bits:=words.getD j []
    have mem:bits∈words:=by dsimp only [bits];rw [List.getD_eq_getElem words [] hj];exact List.getElem_mem hj
    let lp:=pre++(words.take j).flatMap frame
    let rt:=(words.drop (j+1)).flatMap frame++tail
    have split:lp++frame bits++rt=pre++words.flatMap frame++tail:=by
      rw [split_word words [] frame j hj]
      simp only [lp,rt,bits,List.append_assoc]
    obtain ⟨r,run,rf,rs⟩:=FrameSkip.skip_run lp bits rt
    have more:=runFrom_moreFuel FrameSkip.machine _ (2*w+1-(2*bits.length+1)) _ r run
    have fit:2*bits.length+1≤2*w+1:=by have h:=hw bits mem;omega
    rw [Nat.add_sub_of_le fit,split] at more
    rw [split] at rf
    refine ⟨r,?_,?_,?_,rs.le.trans fit⟩
    · simpa only [source,entry,lp,List.length_append] using more
    · rw [rf]
      simp only [source,entry,FrameSkip.cfg,next_word words [] frame j hj,lp,List.length_append,bits,Nat.add_assoc]
    · rw [rf];rfl
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run FrameSkip.machine source (fun _=>[]) (2*w+1)
    words.length (by intro j hj out;rfl) supplier []
  have emitted:(List.range words.length).flatMap (fun _ : ℕ=>([] : List Bool))=[]:=by simp
  rw [emitted,List.nil_append] at rf
  rw [show 2*w+1+3=2*w+4 by omega] at run rs
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameSeek
