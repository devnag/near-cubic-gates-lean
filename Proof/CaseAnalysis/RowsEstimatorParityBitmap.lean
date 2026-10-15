import Proof.CaseAnalysis.RowsEstimatorParityFragment

/-! Cache the paper's bitmap weights and support once, with a recorded logical reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Bitmap
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def strokes : List (Stroke 2):=
  [![some (fun _=>true),some (fun _=>true)],
   ![some (fun _=>false),some id],
   ![some (fun _=>true),none],
   ![some (fun _=>true),none],
   ![some (fun _=>true),none],
   ![some (fun _=>false),none],
   ![some (fun _=>true),none],
   ![some id,none]]
def stopStrokes : List (Stroke 2):=[![some (fun _=>false),some (fun _=>false)]]
noncomputable def appendStop:=TapeEmbedding.machine 1 (Glyph.machine stopStrokes)
noncomputable def raw:=Composition.machine (Scan.machine strokes) appendStop
noncomputable def machine:=MaskedReset.machine raw (fun i=>decide (i≠3))
def input (bits tail : List Bool) : Fin 4→List Bool:=![bits++tail,[],[],CompareMachine.word bits.length]
def head : Fin 4→ℕ:=![0,0,0,1]
def result (bits tail : List Bool) : Fin 4→List Bool:=
  ![bits++tail,frame (weights bits),frame bits,CompareMachine.word bits.length]
def finalHeads (bits : List Bool) : Fin 4→ℕ:=![bits.length,(frame (weights bits)).length,(frame bits).length,1]

theorem word_exact (b : Bool) :
    (fun i=>word strokes b i)=![Fragment.body (bitWeight b),[true,b]] := by
  funext i;fin_cases i <;>rfl

theorem cache_exact (bits : List Bool) :
    (fun i=>bits.flatMap (fun b=>word strokes b i))=![Fragment.body (weights bits),Fragment.body bits] := by
  funext i;fin_cases i
  · simp only [weights,Fragment.body,List.flatMap_assoc]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro b _
    exact congrFun (word_exact b) 0
  · rfl

theorem raw_run (bits tail : List Bool) :
    Step raw (21*bits.length+6) head (input bits tail) (finalHeads bits) (result bits tail) := by
  have first:=Scan.scan_run strokes [] bits tail (fun _ : Fin 2=>[])
  have last:=(word_run stopStrokes (readTapeBit (bits++tail) bits.length) (bits++tail) bits.length
    (![Fragment.body (weights bits),Fragment.body bits]) rfl).embed
      (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word bits.length)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at first
  rw [cache_exact bits] at first
  have whole:=first.seq last
  have ht:bits.length*(2*strokes.length+5)+3+1+2*stopStrokes.length=21*bits.length+6:=by
    simp only [strokes,stopStrokes,List.length_cons,List.length_nil]
    omega
  rw [ht] at whole
  apply whole.congr_in ?_ ?_ |>.congr ?_ ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i
    · rfl
    · change (Fragment.body (weights bits)++[false]).length=(frame (weights bits)).length
      rw [Fragment.frame_eq]
    · change (Fragment.body bits++[false]).length=(frame bits).length
      rw [Fragment.frame_eq]
    · rfl
  · funext i;fin_cases i
    · rfl
    · exact (Fragment.frame_eq (weights bits)).symm
    · exact (Fragment.frame_eq bits).symm
    · rfl

theorem cache_run (bits tail : List Bool) : ∃ n, n≤21*bits.length+6 ∧
    Step machine (42*bits.length+14) (![0,0,0,1,0])
      (![bits++tail,[],[],CompareMachine.word bits.length,[]])
      (![0,0,0,1,0]) (![bits++tail,frame (weights bits),frame bits,CompareMachine.word bits.length,List.replicate n false]) := by
  obtain ⟨base,hb,bh,bt,bs⟩:=raw_run bits tail
  have bound : ∀ i,decide (i≠(3 : Fin 4))=true →base.final.heads i≤base.steps:=by
    intro i hi
    have h:=SelectiveReset.prefix_head (prefix_of_run raw _ _ base hb).1 i
    have hz:head i=0:=by fin_cases i <;> simp_all [head]
    simpa only [hz,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.reset_run raw (fun i=>decide (i≠3)) _ _ base hb bound
  have actual:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  refine ⟨base.steps,bs,?_⟩
  have final:=actual.enlarge (show 2*base.steps+2≤42*bits.length+14 by omega)
  apply final.congr_in ?_ ?_ |>.congr ?_ ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;> simp [Fin.addCases,SelectiveReset.finished,Rewind.config,bh,finalHeads]
  · funext i;fin_cases i <;> simp [Fin.addCases,SelectiveReset.finished,Rewind.config,bt,result]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Bitmap
