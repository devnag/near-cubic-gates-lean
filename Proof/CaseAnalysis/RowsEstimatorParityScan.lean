import Proof.CaseAnalysis.RowsEstimatorParityWords

/-! A retained unary arity driver copies exactly the bitmap's logical bits into native byte streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Scan
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
open Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def direction (t : ℕ) (d : HeadMove) : Fin (t+1)→HeadMove:=Fin.cases d (fun _=>.stay)
noncomputable def body {t : ℕ} (fs : List (Stroke t)):=
  Composition.machine (Glyph.machine fs) (DecompositionCountPosition.move (direction t .right))
noncomputable def machine {t : ℕ} (fs : List (Stroke t)):=CloseoutRowsDegreeLoop.machine (body fs)
def emittedPrefix {t : ℕ} (fs : List (Stroke t)) (bits : List Bool) (j : ℕ) (out : Fin t→List Bool) :=
  fun i=>out i++(bits.take j).flatMap (fun b=>word fs b i)
noncomputable def entry {t : ℕ} (fs : List (Stroke t)) (pre bits tail : List Bool)
    (out : Fin t→List Bool) (j : ℕ) (_unused : List Bool):=
  cfg (body fs).start (pre++bits++tail) (pre.length+j) (emittedPrefix fs bits j out)

theorem advance {t : ℕ} (source : List Bool) (pos : ℕ) (out : Fin t→List Bool) :
    Step (DecompositionCountPosition.move (direction t .right)) 1
      (heads pos out) (data source out) (heads (pos+1) out) (data source out) := by
  obtain ⟨r,hr,rf,_⟩:=DecompositionCountPosition.move_run (direction t .right) (heads pos out) (data source out)
  refine Step.of_run hr ?_ (by rw [rf])
  rw [rf]
  funext i
  refine Fin.cases rfl (fun _=>rfl) i

theorem bit_read (pre bits tail : List Bool) (j : ℕ) (hj : j<bits.length) :
    readTapeBit (pre++bits++tail) (pre.length+j)=bits[j] := by
  rw [List.append_assoc]
  simp only [readTapeBit,List.getD]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hj,List.getElem?_eq_getElem hj]
  rfl

theorem prefix_succ {t : ℕ} (fs : List (Stroke t)) (bits : List Bool) (j : ℕ)
    (out : Fin t→List Bool) (hj : j<bits.length) :
    emittedPrefix fs bits (j+1) out=fun i=>emittedPrefix fs bits j out i++word fs bits[j] i := by
  funext i
  simp only [emittedPrefix,List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc]

theorem scan_run {t : ℕ} (fs : List (Stroke t)) (pre bits tail : List Bool) (out : Fin t→List Bool) :
    Step (machine fs) (bits.length*(2*fs.length+5)+3)
      (Fin.addCases (heads pre.length out) (fun _ : Fin 1=>1))
      (Fin.addCases (data (pre++bits++tail) out) (fun _ : Fin 1=>CompareMachine.word bits.length))
      (Fin.addCases (heads (pre.length+bits.length) (fun i=>out i++bits.flatMap (fun b=>word fs b i)))
        (fun _ : Fin 1=>1))
      (Fin.addCases (data (pre++bits++tail) (fun i=>out i++bits.flatMap (fun b=>word fs b i)))
        (fun _ : Fin 1=>CompareMachine.word bits.length)) := by
  have supplier : ∀ j<bits.length,∀ acc,∃ r,
      runFrom (body fs) (2*fs.length+2) (entry fs pre bits tail out j acc)=some r ∧
      r.final.heads=(entry fs pre bits tail out (j+1) (acc++[])).heads ∧
      r.final.tapes=(entry fs pre bits tail out (j+1) (acc++[])).tapes ∧r.steps≤2*fs.length+2:=by
    intro j hj acc
    have h:=(word_run fs bits[j] (pre++bits++tail) (pre.length+j) (emittedPrefix fs bits j out)
      (bit_read pre bits tail j hj)).seq (advance (pre++bits++tail) (pre.length+j)
        (fun i=>emittedPrefix fs bits j out i++word fs bits[j] i))
    rw [show 2*fs.length+1+1=2*fs.length+2 by omega] at h
    simpa only [Step,body,entry,cfg,prefix_succ fs bits j out hj,Nat.add_assoc] using h
  obtain ⟨r,hr,rf,_⟩:=CloseoutRowsDegreeLoop.loop_run (body fs)
    (entry fs pre bits tail out) (fun _=>[]) (2*fs.length+2) bits.length (by intros;rfl) supplier []
  have h:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have h0:emittedPrefix fs bits 0 out=out:=by funext i;simp [emittedPrefix]
  have hn:emittedPrefix fs bits bits.length out=(fun i=>out i++bits.flatMap (fun b=>word fs b i)):=by
    funext i;simp [emittedPrefix]
  simpa [machine,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,entry,cfg,h0,hn,Nat.add_assoc] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Scan
