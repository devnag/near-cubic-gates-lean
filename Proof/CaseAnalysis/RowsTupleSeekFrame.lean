import Proof.CaseAnalysis.RowsTouchingFrameStream
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.Runs

/-! The shared seek copies or skips an original framed field without
interpreting its payload. Both modes consume exactly the same source bytes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (keep : Bool) (bits : List Bool) := if keep then bits else []
def frameMachine (keep : Bool) : Machine 2 3 :=
  if keep then CloseoutRowsTouching.FrameStream.machine else TapeEmbedding.machine 1 FrameSkip.machine
def fieldHeads (pos : ℕ) (out : List Bool) : Fin 2→ℕ := ![pos,out.length]
def fieldData (source out : List Bool) : Fin 2→List Bool := ![source,out]

theorem frame_run (keep : Bool) (pre bits tail out : List Bool) :
    Step (frameMachine keep) (2*bits.length+1) (fieldHeads pre.length out)
      (fieldData (pre++frame bits++tail) out)
      (fieldHeads (pre.length+(frame bits).length) (out++selected keep (frame bits)))
      (fieldData (pre++frame bits++tail) (out++selected keep (frame bits))) := by
  cases keep
  · obtain ⟨r,hr,rf,rs⟩ := FrameSkip.skip_run pre bits tail
    have raw : Step FrameSkip.machine (2*bits.length+1) (fun _=>pre.length)
        (fun _=>pre++frame bits++tail) (fun _=>pre.length+(frame bits).length)
        (fun _=>pre++frame bits++tail) :=
      ⟨r,hr,by rw [rf];rfl,by rw [rf];rfl,rs.le⟩
    have h := raw.embed (fun _ : Fin 1=>out.length) (fun _ : Fin 1=>out)
    simpa only [frameMachine,selected,Bool.false_eq_true,↓reduceIte,List.append_nil]
      using h.congr_in (by funext i;fin_cases i <;> rfl)
        (by funext i;fin_cases i <;> rfl) |>.congr
        (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
  · obtain ⟨r,hr,rf,_⟩ := CloseoutRowsTouching.FrameStream.copy_run pre bits tail out
    refine Step.of_run hr ?_ ?_
    · rw [rf]
      simp only [selected,↓reduceIte,fieldHeads,CloseoutRowsTouching.FrameStream.cfg,
        frame_length',Nat.add_assoc]
    · rw [rf];rfl

def threeFrames (keep : Bool) :=
  Composition.machine (Composition.machine (frameMachine keep) (frameMachine keep)) (frameMachine keep)
def record (a b c : List Bool) := frame a++frame b++frame c

theorem three_run (keep : Bool) (pre a b c tail out : List Bool) :
    Step (threeFrames keep) ((record a b c).length+2) (fieldHeads pre.length out)
      (fieldData (pre++record a b c++tail) out)
      (fieldHeads (pre.length+(record a b c).length) (out++selected keep (record a b c)))
      (fieldData (pre++record a b c++tail) (out++selected keep (record a b c))) := by
  have first := frame_run keep pre a (frame b++frame c++tail) out
  have second := frame_run keep (pre++frame a) b (frame c++tail) (out++selected keep (frame a))
  have third := frame_run keep (pre++frame a++frame b) c tail
    ((out++selected keep (frame a))++selected keep (frame b))
  simp only [List.length_append,List.append_assoc,Nat.add_assoc] at first second third
  have all := (first.seq second).seq third
  have time : (2*a.length+1)+1+(2*b.length+1)+1+(2*c.length+1)=(record a b c).length+2 := by
    simp only [record,List.length_append,frame_length'];omega
  rw [time] at all
  cases keep <;> simpa only [threeFrames,record,List.length_append,List.append_assoc,
    selected,Bool.false_eq_true,↓reduceIte,List.append_nil,Nat.add_assoc] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
