import Proof.Amplification.RecoveryFixedWidth
import Proof.PCP.VerifierDecodingField
import Proof.PCP.VerifierDecodingLength

/-! Reuse the accepted ordinary decoder field copier. A paid initial move
positions its width sentinel; an executed rewind restores source, output,
width and reusable reset-workspace heads. No canonical trimming is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFieldCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positionMachine : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1, fun _ => none, ![.stay, .stay, .right]⟩ else none

def rawMachine : Machine 3 8 := Composition.machine positionMachine FieldMachine.machine

def machine : Machine 4 10 := Rewind.machine rawMachine

theorem raw_run (bits tail backing : List Bool) (hb : backing.length ≤ 2 * bits.length + 1) :
    let source := Streaming.marks bits ++ tail
    ∃ r : ExecutionReceipt 3 8,
      run rawMachine (4 * bits.length + 4) ![source, backing, CompareMachine.word bits.length] = some r ∧
      r.final.tapes = ![source, frame bits, CompareMachine.word bits.length] ∧
      r.steps = 4 * bits.length + 4 := by
  let source := Streaming.marks bits ++ tail
  let final : Configuration 3 2 := ⟨1, ![0, 0, 1], ![source, backing, CompareMachine.word bits.length]⟩
  have hstep : step positionMachine
      (initialConfiguration positionMachine ![source, backing, CompareMachine.word bits.length]) = some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨first, hfirst, hf, hs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨second, hsecond, hout, htime, _⟩ := FieldMachine.field_run [] bits tail backing hb
  have hin : Composition.restart first.final FieldMachine.machine.start =
      FieldMachine.scan 0 ([] ++ Streaming.marks bits ++ tail) 0 bits.length 0 [] backing := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.restart, final, source, FieldMachine.scan, StablePartition.Workspace.overlay]
  simp only [List.length_nil] at hsecond
  rw [← hin] at hsecond
  have h := Composition.run_join positionMachine FieldMachine.machine 1 (4 * bits.length + 2)
    _ first second hfirst hsecond
  have he : 1 + 1 + (4 * bits.length + 2) = 4 * bits.length + 4 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt first second, h, ?_, ?_⟩
  · rw [Composition.joinedReceipt, hout]
    rfl
  · simp only [Composition.joinedReceipt, hs, htime]
    omega

theorem copy_ready (bits tail backing : List Bool) (capacity : Nat)
    (hb : backing.length ≤ 2 * bits.length + 1) :
    ReadyRun machine (8 * bits.length + 10)
      ![Streaming.marks bits ++ tail, backing, CompareMachine.word bits.length,
        List.replicate capacity false]
      ![Streaming.marks bits ++ tail, frame bits, CompareMachine.word bits.length,
        List.replicate (max capacity (4 * bits.length + 4)) false] := by
  obtain ⟨source, hr, ht, hs⟩ := raw_run bits tail backing hb
  obtain ⟨r, hrun, htapes, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    rawMachine (4 * bits.length + 4) _ source hr capacity
  have he : 2 * source.steps + 2 = 8 * bits.length + 10 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [ht] using htapes 0
    · simpa [ht] using htapes 1
    · simpa [ht] using htapes 2
    · simpa [hs] using hc

theorem take_ready (source backing : List Bool) (width capacity : Nat)
    (hw : width ≤ source.length) (hb : backing.length ≤ 2 * width + 1) :
    ReadyRun machine (8 * width + 10)
      ![frame source, backing, CompareMachine.word width, List.replicate capacity false]
      ![frame source, frame (source.take width), CompareMachine.word width,
        List.replicate (max capacity (4 * width + 4)) false] := by
  have hlen : (source.take width).length = width := by simp [List.length_take, Nat.min_eq_left hw]
  have hb' : backing.length ≤ 2 * (source.take width).length + 1 := by rw [hlen]; exact hb
  have h := copy_ready (source.take width) (frame (source.drop width)) backing capacity hb'
  have he : Streaming.marks (source.take width) ++ frame (source.drop width) = frame source := by
    rw [← Streaming.frame_append, List.take_append_drop]
  rw [he, hlen] at h
  exact h

/-- Width generation from the retained original framed input is also paid.
The extra unary rewind tape remains explicit and reusable. -/
def widthMachine : Machine 3 8 := Rewind.machine LengthMachine.machine

theorem width_ready (word : List Bool) (capacity : Nat) :
    ReadyRun widthMachine (8 * word.length + 8)
      ![frame word, [], List.replicate capacity false]
      ![frame word, CompareMachine.word word.length,
        List.replicate (max capacity (4 * word.length + 3)) false] := by
  obtain ⟨source, hr, hf, hs, _⟩ := LengthMachine.length_run word
  obtain ⟨r, hrun, ht, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    LengthMachine.machine _ _ source hr capacity
  have he : 2 * source.steps + 2 = 8 * word.length + 8 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf, LengthMachine.cfg] using ht 0
    · simpa [hf, LengthMachine.cfg, CompareMachine.word] using ht 1
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryFieldCopy
