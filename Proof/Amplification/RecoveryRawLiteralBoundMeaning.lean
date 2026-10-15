import Proof.Amplification.RecoveryRawLiteralBoundWhole

/-! The flags describe values decoded from the actual code, independently
of the skipped certificate scalar fields. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (x : State) := value x.stream.data.data.bits
def head (x : State) := Nat.unpair (Nat.unpair (code x-1)).1

theorem output_present (x : State) : (output x).stream.data.present=decide (code x≠0) := by
  rw [output_stream,RecoveryRawLiteralStream.output_data]
  exact RecoveryRawLiteral.output_present x.stream.data

theorem output_width (x : State) : (output x).stream.width=x.stream.width := by
  rw [output_stream]
  exact RecoveryRawLiteralStream.output_width x.stream

theorem output_tail (x : State) (hn : code x≠0) : code (output x)=(Nat.unpair (code x-1)).2 := by
  unfold code
  rw [output_stream,RecoveryRawLiteralStream.output_data]
  exact RecoveryRawLiteral.output_tail x.stream.data hn

theorem decoded_present (x : State) (hn : code x≠0) : (decoded x).stream.data.present=true := by
  change (RecoveryRawLiteralStream.output x.stream).data.present=true
  rw [RecoveryRawLiteralStream.output_data,RecoveryRawLiteral.output_present]
  exact decide_eq_true hn

theorem output_tags (x : State) (hn : code x≠0) :
    (output x).tags=(x.tags && decide ((head x).1 ≤ 1)) := by
  rw [output,if_pos (decoded_present x hn)]
  change (x.tags && (RecoveryRawLiteralStream.output x.stream).data.data.result)=_
  rw [RecoveryRawLiteralStream.output_data]
  rw [RecoveryRawLiteral.output_tag x.stream.data hn]
  rfl

theorem output_bounded (x : State) (hn : code x≠0) :
    (output x).bounded=(x.bounded && decide ((head x).2 < value x.bound)) := by
  have hi : value (indexWord x)=(head x).2 := (RecoveryRawLiteral.output_variable x.stream.data hn).2
  rw [output,if_pos (decoded_present x hn)]
  change (x.bounded && !decide (value x.bound ≤ value (indexWord x)))=_
  rw [hi]
  congr 1
  by_cases h : value x.bound ≤ (head x).2
  · have hn : ¬(head x).2 < value x.bound := by omega
    simp only [h,hn,decide_true,decide_false,Bool.not_true]
  · have hn : (head x).2 < value x.bound := by omega
    simp only [h,hn,decide_false,decide_true,Bool.not_false]

theorem output_pos (x : State) : (output x).stream.pos=
    if code x=0 then x.stream.pos else x.stream.pos+4*x.stream.width := by
  rw [output_stream]
  exact RecoveryRawLiteralStream.output_pos x.stream

theorem output_source (x : State) : (output x).stream.source=x.stream.source := by
  rw [output_stream]
  exact RecoveryRawLiteralStream.output_source x.stream

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
