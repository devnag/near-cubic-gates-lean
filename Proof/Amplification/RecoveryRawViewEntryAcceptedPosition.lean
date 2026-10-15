import Proof.Amplification.RecoveryRawViewEntryPosition

/-! Every successful raw-view parse leaves the same source at an even
physical cursor. Canonical input separately determines that cursor exactly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_position (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k)
    (ha : answer x word k=true) :
    ∃ pos,(output x word k).1.inner.stream.source=frame word ∧
      (output x word k).1.inner.stream.pos=2*pos := by
  obtain ⟨n,rest,hparse,hcheck⟩ := accepted_case x word k ha
  have hv := cursor_valid (flagged x false) word k n (flagged_valid x false hx) hs hp
  have ho : (RecoveryRawViewLoop.out word n (cursor (flagged x false) k n)).1=true := by
    simp only [RecoveryRawViewWhole.answer,Bool.and_eq_true] at hcheck
    exact hcheck.1
  have hi := RecoveryRawViewLoop.out_inv x.width n word (cursor (flagged x false) k n) hv ho
  rw [output_some x word k n rest hparse]
  exact ⟨_,hi.2.2.1,hi.2.2.2⟩

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
