import Proof.Hierarchy.CompetitorSameBucketGroupReadRun
import Proof.Hierarchy.CompetitorSameBucketGroupSemantics

/-! The direct key reader applied to the literal typed record emitted and
sorted by the same-bucket source producer. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
open LocalBitMultitape MatrixScoreBatch SignedSortKey CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_word (p m : ℕ) (e : Entry) :
    word (decide (e.coefficient<0)) (binary p e.coefficient.natAbs) (e.ids m)=
      StablePartition.recordBits (e.record p m) := by
  rw [word_frame]
  simp [StablePartition.recordBits,Entry.record,CompetitorSameBucketKeys.key,
    signMagnitude,Entry.ids,frame,List.append_assoc]

theorem entry_run (pre suffix oldMagnitude oldIDs oldFlag : List Bool) (p m cap : ℕ) (e : Entry)
    (hm : oldMagnitude.length≤2*p+1) (hi : oldIDs.length≤4*m+1) (hf : oldFlag.length≤1) :
    ∃ r,runFrom machine (4*p+8*m+12)
      (cfg machine.start (pre++StablePartition.recordBits (e.record p m)++suffix)
        oldMagnitude oldIDs oldFlag pre.length p (2*m) cap)=some r ∧
      r.final.heads=heads (pre.length+2*p+4*m+5) ∧
      r.final.tapes=data (pre++StablePartition.recordBits (e.record p m)++suffix)
        (frame (binary p e.coefficient.natAbs)) (frame (e.ids m)) [decide (e.coefficient<0)] p (2*m) cap ∧
      r.steps=4*p+8*m+12 := by
  have h := read_run pre suffix (binary p e.coefficient.natAbs) (e.ids m)
    oldMagnitude oldIDs oldFlag cap (decide (e.coefficient<0)) (by simpa using hm)
    (by rw [ids_length]; omega) hf
  have hw : (word (decide (e.coefficient<0)) (binary p e.coefficient.natAbs) (e.ids m)).length=
      2*p+4*m+5 := by rw [word_length,binary_length,ids_length]; omega
  rw [hw,entry_word] at h
  simp only [binary_length,ids_length,budget] at h
  have hb : 4*p+4*(2*m)+12=4*p+8*m+12 := by omega
  rw [hb] at h
  simpa only [Nat.add_assoc] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
