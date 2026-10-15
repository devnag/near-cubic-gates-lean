import Proof.Foundations.OrdinaryStablePartition
import Proof.Foundations.OrdinaryFramedSource

/-! Actual stable partition consumed by the common framed-input carrier.
The wrapper charges input copying, rewind and handoff. Terminal partition
heads are not reset by this theorem. -/
namespace NearCubicWires.RepairOrdinary.StablePartition
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def partitionCarrier (tag : Bool) :
    WordFunction (List Record) stream (fun rs => stream (selected tag rs))
      (fun rs => 6 * (stream rs).length + 3) := by
  let raw := FramedSource.ofRaw (by decide : 0 < 3) machine
    (if tag then (2 : Fin 3) else 1) stream (fun rs => stream (selected tag rs))
    (fun rs => (stream rs).length + rs.length) (by
      intro rs
      obtain ⟨r, hr, _, hf, ht, _, _, _⟩ := partition_run rs
      refine ⟨r, hr, ?_⟩
      cases tag
      · exact hf
      · exact ht)
  apply raw.enlargeBudget
  intro rs
  have h := record_count_le rs
  simp only [stream, List.length_append, List.length_singleton] at h ⊢
  omega

end NearCubicWires.RepairOrdinary.StablePartition
