import Proof.CaseAnalysis.ScheduleDock

/-! An opaque receipt bridge for the existing literal word printer. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_ready (word : List Bool) :
    ClockJoin.ReadyRun (HierarchyFixedWord.machine word) (2*word.length+2)
      (fun _ => []) ![word,List.replicate word.length false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready word
  exact ⟨r,hr,ht,hh,hs.le⟩

end NearCubicWires.RepairSource.CloseoutSchedule
