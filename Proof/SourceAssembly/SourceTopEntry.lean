import Proof.SourceAssembly.SourcePoolIndexReady

/- Pay the original decomposition constructor on the retained native TOP and
frame precisely its logical output. The arbitrary constructor is disjoint
from the append-only destination; no forward-motion hypothesis is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyTopEntry
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairSource.ProjectionNormalization DecompositionSource ExecutableInterfaces
noncomputable section

theorem prepare_forward : CursorRestore.NoLeft Prepare.machine 15 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact EquationRowRaw.embedded_extra_forward Streaming.machine (12 : Fin 13)
    · exact EquationRowCuts.unselected_forward Prepare.countSlots _ 15 (by decide)
  · exact CursorRestore.focus_forward Prepare.fieldSlots (by decide) _ 2
      EquationRowRaw.header_field_forward

theorem call_forward (a : DecompositionAlgorithm) :
    CursorRestore.NoLeft (Call.machine a) (Call.old a 15) := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.embedded_forward _ _ 15 prepare_forward
  · apply EquationRowCuts.unselected_forward (Call.slots a) _ _
    intro j he
    have hn := Call.old_none a 15 (by decide)
    have hs := RecoveryFocus.pick_slot (Call.slots a) (Call.slots_injective a) j
    rw [he,hn] at hs
    contradiction

theorem counted_forward (a : DecompositionAlgorithm) :
    CursorRestore.NoLeft (Counted.machine a) (Counted.localTape a 15) := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.embedded_forward 11 _ _ (call_forward a)
  · apply EquationRowCuts.unselected_forward (Counted.countSlots a) _ _
    intro j he
    have hn := Counted.old_none a (Call.old a 15) (Ne.symm (Call.output_ne_old a 15))
    have hs := RecoveryFocus.pick_slot (Counted.countSlots a) (Counted.countSlots_injective a) j
    rw [he] at hs
    change RecoveryFocus.pick (Counted.countSlots a) (Counted.old a (Call.old a 15))=some j at hs
    rw [hn] at hs
    contradiction

theorem fields_forward : CursorRestore.NoLeft Fields.machine 2 := by
  apply CursorRestore.composition_forward
  · intro q bs act hact
    cases hact
    change HeadMove.right ≠ HeadMove.left
    decide
  · exact EquationRowRaw.header_field_forward

theorem records_forward : CursorRestore.NoLeft Records.machine 2 :=
  CursorRestore.repeat_forward Records.child (fun _ _=>true) 2
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.repeat_forward Fields.machine (fun _ _=>true) 2 fields_forward)
      (EquationRowCuts.embedded_forward 1 Fields.machine 2 fields_forward))

theorem forward (a : DecompositionAlgorithm) :
    CursorRestore.NoLeft (Entry.machine a) (Counted.localTape a 15) := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact counted_forward a
    · exact CursorRestore.focus_forward (Entry.fieldSlots a) (Entry.fieldSlots_injective a)
        _ 2 EquationRowRaw.header_field_forward
  · exact CursorRestore.focus_forward (Entry.recordSlots a) (Entry.recordSlots_injective a)
      _ 2 records_forward

def machine (a : DecompositionAlgorithm) :=
  AppendOutputFrame.machine (Entry.machine a) (Counted.localTape a 15)
def budget (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :=
  2*Entry.budget a r+4*(Entry.output a r).length+7

theorem framed_run (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    ∃ A, Step (machine a) (budget a r) (fun _=>0)
      (AppendOutputFrame.input (Counted.input a r)) (fun _=>0) A ∧
      A ((0 : Fin 2).natAdd (Counted.tapes a+2))=frame (Entry.output a r) := by
  obtain ⟨first,hfirst,_hf,ht,hh,_⟩ := Entry.entry_run a r
  obtain ⟨last,hl,lt,lh,_⟩ := AppendOutputFrame.frame_run
    (Entry.machine a) (Counted.localTape a 15) (forward a) (Entry.budget a r)
    (Counted.input a r) first hfirst (Entry.output a r) ht hh
  exact ⟨last.final.tapes,(Step.of_run hl (funext lh) rfl).enlarge (by unfold budget;omega),lt⟩

end
end SourceAssemblyTopEntry
