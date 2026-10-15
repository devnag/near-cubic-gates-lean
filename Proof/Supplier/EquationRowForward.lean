import Proof.Supplier.EquationRowRaw
import Proof.Supplier.EquationRowCutsForward

/-! The complete cold row producer advances its output cursor only right.
This is the exact syntactic premise for paid output-length recording. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embedded_extra_forward {t s extra : ℕ} (p : Machine t s) (i : Fin extra) :
    CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.natAdd t) := by
  intro q bs a ha
  obtain ⟨b,_hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simp only [TapeEmbedding.action,Fin.addCases_right]
  decide

theorem header_field_forward : CursorRestore.NoLeft (PCPPQueryField.machine true) 2 := by
  intro q bs a ha
  fin_cases q <;> simp [PCPPQueryField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp)
    | (cases ha; simp)

theorem header_append_forward : CursorRestore.NoLeft EquationHeaderAppend.machine 17 := by
  apply CursorRestore.composition_forward
  · exact embedded_extra_forward EquationNaturalHeader.machine (1 : Fin 2)
  · exact CursorRestore.focus_forward EquationHeaderAppend.slots (by decide)
      (PCPPQueryField.machine true) 2 header_field_forward

theorem headers_forward : CursorRestore.NoLeft EquationHeaders.machine 51 := by
  have hp (j : Fin 3) : CursorRestore.NoLeft (EquationHeaders.program j) 51 :=
    CursorRestore.focus_forward (EquationHeaders.slot j) (EquationHeaders.slot_injective j)
      EquationHeaderAppend.machine 17 header_append_forward
  exact CursorRestore.composition_forward _ _ 51
    (CursorRestore.composition_forward _ _ 51 (hp 0) (hp 1)) (hp 2)

theorem cold_header_forward : CursorRestore.NoLeft EquationHeaderCold.machine 110 := by
  apply CursorRestore.composition_forward
  · exact embedded_extra_forward EquationCountCold.machine (48 : Fin 49)
  · exact CursorRestore.focus_forward EquationHeaderCold.slots EquationHeaderCold.slots_injective
      EquationHeaders.machine 51 headers_forward

theorem prepare_forward : CursorRestore.NoLeft EquationRowPrepare.machine 110 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · apply CursorRestore.composition_forward
      · apply CursorRestore.composition_forward
        · apply CursorRestore.composition_forward
          · exact EquationRowCuts.embedded_forward 15 EquationHeaderCold.machine 110 cold_header_forward
          · exact EquationRowCuts.unselected_forward EquationRowAllocate.slots _ 110 (by decide)
        · intro q bs a ha
          simp only [EquationRowPrepare.boot,Option.some.injEq] at ha
          subst a
          decide
      · exact EquationRowCuts.unselected_forward EquationRowPhiHeader.eraseSlots _ 110 (by decide)
    · exact CursorRestore.focus_forward EquationRowPhiHeader.appendSlots EquationRowPhiHeader.append_injective
        EquationHeaderAppend.machine 17 header_append_forward
  · exact CursorRestore.focus_forward EquationRowPhiHeader.writerSlots EquationRowPhiHeader.writer_injective
      EquationIdentityColumns.machine 1 EquationIdentityColumns.out_forward

theorem output_forward : CursorRestore.NoLeft machine 110 :=
  CursorRestore.composition_forward _ _ 110 prepare_forward
    (CursorRestore.focus_forward slots slots_injective EquationRowCuts.machine 14 EquationRowCuts.output_forward)

end NearCubicWires.RepairOrdinary.EquationRowRaw
