import Proof.Supplier.EquationRowCutsRequest

/-! The actual cut output is append-only. This syntactic rule-table fact
lets the enclosing row framer count its physical output moves directly. -/
namespace NearCubicWires.RepairOrdinary.EquationRowCuts
open LocalBitMultitape EquationCut
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem unselected_forward {t u s : ℕ} (slots : Fin t → Fin u) (p : Machine t s) (i : Fin u)
    (hi : ∀ j,slots j≠i) : CursorRestore.NoLeft (RecoveryFocus.machine slots p) i := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  have hn : RecoveryFocus.pick slots i=none := by
    unfold RecoveryFocus.pick
    apply dif_neg
    simpa using hi
  simp [RecoveryFocus.action,hn]

theorem embedded_forward {t s : ℕ} (extra : ℕ) (p : Machine t s) (i : Fin t)
    (hp : CursorRestore.NoLeft p i) : CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.castAdd extra) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simpa only [TapeEmbedding.action,Fin.addCases_left] using hp q (fun j => bs (j.castAdd extra)) b hb

theorem field_output_forward : CursorRestore.NoLeft Field.machine 1 := by
  intro q bs a ha
  fin_cases q <;> simp [Field.machine] at ha <;> cases ha <;> simp

theorem scalar_stream_output_forward (negate : Bool) :
    CursorRestore.NoLeft (EquationScalarStream.machine negate) 14 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact unselected_forward EquationScalarStream.moveSlots _ 14 (by decide)
    · exact unselected_forward EquationScalarStream.scalarSlots _ 14
        (EquationScalarStream.scalar_other 14 (by simp))
  · apply CursorRestore.composition_forward
    · exact CursorRestore.focus_forward EquationScalarStream.copySlots (by decide)
        PCPSerializerReuse.copyMachine 1
        (CursorRestore.other_forward Field.machine 0 1 (by decide) field_output_forward)
    · exact unselected_forward EquationScalarStream.eraseSlots _ 14 (by decide)

theorem widen_output_forward : CursorRestore.NoLeft EquationWiden.machine 1 := by
  intro q bs a ha
  fin_cases q <;> simp [EquationWiden.machine] at ha <;> cases ha <;> simp

theorem zero_output_forward : CursorRestore.NoLeft EquationZeroField.machine 1 := by
  intro q bs a ha
  fin_cases q <;> simp [EquationZeroField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp)
    | (cases ha; simp)

theorem weights_output_forward : CursorRestore.NoLeft EquationCut.weightMachine 1 := by
  apply EquationCut.calls_forward
  intro j
  fin_cases j
  · exact CursorRestore.focus_forward EquationCut.weightSlots (by decide) EquationWidenLoop.machine 1
      (CursorRestore.repeat_forward EquationWiden.machine (fun _ _=>true) 1 widen_output_forward)
  · exact CursorRestore.focus_forward EquationCut.zeroSlots (by decide) EquationZeroField.machine 1 zero_output_forward

theorem base_output_forward : CursorRestore.NoLeft EquationCut.base 1 := by
  apply CursorRestore.composition_forward
  · exact weights_output_forward
  · apply CursorRestore.composition_forward
    all_goals exact CursorRestore.focus_forward EquationCut.scalarSlots (by decide) EquationWiden.machine 1 widen_output_forward

theorem cut_output_forward : CursorRestore.NoLeft EquationCut.Ambient.machine 14 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward EquationCut.Ambient.restoreSlots (by decide) EquationCut.restored 1
      (CursorRestore.other_forward EquationCut.base 0 1 (by decide) base_output_forward)
  · apply CursorRestore.composition_forward
    · exact CursorRestore.focus_forward EquationCut.Ambient.slots (by decide) EquationCut.weightMachine 1 weights_output_forward
    · apply CursorRestore.composition_forward
      · exact embedded_forward 4 _ 14 (scalar_stream_output_forward false)
      · exact embedded_forward 4 _ 14 (scalar_stream_output_forward true)

theorem output_forward : CursorRestore.NoLeft machine 14 :=
  CursorRestore.repeat_forward EquationCut.Ambient.machine (fun _ _=>true) 14 cut_output_forward

end NearCubicWires.RepairOrdinary.EquationRowCuts
