import Proof.PCP.PCPPNativeClauseDescriptorAssembly

/-! Header, native-byte copy and final padding/footer all append to the
same descriptor tape. Thus the faithful source framer measures this actual
descriptor, including the source's required padding. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_forward : CursorRestore.NoLeft PCPPNativeColdHeader.machine 18 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward PCPPNativeColdHeader.firstSlots PCPPNativeColdHeader.first_injective
      _ 17 PCPPNativeForward.natural)
    (CursorRestore.focus_forward PCPPNativeColdHeader.lastSlots PCPPNativeColdHeader.last_injective
      _ 17 PCPPNativeForward.natural)
theorem entry_forward (minimum : ℕ) : CursorRestore.NoLeft (PCPPNativeDescriptorEntry.machine minimum) 26 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward PCPPNativeDescriptorEntry.metadataSlots _ 26 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠26; omega))
    (CursorRestore.focus_forward PCPPNativeDescriptorEntry.headerSlots PCPPNativeDescriptorEntry.header_injective
      _ 18 header_forward)
theorem copy_forward : CursorRestore.NoLeft GeneratedAmplifier.Copy.machine 1 := by
  intro q bs a ha
  fin_cases q <;> simp [GeneratedAmplifier.Copy.machine] at ha <;> cases ha <;> simp
theorem padding_position_forward : CursorRestore.NoLeft PCPPNativeColdPadding.position 3 := by
  intro q bs a ha
  simp only [PCPPNativeColdPadding.position] at ha
  split at ha
  · cases ha
    decide
  · contradiction
theorem cold_padding_forward : CursorRestore.NoLeft PCPPNativeColdPadding.machine 3 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.unselected_forward PCPPNativeColdPadding.templateSlots _ 3 (by decide)) padding_position_forward)
    (CursorRestore.focus_forward PCPPNativeColdPadding.paddingSlots (by decide) _ 0 PCPPNativeForward.padding)
theorem tail_forward : CursorRestore.NoLeft PCPPNativeDescriptorTail.machine 4 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward PCPPNativeDescriptorTail.paddingSlots (by decide) _ 3 cold_padding_forward)
    (CursorRestore.focus_forward PCPPNativeDescriptorTail.footerSlots PCPPNativeDescriptorTail.footer_injective
      _ 17 PCPPNativeForward.natural)
theorem forward (minimum : ℕ) : CursorRestore.NoLeft (machine minimum) 26 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 22 _ 26 (entry_forward minimum))
      (CursorRestore.focus_forward copySlots (by decide) _ 1 copy_forward))
    (CursorRestore.focus_forward tailSlots tail_injective _ 4 tail_forward)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
