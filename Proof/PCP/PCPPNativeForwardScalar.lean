import Proof.PCP.PCPPNativePadding
import Proof.Supplier.EquationRowForward

/-! Actual native scalar outputs never move left. These rule-table facts
allow the final existing output framer to measure the real append cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeForward
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem masked {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (i : Fin t)
    (hi : selected i=false) (hp : CursorRestore.NoLeft p i) :
    CursorRestore.NoLeft (MaskedReset.machine p selected) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q=true
    · simp [MaskedReset.machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [MaskedReset.machine,hh,hr] at ha
      | some b =>
        simp [MaskedReset.machine,hh,hr] at ha
        subst a
        simpa only [Rewind.recordAction,Fin.addCases_left] using hp q (fun j => bits (j.castAdd 1)) b hr
  · simp only [MaskedReset.machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha
        simp [MaskedReset.rewindAction,hi]
      · cases ha
        simp [Rewind.finishAction]
    · contradiction

theorem literal (bits : List Bool) : CursorRestore.NoLeft (HierarchyFixedWord.raw bits) 0 := by
  intro q bs a ha
  dsimp only [HierarchyFixedWord.raw] at ha
  split at ha
  · cases ha
    simp
  · contradiction

theorem natural : CursorRestore.NoLeft PCPPNativeNaturalAppend.machine 17 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward PCPPNativeNaturalAppend.headerSlots _ 17 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠17; omega)
  · exact CursorRestore.focus_forward PCPPNativeNaturalAppend.appendSlots (by decide)
      (PCPPQueryField.machine true) 2 EquationRowRaw.header_field_forward

theorem address_append : CursorRestore.NoLeft PCPPNativeAddressAppend.machine 20 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward PCPPNativeAddressAppend.addressSlots _ 20 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠20; omega)
  · exact CursorRestore.focus_forward PCPPNativeAddressAppend.appendSlots PCPPNativeAddressAppend.append_injective
      PCPPNativeNaturalAppend.machine 17 natural

theorem sum_append : CursorRestore.NoLeft PCPPNativeSumAppend.machine 20 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward PCPPNativeSumAppend.addressSlots _ 20 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠20; omega)
  · exact CursorRestore.focus_forward PCPPNativeSumAppend.appendSlots PCPPNativeSumAppend.append_injective
      PCPPNativeNaturalAppend.machine 17 natural

theorem address_reset : CursorRestore.NoLeft PCPPNativeAddressReset.machine 20 :=
  masked PCPPNativeAddressAppend.machine PCPPNativeAddressReset.selected 20 (by decide) address_append
theorem sum_reset : CursorRestore.NoLeft PCPPNativeSumReset.machine 20 :=
  masked PCPPNativeSumAppend.machine PCPPNativeSumReset.selected 20 (by decide) sum_append

theorem address : CursorRestore.NoLeft PCPPNativeAddressReusable.machine 20 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeAddressReusable.resetSlots (by decide)
      PCPPNativeAddressReset.machine 20 address_reset
  · exact EquationRowCuts.unselected_forward PCPPNativeAddressReusable.eraseSlots _ 20 (by
      intro i; apply Fin.ne_of_val_ne; exact (PCPPNativeAddressReusable.erase_away i).2)
theorem sum : CursorRestore.NoLeft PCPPNativeSumReusable.machine 20 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeSumReusable.resetSlots (by decide)
      PCPPNativeSumReset.machine 20 sum_reset
  · exact EquationRowCuts.unselected_forward PCPPNativeSumReusable.eraseSlots _ 20 (by
      intro i; apply Fin.ne_of_val_ne; exact (PCPPNativeSumReusable.erase_away i).2)
theorem literal_append (bits : List Bool) : CursorRestore.NoLeft (PCPPNativeLiteralAppend.machine bits) 20 :=
  CursorRestore.focus_forward PCPPNativeLiteralAppend.slots (by
    intro i j _; exact Subsingleton.elim i j) (HierarchyFixedWord.raw bits) 0 (literal bits)
theorem padding : CursorRestore.NoLeft PCPPNativePadding.machine 0 :=
  CursorRestore.repeat_forward (HierarchyFixedWord.raw PCPPNativePadding.zeroNode) (fun _ _ => true) 0
    (literal PCPPNativePadding.zeroNode)

end NearCubicWires.RepairOrdinary.PCPPNativeForward
