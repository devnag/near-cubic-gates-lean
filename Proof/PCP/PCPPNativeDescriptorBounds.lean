import Proof.PCP.PCPPNativeDescriptorTail

/-! Cold descriptor entry has one explicit quadratic bound. Its header and
tail have forward output cursors, so the existing complete native/source
handoff can physically measure, frame and consume the finished descriptor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeDescriptorBounds
open LocalBitMultitape PCPPNativeColdMetadata RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_budget (minimum width size : ℕ) :
    PCPPNativeDescriptorEntry.budget minimum width size ≤ 8192*(minimum+width+size+1)^2 := by
  let M := minimum+width+size+1
  let d := domain minimum width
  let p := padded minimum width size
  have hd : d ≤ minimum+width := by dsimp [d,domain]; omega
  have hp : p ≤ minimum+width+size := by dsimp [p,padded]; omega
  have hlin : d+p+1 ≤ 2*M := by dsimp [M]; omega
  have hs := Nat.pow_le_pow_left hlin 2
  have hh := PCPPNativeColdHeader.budget_bound d p
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hsq : M ≤ M^2 := by nlinarith
  change 2*minimum+2*d+2*p+12+1+PCPPNativeColdHeader.budget d p ≤ 8192*M^2
  have hmin : minimum ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  have hpM : p ≤ M := by dsimp [M]; omega
  nlinarith

theorem header_forward : CursorRestore.NoLeft PCPPNativeColdHeader.machine 18 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeColdHeader.firstSlots PCPPNativeColdHeader.first_injective
      PCPPNativeNaturalAppend.machine 17 PCPPNativeForward.natural
  · exact CursorRestore.focus_forward PCPPNativeColdHeader.lastSlots PCPPNativeColdHeader.last_injective
      PCPPNativeNaturalAppend.machine 17 PCPPNativeForward.natural

theorem entry_forward (minimum : ℕ) : CursorRestore.NoLeft (PCPPNativeDescriptorEntry.machine minimum) 26 := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward PCPPNativeDescriptorEntry.metadataSlots _ 26 (by
      intro i
      apply Fin.ne_of_val_ne
      change i.val≠26
      omega)
  · exact CursorRestore.focus_forward PCPPNativeDescriptorEntry.headerSlots PCPPNativeDescriptorEntry.header_injective
      PCPPNativeColdHeader.machine 18 header_forward

theorem padding_forward : CursorRestore.NoLeft PCPPNativeColdPadding.machine 3 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact EquationRowCuts.unselected_forward PCPPNativeColdPadding.templateSlots _ 3 (by decide)
    · intro q bits a ha
      dsimp only [PCPPNativeColdPadding.position] at ha
      split at ha
      · cases ha; decide
      · contradiction
  · exact CursorRestore.focus_forward PCPPNativeColdPadding.paddingSlots (by decide)
      PCPPNativePadding.machine 0 PCPPNativeForward.padding

theorem tail_forward : CursorRestore.NoLeft PCPPNativeDescriptorTail.machine 4 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeDescriptorTail.paddingSlots (by decide)
      PCPPNativeColdPadding.machine 3 padding_forward
  · exact CursorRestore.focus_forward PCPPNativeDescriptorTail.footerSlots PCPPNativeDescriptorTail.footer_injective
      PCPPNativeNaturalAppend.machine 17 PCPPNativeForward.natural

end NearCubicWires.RepairOrdinary.PCPPNativeDescriptorBounds
