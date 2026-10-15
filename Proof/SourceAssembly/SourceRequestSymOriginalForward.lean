import Proof.SourceAssembly.SourceRequestThrOriginalForward

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SymOriginalForward
open NearCubicWires LocalBitMultitape RepairOrdinary RepairSource RepairSource.ProjectionNormalization
open NearCubicWires.SourceRequest.ThrOriginalForward (pair_forward move_forward position_forward halt_forward)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate.machine` at tape 1688. -/
theorem snat0 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate.machine) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.seed` at tape 1688. -/
theorem snat1 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.seed) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.first` at tape 1688. -/
theorem snat2 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat0 snat1)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.prefixMachine` at tape 1688. -/
theorem snat3 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.prefixMachine Bool.false) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.second` at tape 1688. -/
theorem snat4 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.second Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat2 snat3)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.load` at tape 1688. -/
theorem snat5 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.load) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.machine` at tape 1688. -/
theorem snat6 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.machine Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat4 snat5)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.parser` at tape 1688. -/
theorem snat7 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.parser) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.publisher` at tape 1688. -/
theorem snat8 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.publisher) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.machine` at tape 1688. -/
theorem snat9 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop.machine) (1688 : Fin 1703) :=
  (pair_forward _ _ _ _ snat7 snat8)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric.machine` at tape 1688. -/
theorem snat10 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric.machine) (1688 : Fin 1703) :=
  (pair_forward _ _ _ _ snat6 snat9)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase.machine` at tape 1688. -/
theorem snat11 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase.machine) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.countCopy` at tape 1688. -/
theorem snat12 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.countCopy) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader.machine` at tape 17. -/
theorem snat13 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader.machine) (17 : Fin 19) :=
  (PCPPNativeForward.masked _ _ (17 : Fin 18) (by decide) EquationRowRaw.header_append_forward)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.header` at tape 1688. -/
theorem snat14 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.header) (1688 : Fin 1703) :=
  (CursorRestore.focus_forward _ (by decide) _ (17 : Fin 19) snat13)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.first` at tape 1688. -/
theorem snat15 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat12 snat14)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.top` at tape 1688. -/
theorem snat16 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.top) (1688 : Fin 1703) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.machine` at tape 1688. -/
theorem snat17 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat15 snat16)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.first` at tape 1688. -/
theorem snat18 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat11 snat17)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.machine` at tape 1688. -/
theorem snat19 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat18 snat11)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition.machine` at tape 1688. -/
theorem snat20 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition.machine Bool.false) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun.machine` at tape 1688. -/
theorem snat21 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun.machine Bool.false) (1688 : Fin 1703) :=
  (pair_forward _ _ _ _ snat19 snat20)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loader` at tape 1049. -/
theorem snat22 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loader) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.parser` at tape 1049. -/
theorem snat23 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.parser) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.describe` at tape 1049. -/
theorem snat24 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.describe) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.native` at tape 1049. -/
theorem snat25 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.native) (1049 : Fin 1059) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.wires` at tape 1049. -/
theorem snat26 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.wires) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.selected` at tape 1049. -/
theorem snat27 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.selected) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat25 snat26)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.choice` at tape 1049. -/
theorem snat28 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.choice Bool.false) (1049 : Fin 1059) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) snat27)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.publish` at tape 1049. -/
theorem snat29 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.publish Bool.false) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat24 snat28)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.checked` at tape 1049. -/
theorem snat30 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.checked Bool.false) (1049 : Fin 1059) :=
  (pair_forward _ _ _ _ snat23 snat29)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loaded` at tape 1049. -/
theorem snat31 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loaded Bool.false) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat22 snat30)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append` at tape 1049. -/
theorem snat32 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append) (1049 : Fin 1060) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice` at tape 1049. -/
theorem snat33 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice Bool.false) (1049 : Fin 1060) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) snat32)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine` at tape 1049. -/
theorem snat34 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine Bool.false) (1049 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowCuts.embedded_forward _ _ (1049 : Fin 1059) snat31) snat33)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.foldFlag` at tape 1049. -/
theorem snat35 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.foldFlag) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.eraser` at tape 1049. -/
theorem snat36 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.eraser) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.folded` at tape 1049. -/
theorem snat37 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.folded) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat35 snat36)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advance` at tape 1049. -/
theorem snat38 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advance) (1049 : Fin 1059) :=
  (position_forward _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advanceTwice` at tape 1049. -/
theorem snat39 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advanceTwice) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat38 snat38)

theorem snat40 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.finish) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ snat37 snat39)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round` at tape 1049. -/
theorem snat41 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.false) (1049 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ snat34 (EquationRowCuts.embedded_forward _ _ (1049 : Fin 1059) snat40))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine` at tape 1049. -/
theorem snat42 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine
  (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.false)) (1049 : Fin 1061) :=
  (CursorRestore.repeat_forward _ _ (1049 : Fin 1060) snat41)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop` at tape 1049. -/
theorem snat43 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop Bool.false) (1049 : Fin 1061) :=
  snat42

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine` at tape 1688. -/
theorem snat44 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine Bool.false) (1688 : Fin 1704) :=
  (CursorRestore.focus_forward _ CloseoutRowsSupportStream.Dock.slots_injective _ (1049 : Fin 1061) snat43)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem snat45 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1689) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem snat46 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1690) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.first` at tape 1688. -/
theorem snat47 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat45 snat46)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem snat48 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 297) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.second` at tape 1688. -/
theorem snat49 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.second) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat47 snat48)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem snat50 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1692) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.third` at tape 1688. -/
theorem snat51 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.third) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat49 snat50)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem snat52 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 624) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.machine` at tape 1688. -/
theorem snat53 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat51 snat52)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned` at tape 1688. -/
theorem snat54 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned Bool.false) (1688 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ snat44 (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) snat53))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem snat55 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 0) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem snat56 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 1) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.first` at tape 1688. -/
theorem snat57 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat55 snat56)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem snat58 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 2) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.machine` at tape 1688. -/
theorem snat59 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat57 snat58)

/-- `Sigma.snd` at tape 1688. -/
theorem snat60 : CursorRestore.NoLeft ((NearCubicWires.RepairOrdinary.CloseoutRowsCircuitArithmeticDock.stage Bool.false).snd) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.first` at tape 1688. -/
theorem snat61 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.first Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat59 snat60)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.description` at tape 1688. -/
theorem snat62 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.description Bool.false) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.wires` at tape 1688. -/
theorem snat63 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.wires) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.first` at tape 1688. -/
theorem snat64 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.first Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat62 snat63)

theorem snat65 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.finish) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.machine` at tape 1688. -/
theorem snat66 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.machine Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat64 snat65)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.machine` at tape 1688. -/
theorem snat67 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.machine Bool.false) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ snat61 snat66)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail` at tape 1688. -/
theorem snat68 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail Bool.false) (1688 : Fin 1704) :=
  (pair_forward _ _ _ _ snat54 (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) snat67))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body` at tape 1688. -/
theorem snat69 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body Bool.false) (1688 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) snat21) snat68)

/-- `Sigma.snd` at tape 1688. -/
theorem snat70 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.program.snd) (1688 : Fin 1704) :=
  (pair_forward _ _ _ _ (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) snat10) snat69)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.machine` at tape 1688. -/
theorem snat71 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.machine) (1688 : Fin 1704) :=
  snat70

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append` at tape 1059. -/
theorem ssup0 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append) (1059 : Fin 1060) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice` at tape 1059. -/
theorem ssup1 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice Bool.false) (1059 : Fin 1060) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) ssup0)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine` at tape 1059. -/
theorem ssup2 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine Bool.false) (1059 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) ssup1)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round` at tape 1059. -/
theorem ssup3 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.false) (1059 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ ssup2 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine` at tape 1059. -/
theorem ssup4 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine
  (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.false)) (1059 : Fin 1061) :=
  (CursorRestore.repeat_forward _ _ (1059 : Fin 1060) ssup3)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop` at tape 1059. -/
theorem ssup5 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop Bool.false) (1059 : Fin 1061) :=
  ssup4

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine` at tape 1703. -/
theorem ssup6 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine Bool.false) (1703 : Fin 1704) :=
  (CursorRestore.focus_forward _ CloseoutRowsSupportStream.Dock.slots_injective _ (1059 : Fin 1061) ssup5)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned` at tape 1703. -/
theorem ssup7 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned Bool.false) (1703 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ ssup6 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail` at tape 1703. -/
theorem ssup8 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail Bool.false) (1703 : Fin 1704) :=
  (pair_forward _ _ _ _ ssup7 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body` at tape 1703. -/
theorem ssup9 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body Bool.false) (1703 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) ssup8)

/-- `Sigma.snd` at tape 1703. -/
theorem ssup10 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.program.snd) (1703 : Fin 1704) :=
  (pair_forward _ _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) ssup9)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.machine` at tape 1703. -/
theorem ssup11 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric.machine) (1703 : Fin 1704) :=
  ssup10

/-- **The original SYM writer's native cursor (tape 1688) never moves left.** -/
theorem native_forward :
    CursorRestore.NoLeft CloseoutRowsSupportStream.Symmetric.machine (1688 : Fin 1704) := snat71

/-- **The original SYM writer's support cursor (tape 1703) never moves left.** -/
theorem support_forward :
    CursorRestore.NoLeft CloseoutRowsSupportStream.Symmetric.machine (1703 : Fin 1704) := ssup11

end NearCubicWires.SourceRequest.SymOriginalForward

