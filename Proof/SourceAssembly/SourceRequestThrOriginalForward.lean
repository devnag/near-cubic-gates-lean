import Proof.SourceAssembly.SourceCircuitNative
import Proof.Supplier.EquationCutLayout
import Proof.Supplier.EquationRowCutsForward
import Proof.PCP.ProjectionNormalizationForwardRules
import Proof.PCP.ProjectionNormalizationSuffixRestore
import Proof.Amplification.RecoveryPCPFormulaResumeForward
import Proof.Supplier.EquationRowForward
import Proof.PCP.PCPPNativeForwardScalar

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.ThrOriginalForward
open NearCubicWires LocalBitMultitape RepairOrdinary RepairSource RepairSource.ProjectionNormalization

theorem pair_forward {t a b : Nat} (p : Machine t a) (q : Machine t b)
    (test : (Fin t → Bool) → Bool) (i : Fin t) (hp : CursorRestore.NoLeft p i)
    (hq : CursorRestore.NoLeft q i) :
    CursorRestore.NoLeft (CloseoutRowsGateColdPair.machine p q test) i :=
  EquationCut.calls_forward _ _ _ _ _ (fun j => match j with
    | ⟨0, _⟩ => hp
    | ⟨1, _⟩ => hq
    | ⟨_ + 2, h⟩ => absurd h (by omega))

theorem move_forward {t : Nat} (target i : Fin t) :
    CursorRestore.NoLeft (CompetitorCountTable.moveMachine target) i := by
  intro q bits a ha
  simp only [CompetitorCountTable.moveMachine] at ha
  split at ha
  · cases ha
    dsimp only
    split <;> simp
  · cases ha

theorem position_forward {t : Nat} (directions : Fin t → HeadMove) (i : Fin t)
    (h : directions i ≠ .left) : CursorRestore.NoLeft (DecompositionCountPosition.move directions) i := by
  intro q bits a ha
  simp only [DecompositionCountPosition.move] at ha
  split at ha
  · cases ha
    exact h
  · cases ha

theorem halt_forward {t s : Nat} (p : Machine t s) (i : Fin t)
    (h : ∀ q bits, p.rule q bits = none) : CursorRestore.NoLeft p i := by
  intro q bits a ha
  rw [h] at ha
  cases ha

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate.machine` at tape 1688. -/
theorem nat0 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate.machine) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.seed` at tape 1688. -/
theorem nat1 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.seed) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.first` at tape 1688. -/
theorem nat2 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat0 nat1)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.prefixMachine` at tape 1688. -/
theorem nat3 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.prefixMachine Bool.true) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.second` at tape 1688. -/
theorem nat4 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.second Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat2 nat3)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.load` at tape 1688. -/
theorem nat5 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.load) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.machine` at tape 1688. -/
theorem nat6 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry.machine Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat4 nat5)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold.positioned` at tape 1688. -/
theorem nat7 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold.positioned) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat6 (move_forward _ _))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.parser` at tape 1688. -/
theorem nat8 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.parser) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.publish` at tape 1688. -/
theorem nat9 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.publish) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.machine` at tape 1688. -/
theorem nat10 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop.machine) (1688 : Fin 1703) :=
  (pair_forward _ _ _ _ nat8 nat9)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold.machine` at tape 1688. -/
theorem nat11 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat7 nat10)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase.machine` at tape 1688. -/
theorem nat12 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase.machine) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.countCopy` at tape 1688. -/
theorem nat13 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.countCopy) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader.machine` at tape 17. -/
theorem nat14 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader.machine) (17 : Fin 19) :=
  (PCPPNativeForward.masked _ _ (17 : Fin 18) (by decide) EquationRowRaw.header_append_forward)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.header` at tape 1688. -/
theorem nat15 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.header) (1688 : Fin 1703) :=
  (CursorRestore.focus_forward _ (by decide) _ (17 : Fin 19) nat14)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.first` at tape 1688. -/
theorem nat16 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat13 nat15)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.top` at tape 1688. -/
theorem nat17 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.top) (1688 : Fin 1703) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.machine` at tape 1688. -/
theorem nat18 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrefix.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat16 nat17)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.first` at tape 1688. -/
theorem nat19 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat12 nat18)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.machine` at tape 1688. -/
theorem nat20 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitNativePrepare.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat19 nat12)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition.machine` at tape 1688. -/
theorem nat21 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomPosition.machine Bool.true) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun.machine` at tape 1688. -/
theorem nat22 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPreparedRun.machine Bool.true) (1688 : Fin 1703) :=
  (pair_forward _ _ _ _ nat20 nat21)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loader` at tape 1049. -/
theorem nat23 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loader) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.parser` at tape 1049. -/
theorem nat24 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.parser) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.describe` at tape 1049. -/
theorem nat25 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.describe) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.native` at tape 1049. -/
theorem nat26 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.native) (1049 : Fin 1059) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.wires` at tape 1049. -/
theorem nat27 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.wires) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.selected` at tape 1049. -/
theorem nat28 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.selected) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat26 nat27)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.choice` at tape 1049. -/
theorem nat29 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.choice Bool.true) (1049 : Fin 1059) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) nat28)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.publish` at tape 1049. -/
theorem nat30 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.publish Bool.true) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat25 nat29)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.checked` at tape 1049. -/
theorem nat31 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.checked Bool.true) (1049 : Fin 1059) :=
  (pair_forward _ _ _ _ nat24 nat30)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loaded` at tape 1049. -/
theorem nat32 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.loaded Bool.true) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat23 nat31)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append` at tape 1049. -/
theorem nat33 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append) (1049 : Fin 1060) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice` at tape 1049. -/
theorem nat34 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice Bool.true) (1049 : Fin 1060) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) nat33)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine` at tape 1049. -/
theorem nat35 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine Bool.true) (1049 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowCuts.embedded_forward _ _ (1049 : Fin 1059) nat32) nat34)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.foldFlag` at tape 1049. -/
theorem nat36 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.foldFlag) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.eraser` at tape 1049. -/
theorem nat37 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.eraser) (1049 : Fin 1059) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.folded` at tape 1049. -/
theorem nat38 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.folded) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat36 nat37)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advance` at tape 1049. -/
theorem nat39 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advance) (1049 : Fin 1059) :=
  (position_forward _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advanceTwice` at tape 1049. -/
theorem nat40 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.advanceTwice) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat39 nat39)

theorem nat41 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom.finish) (1049 : Fin 1059) :=
  (CursorRestore.composition_forward _ _ _ nat38 nat40)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round` at tape 1049. -/
theorem nat42 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.true) (1049 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ nat35 (EquationRowCuts.embedded_forward _ _ (1049 : Fin 1059) nat41))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine` at tape 1049. -/
theorem nat43 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine
  (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.true)) (1049 : Fin 1061) :=
  (CursorRestore.repeat_forward _ _ (1049 : Fin 1060) nat42)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop` at tape 1049. -/
theorem nat44 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop Bool.true) (1049 : Fin 1061) :=
  nat43

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine` at tape 1688. -/
theorem nat45 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine Bool.true) (1688 : Fin 1704) :=
  (CursorRestore.focus_forward _ CloseoutRowsSupportStream.Dock.slots_injective _ (1049 : Fin 1061) nat44)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem nat46 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1689) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem nat47 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1690) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.first` at tape 1688. -/
theorem nat48 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat46 nat47)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem nat49 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 297) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.second` at tape 1688. -/
theorem nat50 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.second) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat48 nat49)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem nat51 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 1692) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.third` at tape 1688. -/
theorem nat52 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.third) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat50 nat51)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker` at tape 1688. -/
theorem nat53 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.worker 624) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.machine` at tape 1688. -/
theorem nat54 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitReturnHeads.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat52 nat53)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned` at tape 1688. -/
theorem nat55 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned Bool.true) (1688 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ nat45 (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) nat54))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem nat56 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 0) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem nat57 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 1) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.first` at tape 1688. -/
theorem nat58 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.first) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat56 nat57)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy` at tape 1688. -/
theorem nat59 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.copy 2) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.machine` at tape 1688. -/
theorem nat60 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceCopies.machine) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat58 nat59)

/-- `Sigma.snd` at tape 1688. -/
theorem nat61 : CursorRestore.NoLeft ((NearCubicWires.RepairOrdinary.CloseoutRowsCircuitArithmeticDock.stage Bool.true).snd) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.first` at tape 1688. -/
theorem nat62 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.first Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat60 nat61)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.description` at tape 1688. -/
theorem nat63 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.description Bool.true) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.wires` at tape 1688. -/
theorem nat64 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.wires) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.first` at tape 1688. -/
theorem nat65 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.first Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat63 nat64)

theorem nat66 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.finish) (1688 : Fin 1703) :=
  (EquationRowCuts.unselected_forward _ _ _ (by decide))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.machine` at tape 1688. -/
theorem nat67 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps.machine Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat65 nat66)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.machine` at tape 1688. -/
theorem nat68 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsCircuitResourceRun.machine Bool.true) (1688 : Fin 1703) :=
  (CursorRestore.composition_forward _ _ _ nat62 nat67)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail` at tape 1688. -/
theorem nat69 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail Bool.true) (1688 : Fin 1704) :=
  (pair_forward _ _ _ _ nat55 (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) nat68))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body` at tape 1688. -/
theorem nat70 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body Bool.true) (1688 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) nat22) nat69)

/-- `Sigma.snd` at tape 1688. -/
theorem nat71 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.program.snd) (1688 : Fin 1704) :=
  (pair_forward _ _ _ _ (EquationRowCuts.embedded_forward _ _ (1688 : Fin 1703) nat11) nat70)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.machine` at tape 1688. -/
theorem nat72 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.machine) (1688 : Fin 1704) :=
  nat71

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append` at tape 1059. -/
theorem sup0 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.append) (1059 : Fin 1060) :=
  (CursorRestore.focus_forward _ (by decide) _ (1 : Fin 3) RecoveryPCPFormulaResumeForward.field_append)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice` at tape 1059. -/
theorem sup1 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.choice Bool.true) (1059 : Fin 1060) :=
  (pair_forward _ _ _ _ (halt_forward _ _ (fun _ _ => rfl)) sup0)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine` at tape 1059. -/
theorem sup2 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.prefixMachine Bool.true) (1059 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) sup1)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round` at tape 1059. -/
theorem sup3 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.true) (1059 : Fin 1060) :=
  (CursorRestore.composition_forward _ _ _ sup2 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine` at tape 1059. -/
theorem sup4 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsDegreeLoop.machine
  (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.round Bool.true)) (1059 : Fin 1061) :=
  (CursorRestore.repeat_forward _ _ (1059 : Fin 1060) sup3)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop` at tape 1059. -/
theorem sup5 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.loop Bool.true) (1059 : Fin 1061) :=
  sup4

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine` at tape 1703. -/
theorem sup6 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.machine Bool.true) (1703 : Fin 1704) :=
  (CursorRestore.focus_forward _ CloseoutRowsSupportStream.Dock.slots_injective _ (1059 : Fin 1061) sup5)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned` at tape 1703. -/
theorem sup7 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock.returned Bool.true) (1703 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ sup6 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail` at tape 1703. -/
theorem sup8 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.tail Bool.true) (1703 : Fin 1704) :=
  (pair_forward _ _ _ _ sup7 (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)))

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body` at tape 1703. -/
theorem sup9 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.body Bool.true) (1703 : Fin 1704) :=
  (CursorRestore.composition_forward _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) sup8)

/-- `Sigma.snd` at tape 1703. -/
theorem sup10 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.program.snd) (1703 : Fin 1704) :=
  (pair_forward _ _ _ _ (EquationRowRaw.embedded_extra_forward _ (0 : Fin 1)) sup9)

/-- `NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.machine` at tape 1703. -/
theorem sup11 : CursorRestore.NoLeft (NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold.machine) (1703 : Fin 1704) :=
  sup10

/-- **The original THR writer's native cursor (tape 1688) never moves left.** -/
theorem native_forward :
    CursorRestore.NoLeft CloseoutRowsSupportStream.Threshold.machine (1688 : Fin 1704) := nat72

/-- **The original THR writer's support cursor (tape 1703) never moves left.** -/
theorem support_forward :
    CursorRestore.NoLeft CloseoutRowsSupportStream.Threshold.machine (1703 : Fin 1704) := sup11

end NearCubicWires.SourceRequest.ThrOriginalForward

