import Proof.Wire_3_5.CompilerMachineEmitRun
import Proof.MachineModel.GeneratedAmplifierCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

/-- The record of eleven framed fields. -/
def loadRec (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) : List Bool :=
  frame f0 ++ (frame f1 ++ (frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++
    (frame f9 ++ frame f10)))))))))

/-- **Unframe onto an empty tape** (base's `GeneratedAmplifier.Copy`): the content of the framed field at the source
cursor is written on the empty target; the source cursor stops one cell past the field. -/
theorem unframeStep0 (pre bits tail : List Bool) :
    Step GeneratedAmplifier.Copy.machine (2 * bits.length + 1) ![pre.length, 0] ![pre ++ frame bits ++ tail, []]
      ![pre.length + 2 * bits.length + 1, bits.length] ![pre ++ frame bits ++ tail, bits] := by
  obtain ⟨r, hr, hf, hs⟩ := GeneratedAmplifier.Copy.copy_run pre bits tail []
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩

/-! ## The slot maps of the load layout

Tapes: 0 the input, 1 the record, 2 `1^{Q'}`, 3 `1^{P_ex}`, 4 `1^m`, 5 `1^h`, 6 `1^{p+1}`, 7 `1^{width}`, 8 the pool
stream, 9 the children table, 10 the expression, 11 and 12 the framed header parts. -/

def lIn : Fin 2 → Fin 13 := ![0, 1]
def lF0 : Fin 2 → Fin 13 := ![1, 2]
def lF1 : Fin 2 → Fin 13 := ![1, 3]
def lF2 : Fin 2 → Fin 13 := ![1, 4]
def lF3 : Fin 2 → Fin 13 := ![1, 5]
def lF4 : Fin 2 → Fin 13 := ![1, 6]
def lF5 : Fin 2 → Fin 13 := ![1, 7]
def lF6 : Fin 2 → Fin 13 := ![1, 8]
def lF7 : Fin 2 → Fin 13 := ![1, 9]
def lF8 : Fin 2 → Fin 13 := ![1, 10]
def lF9 : Fin 2 → Fin 13 := ![1, 11]
def lF10 : Fin 2 → Fin 13 := ![1, 12]

theorem lIn_inj : Function.Injective lIn := by decide

theorem install_lIn (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lIn A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_slot lIn lIn_inj A v 0
  · exact install_slot lIn lIn_inj A v 1
  · exact install_other lIn A v 2 (by decide)
  · exact install_other lIn A v 3 (by decide)
  · exact install_other lIn A v 4 (by decide)
  · exact install_other lIn A v 5 (by decide)
  · exact install_other lIn A v 6 (by decide)
  · exact install_other lIn A v 7 (by decide)
  · exact install_other lIn A v 8 (by decide)
  · exact install_other lIn A v 9 (by decide)
  · exact install_other lIn A v 10 (by decide)
  · exact install_other lIn A v 11 (by decide)
  · exact install_other lIn A v 12 (by decide)

theorem dockH_lIn (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lIn H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_slot lIn lIn_inj H v 0
  · exact dockH_slot lIn lIn_inj H v 1
  · exact dockH_other lIn H v 2 (by decide)
  · exact dockH_other lIn H v 3 (by decide)
  · exact dockH_other lIn H v 4 (by decide)
  · exact dockH_other lIn H v 5 (by decide)
  · exact dockH_other lIn H v 6 (by decide)
  · exact dockH_other lIn H v 7 (by decide)
  · exact dockH_other lIn H v 8 (by decide)
  · exact dockH_other lIn H v 9 (by decide)
  · exact dockH_other lIn H v 10 (by decide)
  · exact dockH_other lIn H v 11 (by decide)
  · exact dockH_other lIn H v 12 (by decide)

theorem lF0_inj : Function.Injective lF0 := by decide

theorem install_lF0 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF0 A v = ![A 0, v 0, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF0 A v 0 (by decide)
  · exact install_slot lF0 lF0_inj A v 0
  · exact install_slot lF0 lF0_inj A v 1
  · exact install_other lF0 A v 3 (by decide)
  · exact install_other lF0 A v 4 (by decide)
  · exact install_other lF0 A v 5 (by decide)
  · exact install_other lF0 A v 6 (by decide)
  · exact install_other lF0 A v 7 (by decide)
  · exact install_other lF0 A v 8 (by decide)
  · exact install_other lF0 A v 9 (by decide)
  · exact install_other lF0 A v 10 (by decide)
  · exact install_other lF0 A v 11 (by decide)
  · exact install_other lF0 A v 12 (by decide)

theorem dockH_lF0 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF0 H v = ![H 0, v 0, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF0 H v 0 (by decide)
  · exact dockH_slot lF0 lF0_inj H v 0
  · exact dockH_slot lF0 lF0_inj H v 1
  · exact dockH_other lF0 H v 3 (by decide)
  · exact dockH_other lF0 H v 4 (by decide)
  · exact dockH_other lF0 H v 5 (by decide)
  · exact dockH_other lF0 H v 6 (by decide)
  · exact dockH_other lF0 H v 7 (by decide)
  · exact dockH_other lF0 H v 8 (by decide)
  · exact dockH_other lF0 H v 9 (by decide)
  · exact dockH_other lF0 H v 10 (by decide)
  · exact dockH_other lF0 H v 11 (by decide)
  · exact dockH_other lF0 H v 12 (by decide)

theorem lF1_inj : Function.Injective lF1 := by decide

theorem install_lF1 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF1 A v = ![A 0, v 0, A 2, v 1, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF1 A v 0 (by decide)
  · exact install_slot lF1 lF1_inj A v 0
  · exact install_other lF1 A v 2 (by decide)
  · exact install_slot lF1 lF1_inj A v 1
  · exact install_other lF1 A v 4 (by decide)
  · exact install_other lF1 A v 5 (by decide)
  · exact install_other lF1 A v 6 (by decide)
  · exact install_other lF1 A v 7 (by decide)
  · exact install_other lF1 A v 8 (by decide)
  · exact install_other lF1 A v 9 (by decide)
  · exact install_other lF1 A v 10 (by decide)
  · exact install_other lF1 A v 11 (by decide)
  · exact install_other lF1 A v 12 (by decide)

theorem dockH_lF1 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF1 H v = ![H 0, v 0, H 2, v 1, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF1 H v 0 (by decide)
  · exact dockH_slot lF1 lF1_inj H v 0
  · exact dockH_other lF1 H v 2 (by decide)
  · exact dockH_slot lF1 lF1_inj H v 1
  · exact dockH_other lF1 H v 4 (by decide)
  · exact dockH_other lF1 H v 5 (by decide)
  · exact dockH_other lF1 H v 6 (by decide)
  · exact dockH_other lF1 H v 7 (by decide)
  · exact dockH_other lF1 H v 8 (by decide)
  · exact dockH_other lF1 H v 9 (by decide)
  · exact dockH_other lF1 H v 10 (by decide)
  · exact dockH_other lF1 H v 11 (by decide)
  · exact dockH_other lF1 H v 12 (by decide)

theorem lF2_inj : Function.Injective lF2 := by decide

theorem install_lF2 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF2 A v = ![A 0, v 0, A 2, A 3, v 1, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF2 A v 0 (by decide)
  · exact install_slot lF2 lF2_inj A v 0
  · exact install_other lF2 A v 2 (by decide)
  · exact install_other lF2 A v 3 (by decide)
  · exact install_slot lF2 lF2_inj A v 1
  · exact install_other lF2 A v 5 (by decide)
  · exact install_other lF2 A v 6 (by decide)
  · exact install_other lF2 A v 7 (by decide)
  · exact install_other lF2 A v 8 (by decide)
  · exact install_other lF2 A v 9 (by decide)
  · exact install_other lF2 A v 10 (by decide)
  · exact install_other lF2 A v 11 (by decide)
  · exact install_other lF2 A v 12 (by decide)

theorem dockH_lF2 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF2 H v = ![H 0, v 0, H 2, H 3, v 1, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF2 H v 0 (by decide)
  · exact dockH_slot lF2 lF2_inj H v 0
  · exact dockH_other lF2 H v 2 (by decide)
  · exact dockH_other lF2 H v 3 (by decide)
  · exact dockH_slot lF2 lF2_inj H v 1
  · exact dockH_other lF2 H v 5 (by decide)
  · exact dockH_other lF2 H v 6 (by decide)
  · exact dockH_other lF2 H v 7 (by decide)
  · exact dockH_other lF2 H v 8 (by decide)
  · exact dockH_other lF2 H v 9 (by decide)
  · exact dockH_other lF2 H v 10 (by decide)
  · exact dockH_other lF2 H v 11 (by decide)
  · exact dockH_other lF2 H v 12 (by decide)

theorem lF3_inj : Function.Injective lF3 := by decide

theorem install_lF3 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF3 A v = ![A 0, v 0, A 2, A 3, A 4, v 1, A 6, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF3 A v 0 (by decide)
  · exact install_slot lF3 lF3_inj A v 0
  · exact install_other lF3 A v 2 (by decide)
  · exact install_other lF3 A v 3 (by decide)
  · exact install_other lF3 A v 4 (by decide)
  · exact install_slot lF3 lF3_inj A v 1
  · exact install_other lF3 A v 6 (by decide)
  · exact install_other lF3 A v 7 (by decide)
  · exact install_other lF3 A v 8 (by decide)
  · exact install_other lF3 A v 9 (by decide)
  · exact install_other lF3 A v 10 (by decide)
  · exact install_other lF3 A v 11 (by decide)
  · exact install_other lF3 A v 12 (by decide)

theorem dockH_lF3 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF3 H v = ![H 0, v 0, H 2, H 3, H 4, v 1, H 6, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF3 H v 0 (by decide)
  · exact dockH_slot lF3 lF3_inj H v 0
  · exact dockH_other lF3 H v 2 (by decide)
  · exact dockH_other lF3 H v 3 (by decide)
  · exact dockH_other lF3 H v 4 (by decide)
  · exact dockH_slot lF3 lF3_inj H v 1
  · exact dockH_other lF3 H v 6 (by decide)
  · exact dockH_other lF3 H v 7 (by decide)
  · exact dockH_other lF3 H v 8 (by decide)
  · exact dockH_other lF3 H v 9 (by decide)
  · exact dockH_other lF3 H v 10 (by decide)
  · exact dockH_other lF3 H v 11 (by decide)
  · exact dockH_other lF3 H v 12 (by decide)

theorem lF4_inj : Function.Injective lF4 := by decide

theorem install_lF4 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF4 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, v 1, A 7, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF4 A v 0 (by decide)
  · exact install_slot lF4 lF4_inj A v 0
  · exact install_other lF4 A v 2 (by decide)
  · exact install_other lF4 A v 3 (by decide)
  · exact install_other lF4 A v 4 (by decide)
  · exact install_other lF4 A v 5 (by decide)
  · exact install_slot lF4 lF4_inj A v 1
  · exact install_other lF4 A v 7 (by decide)
  · exact install_other lF4 A v 8 (by decide)
  · exact install_other lF4 A v 9 (by decide)
  · exact install_other lF4 A v 10 (by decide)
  · exact install_other lF4 A v 11 (by decide)
  · exact install_other lF4 A v 12 (by decide)

theorem dockH_lF4 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF4 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, v 1, H 7, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF4 H v 0 (by decide)
  · exact dockH_slot lF4 lF4_inj H v 0
  · exact dockH_other lF4 H v 2 (by decide)
  · exact dockH_other lF4 H v 3 (by decide)
  · exact dockH_other lF4 H v 4 (by decide)
  · exact dockH_other lF4 H v 5 (by decide)
  · exact dockH_slot lF4 lF4_inj H v 1
  · exact dockH_other lF4 H v 7 (by decide)
  · exact dockH_other lF4 H v 8 (by decide)
  · exact dockH_other lF4 H v 9 (by decide)
  · exact dockH_other lF4 H v 10 (by decide)
  · exact dockH_other lF4 H v 11 (by decide)
  · exact dockH_other lF4 H v 12 (by decide)

theorem lF5_inj : Function.Injective lF5 := by decide

theorem install_lF5 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF5 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, v 1, A 8, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF5 A v 0 (by decide)
  · exact install_slot lF5 lF5_inj A v 0
  · exact install_other lF5 A v 2 (by decide)
  · exact install_other lF5 A v 3 (by decide)
  · exact install_other lF5 A v 4 (by decide)
  · exact install_other lF5 A v 5 (by decide)
  · exact install_other lF5 A v 6 (by decide)
  · exact install_slot lF5 lF5_inj A v 1
  · exact install_other lF5 A v 8 (by decide)
  · exact install_other lF5 A v 9 (by decide)
  · exact install_other lF5 A v 10 (by decide)
  · exact install_other lF5 A v 11 (by decide)
  · exact install_other lF5 A v 12 (by decide)

theorem dockH_lF5 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF5 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, v 1, H 8, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF5 H v 0 (by decide)
  · exact dockH_slot lF5 lF5_inj H v 0
  · exact dockH_other lF5 H v 2 (by decide)
  · exact dockH_other lF5 H v 3 (by decide)
  · exact dockH_other lF5 H v 4 (by decide)
  · exact dockH_other lF5 H v 5 (by decide)
  · exact dockH_other lF5 H v 6 (by decide)
  · exact dockH_slot lF5 lF5_inj H v 1
  · exact dockH_other lF5 H v 8 (by decide)
  · exact dockH_other lF5 H v 9 (by decide)
  · exact dockH_other lF5 H v 10 (by decide)
  · exact dockH_other lF5 H v 11 (by decide)
  · exact dockH_other lF5 H v 12 (by decide)

theorem lF6_inj : Function.Injective lF6 := by decide

theorem install_lF6 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF6 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, v 1, A 9, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF6 A v 0 (by decide)
  · exact install_slot lF6 lF6_inj A v 0
  · exact install_other lF6 A v 2 (by decide)
  · exact install_other lF6 A v 3 (by decide)
  · exact install_other lF6 A v 4 (by decide)
  · exact install_other lF6 A v 5 (by decide)
  · exact install_other lF6 A v 6 (by decide)
  · exact install_other lF6 A v 7 (by decide)
  · exact install_slot lF6 lF6_inj A v 1
  · exact install_other lF6 A v 9 (by decide)
  · exact install_other lF6 A v 10 (by decide)
  · exact install_other lF6 A v 11 (by decide)
  · exact install_other lF6 A v 12 (by decide)

theorem dockH_lF6 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF6 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, v 1, H 9, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF6 H v 0 (by decide)
  · exact dockH_slot lF6 lF6_inj H v 0
  · exact dockH_other lF6 H v 2 (by decide)
  · exact dockH_other lF6 H v 3 (by decide)
  · exact dockH_other lF6 H v 4 (by decide)
  · exact dockH_other lF6 H v 5 (by decide)
  · exact dockH_other lF6 H v 6 (by decide)
  · exact dockH_other lF6 H v 7 (by decide)
  · exact dockH_slot lF6 lF6_inj H v 1
  · exact dockH_other lF6 H v 9 (by decide)
  · exact dockH_other lF6 H v 10 (by decide)
  · exact dockH_other lF6 H v 11 (by decide)
  · exact dockH_other lF6 H v 12 (by decide)

theorem lF7_inj : Function.Injective lF7 := by decide

theorem install_lF7 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF7 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 1, A 10, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF7 A v 0 (by decide)
  · exact install_slot lF7 lF7_inj A v 0
  · exact install_other lF7 A v 2 (by decide)
  · exact install_other lF7 A v 3 (by decide)
  · exact install_other lF7 A v 4 (by decide)
  · exact install_other lF7 A v 5 (by decide)
  · exact install_other lF7 A v 6 (by decide)
  · exact install_other lF7 A v 7 (by decide)
  · exact install_other lF7 A v 8 (by decide)
  · exact install_slot lF7 lF7_inj A v 1
  · exact install_other lF7 A v 10 (by decide)
  · exact install_other lF7 A v 11 (by decide)
  · exact install_other lF7 A v 12 (by decide)

theorem dockH_lF7 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF7 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 1, H 10, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF7 H v 0 (by decide)
  · exact dockH_slot lF7 lF7_inj H v 0
  · exact dockH_other lF7 H v 2 (by decide)
  · exact dockH_other lF7 H v 3 (by decide)
  · exact dockH_other lF7 H v 4 (by decide)
  · exact dockH_other lF7 H v 5 (by decide)
  · exact dockH_other lF7 H v 6 (by decide)
  · exact dockH_other lF7 H v 7 (by decide)
  · exact dockH_other lF7 H v 8 (by decide)
  · exact dockH_slot lF7 lF7_inj H v 1
  · exact dockH_other lF7 H v 10 (by decide)
  · exact dockH_other lF7 H v 11 (by decide)
  · exact dockH_other lF7 H v 12 (by decide)

theorem lF8_inj : Function.Injective lF8 := by decide

theorem install_lF8 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF8 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 1, A 11, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF8 A v 0 (by decide)
  · exact install_slot lF8 lF8_inj A v 0
  · exact install_other lF8 A v 2 (by decide)
  · exact install_other lF8 A v 3 (by decide)
  · exact install_other lF8 A v 4 (by decide)
  · exact install_other lF8 A v 5 (by decide)
  · exact install_other lF8 A v 6 (by decide)
  · exact install_other lF8 A v 7 (by decide)
  · exact install_other lF8 A v 8 (by decide)
  · exact install_other lF8 A v 9 (by decide)
  · exact install_slot lF8 lF8_inj A v 1
  · exact install_other lF8 A v 11 (by decide)
  · exact install_other lF8 A v 12 (by decide)

theorem dockH_lF8 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF8 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 1, H 11, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF8 H v 0 (by decide)
  · exact dockH_slot lF8 lF8_inj H v 0
  · exact dockH_other lF8 H v 2 (by decide)
  · exact dockH_other lF8 H v 3 (by decide)
  · exact dockH_other lF8 H v 4 (by decide)
  · exact dockH_other lF8 H v 5 (by decide)
  · exact dockH_other lF8 H v 6 (by decide)
  · exact dockH_other lF8 H v 7 (by decide)
  · exact dockH_other lF8 H v 8 (by decide)
  · exact dockH_other lF8 H v 9 (by decide)
  · exact dockH_slot lF8 lF8_inj H v 1
  · exact dockH_other lF8 H v 11 (by decide)
  · exact dockH_other lF8 H v 12 (by decide)

theorem lF9_inj : Function.Injective lF9 := by decide

theorem install_lF9 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF9 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 1, A 12] := by
  funext i
  fin_cases i
  · exact install_other lF9 A v 0 (by decide)
  · exact install_slot lF9 lF9_inj A v 0
  · exact install_other lF9 A v 2 (by decide)
  · exact install_other lF9 A v 3 (by decide)
  · exact install_other lF9 A v 4 (by decide)
  · exact install_other lF9 A v 5 (by decide)
  · exact install_other lF9 A v 6 (by decide)
  · exact install_other lF9 A v 7 (by decide)
  · exact install_other lF9 A v 8 (by decide)
  · exact install_other lF9 A v 9 (by decide)
  · exact install_other lF9 A v 10 (by decide)
  · exact install_slot lF9 lF9_inj A v 1
  · exact install_other lF9 A v 12 (by decide)

theorem dockH_lF9 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF9 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 1, H 12] := by
  funext i
  fin_cases i
  · exact dockH_other lF9 H v 0 (by decide)
  · exact dockH_slot lF9 lF9_inj H v 0
  · exact dockH_other lF9 H v 2 (by decide)
  · exact dockH_other lF9 H v 3 (by decide)
  · exact dockH_other lF9 H v 4 (by decide)
  · exact dockH_other lF9 H v 5 (by decide)
  · exact dockH_other lF9 H v 6 (by decide)
  · exact dockH_other lF9 H v 7 (by decide)
  · exact dockH_other lF9 H v 8 (by decide)
  · exact dockH_other lF9 H v 9 (by decide)
  · exact dockH_other lF9 H v 10 (by decide)
  · exact dockH_slot lF9 lF9_inj H v 1
  · exact dockH_other lF9 H v 12 (by decide)

theorem lF10_inj : Function.Injective lF10 := by decide

theorem install_lF10 (A : Fin 13 → List Bool) (v : Fin 2 → List Bool) :
    install lF10 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 1] := by
  funext i
  fin_cases i
  · exact install_other lF10 A v 0 (by decide)
  · exact install_slot lF10 lF10_inj A v 0
  · exact install_other lF10 A v 2 (by decide)
  · exact install_other lF10 A v 3 (by decide)
  · exact install_other lF10 A v 4 (by decide)
  · exact install_other lF10 A v 5 (by decide)
  · exact install_other lF10 A v 6 (by decide)
  · exact install_other lF10 A v 7 (by decide)
  · exact install_other lF10 A v 8 (by decide)
  · exact install_other lF10 A v 9 (by decide)
  · exact install_other lF10 A v 10 (by decide)
  · exact install_other lF10 A v 11 (by decide)
  · exact install_slot lF10 lF10_inj A v 1

theorem dockH_lF10 (H : Fin 13 → ℕ) (v : Fin 2 → ℕ) :
    dockH lF10 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other lF10 H v 0 (by decide)
  · exact dockH_slot lF10 lF10_inj H v 0
  · exact dockH_other lF10 H v 2 (by decide)
  · exact dockH_other lF10 H v 3 (by decide)
  · exact dockH_other lF10 H v 4 (by decide)
  · exact dockH_other lF10 H v 5 (by decide)
  · exact dockH_other lF10 H v 6 (by decide)
  · exact dockH_other lF10 H v 7 (by decide)
  · exact dockH_other lF10 H v 8 (by decide)
  · exact dockH_other lF10 H v 9 (by decide)
  · exact dockH_other lF10 H v 10 (by decide)
  · exact dockH_other lF10 H v 11 (by decide)
  · exact dockH_slot lF10 lF10_inj H v 1

noncomputable def lInD := RecoveryFocus.machine lIn GeneratedAmplifier.Copy.machine
noncomputable def lF0D := RecoveryFocus.machine lF0 GeneratedAmplifier.Copy.machine
noncomputable def lF1D := RecoveryFocus.machine lF1 GeneratedAmplifier.Copy.machine
noncomputable def lF2D := RecoveryFocus.machine lF2 GeneratedAmplifier.Copy.machine
noncomputable def lF3D := RecoveryFocus.machine lF3 GeneratedAmplifier.Copy.machine
noncomputable def lF4D := RecoveryFocus.machine lF4 GeneratedAmplifier.Copy.machine
noncomputable def lF5D := RecoveryFocus.machine lF5 GeneratedAmplifier.Copy.machine
noncomputable def lF6D := RecoveryFocus.machine lF6 GeneratedAmplifier.Copy.machine
noncomputable def lF7D := RecoveryFocus.machine lF7 GeneratedAmplifier.Copy.machine
noncomputable def lF8D := RecoveryFocus.machine lF8 GeneratedAmplifier.Copy.machine
noncomputable def lF9D := RecoveryFocus.machine lF9 GeneratedAmplifier.Copy.machine
noncomputable def lF10D := RecoveryFocus.machine lF10 GeneratedAmplifier.Copy.machine

/-- The field loads, in record order. -/
noncomputable def loadChainM := Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (lF0D) lF1D) lF2D) lF3D) lF4D) lF5D) lF6D) lF7D) lF8D) lF9D) lF10D

/-- The cost of the field loads. -/
def loadChainCost (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) : ℕ :=
  (2 * f0.length + 1) + 1 + (2 * f1.length + 1) + 1 + (2 * f2.length + 1) + 1 + (2 * f3.length + 1) + 1 + (2 * f4.length + 1) + 1 + (2 * f5.length + 1) + 1 + (2 * f6.length + 1) + 1 + (2 * f7.length + 1) + 1 + (2 * f8.length + 1) + 1 + (2 * f9.length + 1) + 1 + (2 * f10.length + 1)

theorem rec_split0 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = ([] : List Bool) ++ frame f0 ++ (frame f1 ++ (frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))))))) := by
  simp only [loadRec, List.nil_append]

theorem rec_split1 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = frame f0 ++ frame f1 ++ (frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))))))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split2 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = (frame f0 ++ frame f1) ++ frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split3 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = ((frame f0 ++ frame f1) ++ frame f2) ++ frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split4 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = (((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split5 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split6 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split7 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split8 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8 ++ (frame f9 ++ frame f10) := by
  simp only [loadRec, List.append_assoc]

theorem rec_split9 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9 ++ frame f10 := by
  simp only [loadRec, List.append_assoc]

theorem rec_split10 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9) ++ frame f10 ++ [] := by
  simp only [loadRec, List.append_assoc, List.append_nil]

theorem rec_off0 (f0 : List Bool) :
    (([] : List Bool)).length + 2 * f0.length + 1 = (frame f0).length := by
  simp only [List.length_nil, frame_length]; omega

theorem rec_off1 (f0 f1 : List Bool) :
    (frame f0).length + 2 * f1.length + 1 = ((frame f0 ++ frame f1)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off2 (f0 f1 f2 : List Bool) :
    ((frame f0 ++ frame f1)).length + 2 * f2.length + 1 = (((frame f0 ++ frame f1) ++ frame f2)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off3 (f0 f1 f2 f3 : List Bool) :
    (((frame f0 ++ frame f1) ++ frame f2)).length + 2 * f3.length + 1 = ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off4 (f0 f1 f2 f3 f4 : List Bool) :
    ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)).length + 2 * f4.length + 1 = (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off5 (f0 f1 f2 f3 f4 f5 : List Bool) :
    (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)).length + 2 * f5.length + 1 = ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off6 (f0 f1 f2 f3 f4 f5 f6 : List Bool) :
    ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)).length + 2 * f6.length + 1 = (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off7 (f0 f1 f2 f3 f4 f5 f6 f7 : List Bool) :
    (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)).length + 2 * f7.length + 1 = ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off8 (f0 f1 f2 f3 f4 f5 f6 f7 f8 : List Bool) :
    ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)).length + 2 * f8.length + 1 = (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)).length := by
  simp only [List.length_append, frame_length]; omega

theorem rec_off9 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : List Bool) :
    (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)).length + 2 * f9.length + 1 = ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length := by
  simp only [List.length_append, frame_length]; omega

/-- **The field loads**: every field of the record is unframed onto its own tape, in record order. -/
theorem chain_run (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    Step loadChainM (loadChainCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], []]
      ![0, ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length + 2 * f10.length + 1, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, f9.length, f10.length]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] := by
  have e0 := unframeStep0 (([] : List Bool)) f0 ((frame f1 ++ (frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))))))))
  rw [← rec_split0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off0 f0] at e0
  have s0 := dockRun e0 lF0 lF0_inj ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF0, dockH_lF0] at s0
  have t0 : Step lF0D (2 * f0.length + 1) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], []]
      ![0, (frame f0).length, f0.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, [], [], [], [], [], [], [], [], [], []] :=
    s0.congr rfl rfl
  have e1 := unframeStep0 (frame f0) f1 ((frame f2 ++ (frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))))))))
  rw [← rec_split1 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off1 f0 f1] at e1
  have s1 := dockRun e1 lF1 lF1_inj ![0, (frame f0).length, f0.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, [], [], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF1, dockH_lF1] at s1
  have t1 : Step lF1D (2 * f1.length + 1) ![0, (frame f0).length, f0.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, [], [], [], [], [], [], [], [], [], []]
      ![0, ((frame f0 ++ frame f1)).length, f0.length, f1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, [], [], [], [], [], [], [], [], []] :=
    s1.congr rfl rfl
  have e2 := unframeStep0 ((frame f0 ++ frame f1)) f2 ((frame f3 ++ (frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))))))
  rw [← rec_split2 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off2 f0 f1 f2] at e2
  have s2 := dockRun e2 lF2 lF2_inj ![0, ((frame f0 ++ frame f1)).length, f0.length, f1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, [], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF2, dockH_lF2] at s2
  have t2 : Step lF2D (2 * f2.length + 1) ![0, ((frame f0 ++ frame f1)).length, f0.length, f1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, [], [], [], [], [], [], [], [], []]
      ![0, (((frame f0 ++ frame f1) ++ frame f2)).length, f0.length, f1.length, f2.length, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, [], [], [], [], [], [], [], []] :=
    s2.congr rfl rfl
  have e3 := unframeStep0 (((frame f0 ++ frame f1) ++ frame f2)) f3 ((frame f4 ++ (frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))))))
  rw [← rec_split3 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off3 f0 f1 f2 f3] at e3
  have s3 := dockRun e3 lF3 lF3_inj ![0, (((frame f0 ++ frame f1) ++ frame f2)).length, f0.length, f1.length, f2.length, 0, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF3, dockH_lF3] at s3
  have t3 : Step lF3D (2 * f3.length + 1) ![0, (((frame f0 ++ frame f1) ++ frame f2)).length, f0.length, f1.length, f2.length, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, [], [], [], [], [], [], [], []]
      ![0, ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)).length, f0.length, f1.length, f2.length, f3.length, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, [], [], [], [], [], [], []] :=
    s3.congr rfl rfl
  have e4 := unframeStep0 ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)) f4 ((frame f5 ++ (frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))))
  rw [← rec_split4 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off4 f0 f1 f2 f3 f4] at e4
  have s4 := dockRun e4 lF4 lF4_inj ![0, ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)).length, f0.length, f1.length, f2.length, f3.length, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF4, dockH_lF4] at s4
  have t4 : Step lF4D (2 * f4.length + 1) ![0, ((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3)).length, f0.length, f1.length, f2.length, f3.length, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, [], [], [], [], [], [], []]
      ![0, (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)).length, f0.length, f1.length, f2.length, f3.length, f4.length, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, [], [], [], [], [], []] :=
    s4.congr rfl rfl
  have e5 := unframeStep0 (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)) f5 ((frame f6 ++ (frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10)))))
  rw [← rec_split5 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off5 f0 f1 f2 f3 f4 f5] at e5
  have s5 := dockRun e5 lF5 lF5_inj ![0, (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)).length, f0.length, f1.length, f2.length, f3.length, f4.length, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF5, dockH_lF5] at s5
  have t5 : Step lF5D (2 * f5.length + 1) ![0, (((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4)).length, f0.length, f1.length, f2.length, f3.length, f4.length, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, [], [], [], [], [], []]
      ![0, ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, [], [], [], [], []] :=
    s5.congr rfl rfl
  have e6 := unframeStep0 ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)) f6 ((frame f7 ++ (frame f8 ++ (frame f9 ++ frame f10))))
  rw [← rec_split6 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off6 f0 f1 f2 f3 f4 f5 f6] at e6
  have s6 := dockRun e6 lF6 lF6_inj ![0, ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF6, dockH_lF6] at s6
  have t6 : Step lF6D (2 * f6.length + 1) ![0, ((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, [], [], [], [], []]
      ![0, (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, [], [], [], []] :=
    s6.congr rfl rfl
  have e7 := unframeStep0 (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)) f7 ((frame f8 ++ (frame f9 ++ frame f10)))
  rw [← rec_split7 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off7 f0 f1 f2 f3 f4 f5 f6 f7] at e7
  have s7 := dockRun e7 lF7 lF7_inj ![0, (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF7, dockH_lF7] at s7
  have t7 : Step lF7D (2 * f7.length + 1) ![0, (((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, [], [], [], []]
      ![0, ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, [], [], []] :=
    s7.congr rfl rfl
  have e8 := unframeStep0 ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)) f8 ((frame f9 ++ frame f10))
  rw [← rec_split8 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off8 f0 f1 f2 f3 f4 f5 f6 f7 f8] at e8
  have s8 := dockRun e8 lF8 lF8_inj ![0, ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF8, dockH_lF8] at s8
  have t8 : Step lF8D (2 * f8.length + 1) ![0, ((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, [], [], []]
      ![0, (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, [], []] :=
    s8.congr rfl rfl
  have e9 := unframeStep0 (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)) f9 (frame f10)
  rw [← rec_split9 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10, rec_off9 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9] at e9
  have s9 := dockRun e9 lF9 lF9_inj ![0, (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF9, dockH_lF9] at s9
  have t9 : Step lF9D (2 * f9.length + 1) ![0, (((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, [], []]
      ![0, ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, f9.length, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, []] :=
    s9.congr rfl rfl
  have e10 := unframeStep0 ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)) f10 ([])
  rw [← rec_split10 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10] at e10
  have s10 := dockRun e10 lF10 lF10_inj ![0, ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, f9.length, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lF10, dockH_lF10] at s10
  have t10 : Step lF10D (2 * f10.length + 1) ![0, ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, f9.length, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, []]
      ![0, ((((((((((frame f0 ++ frame f1) ++ frame f2) ++ frame f3) ++ frame f4) ++ frame f5) ++ frame f6) ++ frame f7) ++ frame f8) ++ frame f9)).length + 2 * f10.length + 1, f0.length, f1.length, f2.length, f3.length, f4.length, f5.length, f6.length, f7.length, f8.length, f9.length, f10.length]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] :=
    s10.congr rfl rfl
  exact ((((((((((t0).seq t1).seq t2).seq t3).seq t4).seq t5).seq t6).seq t7).seq t8).seq t9).seq t10

/-- **The record's unframe**: tape 0's framed record is unframed onto tape 1. -/
theorem in_run (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    Step lInD (2 * (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 1) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], [], []]
      ![2 * (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 1, (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], []] := by
  have e := unframeStep0 [] (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at e
  have s := dockRun e lIn lIn_inj ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_lIn, dockH_lIn] at s
  exact s.congr rfl rfl

/-- The load: the record's unframe, then the field loads, each with every head returned to cell 0 (one shared log). -/
noncomputable def loadM := Composition.machine (MaskedReset.machine lInD (fun _ => true))
  (MaskedReset.machine loadChainM (fun _ => true))

/-- The load's cost. -/
def loadCost (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) : ℕ :=
  2 * (2 * (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 1) + 2 + 1 + (2 * loadChainCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 + 2)

theorem addCases_zero13 (H : Fin 13 → ℕ) (hH : ∀ i, H i = 0) :
    Fin.addCases (motive := fun _ => ℕ) H (fun _ : Fin 1 => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hH]

/-- **The load** (T1): from the word function's entry bank (the framed record on tape 0, the other tapes empty, the log
blank), the record is on tape 1 and field `k` on tape `k + 2`, every head at cell 0. -/
theorem load_run (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) (cap : ℕ) (hcap1 : 2 * (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 1 ≤ cap)
    (hcap2 : loadChainCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 ≤ cap) :
    Step loadM (loadCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) (fun _ => 0)
      (Fin.addCases ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases ![frame (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10), f0 , f1 , f2 , f3 , f4 , f5 , f6 , f7 , f8 , f9 , f10]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m1 := (in_run f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap1
  have m2 := (chain_run f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap2
  have z0 := addCases_zero13 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by intro i; fin_cases i <;> rfl)
  have m1' := (m1.congr_in z0 rfl).congr (addCases_zero13 _ (by intro i; fin_cases i <;> rfl)) rfl
  have m2' := (m2.congr_in z0 rfl).congr (addCases_zero13 _ (by intro i; fin_cases i <;> rfl)) rfl
  exact m1'.seq m2'

