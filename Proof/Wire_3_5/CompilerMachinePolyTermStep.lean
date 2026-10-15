import Proof.Wire_3_5.CompilerMachinePolyBlocks

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Slot maps and machines -/

def tV : Fin 1 → Fin 33 := ![0]
def tLoadCW : Fin 3 → Fin 33 := ![0, 20, 8]
def tG : Fin 1 → Fin 33 := ![12]
def tPJ : Fin 1 → Fin 33 := ![19]
def tJB : Fin 21 → Fin 33 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 32]
def tSp : Fin 1 → Fin 33 := ![21]
def tUn : Fin 14 → Fin 33 := ![21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 8, 9, 12, 10]
def tOut : Fin 1 → Fin 33 := ![31]
def tEmitCW : Fin 3 → Fin 33 := ![20, 31, 8]
def tApp : Fin 3 → Fin 33 := ![21, 31, 10]

noncomputable def tNudgeVD := RecoveryFocus.machine tV nudgeM
noncomputable def tLoadCWD := RecoveryFocus.machine tLoadCW loadM
noncomputable def tClrGD := RecoveryFocus.machine tG (cellM false)
noncomputable def tClrPJD := RecoveryFocus.machine tPJ (cellM false)
noncomputable def tJBD := RecoveryFocus.machine tJB jBlockRM
noncomputable def tClrSpD := RecoveryFocus.machine tSp (cellM false)
noncomputable def tUnD := RecoveryFocus.machine tUn unionsAllM
noncomputable def tPutTD := RecoveryFocus.machine tOut (putM true)
noncomputable def tPutFD := RecoveryFocus.machine tOut (putM false)
noncomputable def tEmitCWD := RecoveryFocus.machine tEmitCW emitM
noncomputable def tParityM := branchM 19 tPutTD tPutFD
noncomputable def tAppD := RecoveryFocus.machine tApp appOutRM

/-- Read the term's coefficient and substitute the counter's polarized polynomial. -/
noncomputable def termPart1M :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine tNudgeVD tLoadCWD) tNudgeVD) tClrGD) tClrPJD) tJBD) tNudgeVD

/-- Lift the cancelled polynomial and write the group. -/
noncomputable def termPart2M :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine tClrSpD tUnD) tPutTD) tEmitCWD) tPutTD) tParityM)
    tPutFD) tAppD) tPutFD

/-- **One term for one counter value.** -/
noncomputable def termM := Composition.machine termPart1M termPart2M

theorem tV_inj : Function.Injective tV := by decide

theorem install_tV (A : Fin 33 → List Bool) (v : Fin 1 → List Bool) :
    install tV A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_slot tV tV_inj A v 0
  · exact install_other tV A v 1 (by decide)
  · exact install_other tV A v 2 (by decide)
  · exact install_other tV A v 3 (by decide)
  · exact install_other tV A v 4 (by decide)
  · exact install_other tV A v 5 (by decide)
  · exact install_other tV A v 6 (by decide)
  · exact install_other tV A v 7 (by decide)
  · exact install_other tV A v 8 (by decide)
  · exact install_other tV A v 9 (by decide)
  · exact install_other tV A v 10 (by decide)
  · exact install_other tV A v 11 (by decide)
  · exact install_other tV A v 12 (by decide)
  · exact install_other tV A v 13 (by decide)
  · exact install_other tV A v 14 (by decide)
  · exact install_other tV A v 15 (by decide)
  · exact install_other tV A v 16 (by decide)
  · exact install_other tV A v 17 (by decide)
  · exact install_other tV A v 18 (by decide)
  · exact install_other tV A v 19 (by decide)
  · exact install_other tV A v 20 (by decide)
  · exact install_other tV A v 21 (by decide)
  · exact install_other tV A v 22 (by decide)
  · exact install_other tV A v 23 (by decide)
  · exact install_other tV A v 24 (by decide)
  · exact install_other tV A v 25 (by decide)
  · exact install_other tV A v 26 (by decide)
  · exact install_other tV A v 27 (by decide)
  · exact install_other tV A v 28 (by decide)
  · exact install_other tV A v 29 (by decide)
  · exact install_other tV A v 30 (by decide)
  · exact install_other tV A v 31 (by decide)
  · exact install_other tV A v 32 (by decide)

theorem dockH_tV (H : Fin 33 → ℕ) (v : Fin 1 → ℕ) :
    dockH tV H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_slot tV tV_inj H v 0
  · exact dockH_other tV H v 1 (by decide)
  · exact dockH_other tV H v 2 (by decide)
  · exact dockH_other tV H v 3 (by decide)
  · exact dockH_other tV H v 4 (by decide)
  · exact dockH_other tV H v 5 (by decide)
  · exact dockH_other tV H v 6 (by decide)
  · exact dockH_other tV H v 7 (by decide)
  · exact dockH_other tV H v 8 (by decide)
  · exact dockH_other tV H v 9 (by decide)
  · exact dockH_other tV H v 10 (by decide)
  · exact dockH_other tV H v 11 (by decide)
  · exact dockH_other tV H v 12 (by decide)
  · exact dockH_other tV H v 13 (by decide)
  · exact dockH_other tV H v 14 (by decide)
  · exact dockH_other tV H v 15 (by decide)
  · exact dockH_other tV H v 16 (by decide)
  · exact dockH_other tV H v 17 (by decide)
  · exact dockH_other tV H v 18 (by decide)
  · exact dockH_other tV H v 19 (by decide)
  · exact dockH_other tV H v 20 (by decide)
  · exact dockH_other tV H v 21 (by decide)
  · exact dockH_other tV H v 22 (by decide)
  · exact dockH_other tV H v 23 (by decide)
  · exact dockH_other tV H v 24 (by decide)
  · exact dockH_other tV H v 25 (by decide)
  · exact dockH_other tV H v 26 (by decide)
  · exact dockH_other tV H v 27 (by decide)
  · exact dockH_other tV H v 28 (by decide)
  · exact dockH_other tV H v 29 (by decide)
  · exact dockH_other tV H v 30 (by decide)
  · exact dockH_other tV H v 31 (by decide)
  · exact dockH_other tV H v 32 (by decide)

theorem tLoadCW_inj : Function.Injective tLoadCW := by decide

theorem install_tLoadCW (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install tLoadCW A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 2, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, v 1, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_slot tLoadCW tLoadCW_inj A v 0
  · exact install_other tLoadCW A v 1 (by decide)
  · exact install_other tLoadCW A v 2 (by decide)
  · exact install_other tLoadCW A v 3 (by decide)
  · exact install_other tLoadCW A v 4 (by decide)
  · exact install_other tLoadCW A v 5 (by decide)
  · exact install_other tLoadCW A v 6 (by decide)
  · exact install_other tLoadCW A v 7 (by decide)
  · exact install_slot tLoadCW tLoadCW_inj A v 2
  · exact install_other tLoadCW A v 9 (by decide)
  · exact install_other tLoadCW A v 10 (by decide)
  · exact install_other tLoadCW A v 11 (by decide)
  · exact install_other tLoadCW A v 12 (by decide)
  · exact install_other tLoadCW A v 13 (by decide)
  · exact install_other tLoadCW A v 14 (by decide)
  · exact install_other tLoadCW A v 15 (by decide)
  · exact install_other tLoadCW A v 16 (by decide)
  · exact install_other tLoadCW A v 17 (by decide)
  · exact install_other tLoadCW A v 18 (by decide)
  · exact install_other tLoadCW A v 19 (by decide)
  · exact install_slot tLoadCW tLoadCW_inj A v 1
  · exact install_other tLoadCW A v 21 (by decide)
  · exact install_other tLoadCW A v 22 (by decide)
  · exact install_other tLoadCW A v 23 (by decide)
  · exact install_other tLoadCW A v 24 (by decide)
  · exact install_other tLoadCW A v 25 (by decide)
  · exact install_other tLoadCW A v 26 (by decide)
  · exact install_other tLoadCW A v 27 (by decide)
  · exact install_other tLoadCW A v 28 (by decide)
  · exact install_other tLoadCW A v 29 (by decide)
  · exact install_other tLoadCW A v 30 (by decide)
  · exact install_other tLoadCW A v 31 (by decide)
  · exact install_other tLoadCW A v 32 (by decide)

theorem dockH_tLoadCW (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH tLoadCW H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 2, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, v 1, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_slot tLoadCW tLoadCW_inj H v 0
  · exact dockH_other tLoadCW H v 1 (by decide)
  · exact dockH_other tLoadCW H v 2 (by decide)
  · exact dockH_other tLoadCW H v 3 (by decide)
  · exact dockH_other tLoadCW H v 4 (by decide)
  · exact dockH_other tLoadCW H v 5 (by decide)
  · exact dockH_other tLoadCW H v 6 (by decide)
  · exact dockH_other tLoadCW H v 7 (by decide)
  · exact dockH_slot tLoadCW tLoadCW_inj H v 2
  · exact dockH_other tLoadCW H v 9 (by decide)
  · exact dockH_other tLoadCW H v 10 (by decide)
  · exact dockH_other tLoadCW H v 11 (by decide)
  · exact dockH_other tLoadCW H v 12 (by decide)
  · exact dockH_other tLoadCW H v 13 (by decide)
  · exact dockH_other tLoadCW H v 14 (by decide)
  · exact dockH_other tLoadCW H v 15 (by decide)
  · exact dockH_other tLoadCW H v 16 (by decide)
  · exact dockH_other tLoadCW H v 17 (by decide)
  · exact dockH_other tLoadCW H v 18 (by decide)
  · exact dockH_other tLoadCW H v 19 (by decide)
  · exact dockH_slot tLoadCW tLoadCW_inj H v 1
  · exact dockH_other tLoadCW H v 21 (by decide)
  · exact dockH_other tLoadCW H v 22 (by decide)
  · exact dockH_other tLoadCW H v 23 (by decide)
  · exact dockH_other tLoadCW H v 24 (by decide)
  · exact dockH_other tLoadCW H v 25 (by decide)
  · exact dockH_other tLoadCW H v 26 (by decide)
  · exact dockH_other tLoadCW H v 27 (by decide)
  · exact dockH_other tLoadCW H v 28 (by decide)
  · exact dockH_other tLoadCW H v 29 (by decide)
  · exact dockH_other tLoadCW H v 30 (by decide)
  · exact dockH_other tLoadCW H v 31 (by decide)
  · exact dockH_other tLoadCW H v 32 (by decide)

theorem tG_inj : Function.Injective tG := by decide

theorem install_tG (A : Fin 33 → List Bool) (v : Fin 1 → List Bool) :
    install tG A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 0, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_other tG A v 0 (by decide)
  · exact install_other tG A v 1 (by decide)
  · exact install_other tG A v 2 (by decide)
  · exact install_other tG A v 3 (by decide)
  · exact install_other tG A v 4 (by decide)
  · exact install_other tG A v 5 (by decide)
  · exact install_other tG A v 6 (by decide)
  · exact install_other tG A v 7 (by decide)
  · exact install_other tG A v 8 (by decide)
  · exact install_other tG A v 9 (by decide)
  · exact install_other tG A v 10 (by decide)
  · exact install_other tG A v 11 (by decide)
  · exact install_slot tG tG_inj A v 0
  · exact install_other tG A v 13 (by decide)
  · exact install_other tG A v 14 (by decide)
  · exact install_other tG A v 15 (by decide)
  · exact install_other tG A v 16 (by decide)
  · exact install_other tG A v 17 (by decide)
  · exact install_other tG A v 18 (by decide)
  · exact install_other tG A v 19 (by decide)
  · exact install_other tG A v 20 (by decide)
  · exact install_other tG A v 21 (by decide)
  · exact install_other tG A v 22 (by decide)
  · exact install_other tG A v 23 (by decide)
  · exact install_other tG A v 24 (by decide)
  · exact install_other tG A v 25 (by decide)
  · exact install_other tG A v 26 (by decide)
  · exact install_other tG A v 27 (by decide)
  · exact install_other tG A v 28 (by decide)
  · exact install_other tG A v 29 (by decide)
  · exact install_other tG A v 30 (by decide)
  · exact install_other tG A v 31 (by decide)
  · exact install_other tG A v 32 (by decide)

theorem dockH_tG (H : Fin 33 → ℕ) (v : Fin 1 → ℕ) :
    dockH tG H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, v 0, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tG H v 0 (by decide)
  · exact dockH_other tG H v 1 (by decide)
  · exact dockH_other tG H v 2 (by decide)
  · exact dockH_other tG H v 3 (by decide)
  · exact dockH_other tG H v 4 (by decide)
  · exact dockH_other tG H v 5 (by decide)
  · exact dockH_other tG H v 6 (by decide)
  · exact dockH_other tG H v 7 (by decide)
  · exact dockH_other tG H v 8 (by decide)
  · exact dockH_other tG H v 9 (by decide)
  · exact dockH_other tG H v 10 (by decide)
  · exact dockH_other tG H v 11 (by decide)
  · exact dockH_slot tG tG_inj H v 0
  · exact dockH_other tG H v 13 (by decide)
  · exact dockH_other tG H v 14 (by decide)
  · exact dockH_other tG H v 15 (by decide)
  · exact dockH_other tG H v 16 (by decide)
  · exact dockH_other tG H v 17 (by decide)
  · exact dockH_other tG H v 18 (by decide)
  · exact dockH_other tG H v 19 (by decide)
  · exact dockH_other tG H v 20 (by decide)
  · exact dockH_other tG H v 21 (by decide)
  · exact dockH_other tG H v 22 (by decide)
  · exact dockH_other tG H v 23 (by decide)
  · exact dockH_other tG H v 24 (by decide)
  · exact dockH_other tG H v 25 (by decide)
  · exact dockH_other tG H v 26 (by decide)
  · exact dockH_other tG H v 27 (by decide)
  · exact dockH_other tG H v 28 (by decide)
  · exact dockH_other tG H v 29 (by decide)
  · exact dockH_other tG H v 30 (by decide)
  · exact dockH_other tG H v 31 (by decide)
  · exact dockH_other tG H v 32 (by decide)

theorem tPJ_inj : Function.Injective tPJ := by decide

theorem install_tPJ (A : Fin 33 → List Bool) (v : Fin 1 → List Bool) :
    install tPJ A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_other tPJ A v 0 (by decide)
  · exact install_other tPJ A v 1 (by decide)
  · exact install_other tPJ A v 2 (by decide)
  · exact install_other tPJ A v 3 (by decide)
  · exact install_other tPJ A v 4 (by decide)
  · exact install_other tPJ A v 5 (by decide)
  · exact install_other tPJ A v 6 (by decide)
  · exact install_other tPJ A v 7 (by decide)
  · exact install_other tPJ A v 8 (by decide)
  · exact install_other tPJ A v 9 (by decide)
  · exact install_other tPJ A v 10 (by decide)
  · exact install_other tPJ A v 11 (by decide)
  · exact install_other tPJ A v 12 (by decide)
  · exact install_other tPJ A v 13 (by decide)
  · exact install_other tPJ A v 14 (by decide)
  · exact install_other tPJ A v 15 (by decide)
  · exact install_other tPJ A v 16 (by decide)
  · exact install_other tPJ A v 17 (by decide)
  · exact install_other tPJ A v 18 (by decide)
  · exact install_slot tPJ tPJ_inj A v 0
  · exact install_other tPJ A v 20 (by decide)
  · exact install_other tPJ A v 21 (by decide)
  · exact install_other tPJ A v 22 (by decide)
  · exact install_other tPJ A v 23 (by decide)
  · exact install_other tPJ A v 24 (by decide)
  · exact install_other tPJ A v 25 (by decide)
  · exact install_other tPJ A v 26 (by decide)
  · exact install_other tPJ A v 27 (by decide)
  · exact install_other tPJ A v 28 (by decide)
  · exact install_other tPJ A v 29 (by decide)
  · exact install_other tPJ A v 30 (by decide)
  · exact install_other tPJ A v 31 (by decide)
  · exact install_other tPJ A v 32 (by decide)

theorem dockH_tPJ (H : Fin 33 → ℕ) (v : Fin 1 → ℕ) :
    dockH tPJ H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, v 0, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tPJ H v 0 (by decide)
  · exact dockH_other tPJ H v 1 (by decide)
  · exact dockH_other tPJ H v 2 (by decide)
  · exact dockH_other tPJ H v 3 (by decide)
  · exact dockH_other tPJ H v 4 (by decide)
  · exact dockH_other tPJ H v 5 (by decide)
  · exact dockH_other tPJ H v 6 (by decide)
  · exact dockH_other tPJ H v 7 (by decide)
  · exact dockH_other tPJ H v 8 (by decide)
  · exact dockH_other tPJ H v 9 (by decide)
  · exact dockH_other tPJ H v 10 (by decide)
  · exact dockH_other tPJ H v 11 (by decide)
  · exact dockH_other tPJ H v 12 (by decide)
  · exact dockH_other tPJ H v 13 (by decide)
  · exact dockH_other tPJ H v 14 (by decide)
  · exact dockH_other tPJ H v 15 (by decide)
  · exact dockH_other tPJ H v 16 (by decide)
  · exact dockH_other tPJ H v 17 (by decide)
  · exact dockH_other tPJ H v 18 (by decide)
  · exact dockH_slot tPJ tPJ_inj H v 0
  · exact dockH_other tPJ H v 20 (by decide)
  · exact dockH_other tPJ H v 21 (by decide)
  · exact dockH_other tPJ H v 22 (by decide)
  · exact dockH_other tPJ H v 23 (by decide)
  · exact dockH_other tPJ H v 24 (by decide)
  · exact dockH_other tPJ H v 25 (by decide)
  · exact dockH_other tPJ H v 26 (by decide)
  · exact dockH_other tPJ H v 27 (by decide)
  · exact dockH_other tPJ H v 28 (by decide)
  · exact dockH_other tPJ H v 29 (by decide)
  · exact dockH_other tPJ H v 30 (by decide)
  · exact dockH_other tPJ H v 31 (by decide)
  · exact dockH_other tPJ H v 32 (by decide)

theorem tJB_inj : Function.Injective tJB := by decide

theorem install_tJB (A : Fin 33 → List Bool) (v : Fin 21 → List Bool) :
    install tJB A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 20] := by
  funext i
  fin_cases i
  · exact install_slot tJB tJB_inj A v 0
  · exact install_slot tJB tJB_inj A v 1
  · exact install_slot tJB tJB_inj A v 2
  · exact install_slot tJB tJB_inj A v 3
  · exact install_slot tJB tJB_inj A v 4
  · exact install_slot tJB tJB_inj A v 5
  · exact install_slot tJB tJB_inj A v 6
  · exact install_slot tJB tJB_inj A v 7
  · exact install_slot tJB tJB_inj A v 8
  · exact install_slot tJB tJB_inj A v 9
  · exact install_slot tJB tJB_inj A v 10
  · exact install_slot tJB tJB_inj A v 11
  · exact install_slot tJB tJB_inj A v 12
  · exact install_slot tJB tJB_inj A v 13
  · exact install_slot tJB tJB_inj A v 14
  · exact install_slot tJB tJB_inj A v 15
  · exact install_slot tJB tJB_inj A v 16
  · exact install_slot tJB tJB_inj A v 17
  · exact install_slot tJB tJB_inj A v 18
  · exact install_slot tJB tJB_inj A v 19
  · exact install_other tJB A v 20 (by decide)
  · exact install_other tJB A v 21 (by decide)
  · exact install_other tJB A v 22 (by decide)
  · exact install_other tJB A v 23 (by decide)
  · exact install_other tJB A v 24 (by decide)
  · exact install_other tJB A v 25 (by decide)
  · exact install_other tJB A v 26 (by decide)
  · exact install_other tJB A v 27 (by decide)
  · exact install_other tJB A v 28 (by decide)
  · exact install_other tJB A v 29 (by decide)
  · exact install_other tJB A v 30 (by decide)
  · exact install_other tJB A v 31 (by decide)
  · exact install_slot tJB tJB_inj A v 20

theorem dockH_tJB (H : Fin 33 → ℕ) (v : Fin 21 → ℕ) :
    dockH tJB H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 20] := by
  funext i
  fin_cases i
  · exact dockH_slot tJB tJB_inj H v 0
  · exact dockH_slot tJB tJB_inj H v 1
  · exact dockH_slot tJB tJB_inj H v 2
  · exact dockH_slot tJB tJB_inj H v 3
  · exact dockH_slot tJB tJB_inj H v 4
  · exact dockH_slot tJB tJB_inj H v 5
  · exact dockH_slot tJB tJB_inj H v 6
  · exact dockH_slot tJB tJB_inj H v 7
  · exact dockH_slot tJB tJB_inj H v 8
  · exact dockH_slot tJB tJB_inj H v 9
  · exact dockH_slot tJB tJB_inj H v 10
  · exact dockH_slot tJB tJB_inj H v 11
  · exact dockH_slot tJB tJB_inj H v 12
  · exact dockH_slot tJB tJB_inj H v 13
  · exact dockH_slot tJB tJB_inj H v 14
  · exact dockH_slot tJB tJB_inj H v 15
  · exact dockH_slot tJB tJB_inj H v 16
  · exact dockH_slot tJB tJB_inj H v 17
  · exact dockH_slot tJB tJB_inj H v 18
  · exact dockH_slot tJB tJB_inj H v 19
  · exact dockH_other tJB H v 20 (by decide)
  · exact dockH_other tJB H v 21 (by decide)
  · exact dockH_other tJB H v 22 (by decide)
  · exact dockH_other tJB H v 23 (by decide)
  · exact dockH_other tJB H v 24 (by decide)
  · exact dockH_other tJB H v 25 (by decide)
  · exact dockH_other tJB H v 26 (by decide)
  · exact dockH_other tJB H v 27 (by decide)
  · exact dockH_other tJB H v 28 (by decide)
  · exact dockH_other tJB H v 29 (by decide)
  · exact dockH_other tJB H v 30 (by decide)
  · exact dockH_other tJB H v 31 (by decide)
  · exact dockH_slot tJB tJB_inj H v 20

theorem tSp_inj : Function.Injective tSp := by decide

theorem install_tSp (A : Fin 33 → List Bool) (v : Fin 1 → List Bool) :
    install tSp A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 0, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_other tSp A v 0 (by decide)
  · exact install_other tSp A v 1 (by decide)
  · exact install_other tSp A v 2 (by decide)
  · exact install_other tSp A v 3 (by decide)
  · exact install_other tSp A v 4 (by decide)
  · exact install_other tSp A v 5 (by decide)
  · exact install_other tSp A v 6 (by decide)
  · exact install_other tSp A v 7 (by decide)
  · exact install_other tSp A v 8 (by decide)
  · exact install_other tSp A v 9 (by decide)
  · exact install_other tSp A v 10 (by decide)
  · exact install_other tSp A v 11 (by decide)
  · exact install_other tSp A v 12 (by decide)
  · exact install_other tSp A v 13 (by decide)
  · exact install_other tSp A v 14 (by decide)
  · exact install_other tSp A v 15 (by decide)
  · exact install_other tSp A v 16 (by decide)
  · exact install_other tSp A v 17 (by decide)
  · exact install_other tSp A v 18 (by decide)
  · exact install_other tSp A v 19 (by decide)
  · exact install_other tSp A v 20 (by decide)
  · exact install_slot tSp tSp_inj A v 0
  · exact install_other tSp A v 22 (by decide)
  · exact install_other tSp A v 23 (by decide)
  · exact install_other tSp A v 24 (by decide)
  · exact install_other tSp A v 25 (by decide)
  · exact install_other tSp A v 26 (by decide)
  · exact install_other tSp A v 27 (by decide)
  · exact install_other tSp A v 28 (by decide)
  · exact install_other tSp A v 29 (by decide)
  · exact install_other tSp A v 30 (by decide)
  · exact install_other tSp A v 31 (by decide)
  · exact install_other tSp A v 32 (by decide)

theorem dockH_tSp (H : Fin 33 → ℕ) (v : Fin 1 → ℕ) :
    dockH tSp H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, v 0, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tSp H v 0 (by decide)
  · exact dockH_other tSp H v 1 (by decide)
  · exact dockH_other tSp H v 2 (by decide)
  · exact dockH_other tSp H v 3 (by decide)
  · exact dockH_other tSp H v 4 (by decide)
  · exact dockH_other tSp H v 5 (by decide)
  · exact dockH_other tSp H v 6 (by decide)
  · exact dockH_other tSp H v 7 (by decide)
  · exact dockH_other tSp H v 8 (by decide)
  · exact dockH_other tSp H v 9 (by decide)
  · exact dockH_other tSp H v 10 (by decide)
  · exact dockH_other tSp H v 11 (by decide)
  · exact dockH_other tSp H v 12 (by decide)
  · exact dockH_other tSp H v 13 (by decide)
  · exact dockH_other tSp H v 14 (by decide)
  · exact dockH_other tSp H v 15 (by decide)
  · exact dockH_other tSp H v 16 (by decide)
  · exact dockH_other tSp H v 17 (by decide)
  · exact dockH_other tSp H v 18 (by decide)
  · exact dockH_other tSp H v 19 (by decide)
  · exact dockH_other tSp H v 20 (by decide)
  · exact dockH_slot tSp tSp_inj H v 0
  · exact dockH_other tSp H v 22 (by decide)
  · exact dockH_other tSp H v 23 (by decide)
  · exact dockH_other tSp H v 24 (by decide)
  · exact dockH_other tSp H v 25 (by decide)
  · exact dockH_other tSp H v 26 (by decide)
  · exact dockH_other tSp H v 27 (by decide)
  · exact dockH_other tSp H v 28 (by decide)
  · exact dockH_other tSp H v 29 (by decide)
  · exact dockH_other tSp H v 30 (by decide)
  · exact dockH_other tSp H v 31 (by decide)
  · exact dockH_other tSp H v 32 (by decide)

theorem tUn_inj : Function.Injective tUn := by decide

theorem install_tUn (A : Fin 33 → List Bool) (v : Fin 14 → List Bool) :
    install tUn A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 10, v 11, v 13, A 11, v 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, A 31, A 32] := by
  funext i
  fin_cases i
  · exact install_other tUn A v 0 (by decide)
  · exact install_other tUn A v 1 (by decide)
  · exact install_other tUn A v 2 (by decide)
  · exact install_other tUn A v 3 (by decide)
  · exact install_other tUn A v 4 (by decide)
  · exact install_other tUn A v 5 (by decide)
  · exact install_other tUn A v 6 (by decide)
  · exact install_other tUn A v 7 (by decide)
  · exact install_slot tUn tUn_inj A v 10
  · exact install_slot tUn tUn_inj A v 11
  · exact install_slot tUn tUn_inj A v 13
  · exact install_other tUn A v 11 (by decide)
  · exact install_slot tUn tUn_inj A v 12
  · exact install_other tUn A v 13 (by decide)
  · exact install_other tUn A v 14 (by decide)
  · exact install_other tUn A v 15 (by decide)
  · exact install_other tUn A v 16 (by decide)
  · exact install_other tUn A v 17 (by decide)
  · exact install_other tUn A v 18 (by decide)
  · exact install_other tUn A v 19 (by decide)
  · exact install_other tUn A v 20 (by decide)
  · exact install_slot tUn tUn_inj A v 0
  · exact install_slot tUn tUn_inj A v 1
  · exact install_slot tUn tUn_inj A v 2
  · exact install_slot tUn tUn_inj A v 3
  · exact install_slot tUn tUn_inj A v 4
  · exact install_slot tUn tUn_inj A v 5
  · exact install_slot tUn tUn_inj A v 6
  · exact install_slot tUn tUn_inj A v 7
  · exact install_slot tUn tUn_inj A v 8
  · exact install_slot tUn tUn_inj A v 9
  · exact install_other tUn A v 31 (by decide)
  · exact install_other tUn A v 32 (by decide)

theorem dockH_tUn (H : Fin 33 → ℕ) (v : Fin 14 → ℕ) :
    dockH tUn H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 10, v 11, v 13, H 11, v 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, H 31, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tUn H v 0 (by decide)
  · exact dockH_other tUn H v 1 (by decide)
  · exact dockH_other tUn H v 2 (by decide)
  · exact dockH_other tUn H v 3 (by decide)
  · exact dockH_other tUn H v 4 (by decide)
  · exact dockH_other tUn H v 5 (by decide)
  · exact dockH_other tUn H v 6 (by decide)
  · exact dockH_other tUn H v 7 (by decide)
  · exact dockH_slot tUn tUn_inj H v 10
  · exact dockH_slot tUn tUn_inj H v 11
  · exact dockH_slot tUn tUn_inj H v 13
  · exact dockH_other tUn H v 11 (by decide)
  · exact dockH_slot tUn tUn_inj H v 12
  · exact dockH_other tUn H v 13 (by decide)
  · exact dockH_other tUn H v 14 (by decide)
  · exact dockH_other tUn H v 15 (by decide)
  · exact dockH_other tUn H v 16 (by decide)
  · exact dockH_other tUn H v 17 (by decide)
  · exact dockH_other tUn H v 18 (by decide)
  · exact dockH_other tUn H v 19 (by decide)
  · exact dockH_other tUn H v 20 (by decide)
  · exact dockH_slot tUn tUn_inj H v 0
  · exact dockH_slot tUn tUn_inj H v 1
  · exact dockH_slot tUn tUn_inj H v 2
  · exact dockH_slot tUn tUn_inj H v 3
  · exact dockH_slot tUn tUn_inj H v 4
  · exact dockH_slot tUn tUn_inj H v 5
  · exact dockH_slot tUn tUn_inj H v 6
  · exact dockH_slot tUn tUn_inj H v 7
  · exact dockH_slot tUn tUn_inj H v 8
  · exact dockH_slot tUn tUn_inj H v 9
  · exact dockH_other tUn H v 31 (by decide)
  · exact dockH_other tUn H v 32 (by decide)

theorem tOut_inj : Function.Injective tOut := by decide

theorem install_tOut (A : Fin 33 → List Bool) (v : Fin 1 → List Bool) :
    install tOut A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, v 0, A 32] := by
  funext i
  fin_cases i
  · exact install_other tOut A v 0 (by decide)
  · exact install_other tOut A v 1 (by decide)
  · exact install_other tOut A v 2 (by decide)
  · exact install_other tOut A v 3 (by decide)
  · exact install_other tOut A v 4 (by decide)
  · exact install_other tOut A v 5 (by decide)
  · exact install_other tOut A v 6 (by decide)
  · exact install_other tOut A v 7 (by decide)
  · exact install_other tOut A v 8 (by decide)
  · exact install_other tOut A v 9 (by decide)
  · exact install_other tOut A v 10 (by decide)
  · exact install_other tOut A v 11 (by decide)
  · exact install_other tOut A v 12 (by decide)
  · exact install_other tOut A v 13 (by decide)
  · exact install_other tOut A v 14 (by decide)
  · exact install_other tOut A v 15 (by decide)
  · exact install_other tOut A v 16 (by decide)
  · exact install_other tOut A v 17 (by decide)
  · exact install_other tOut A v 18 (by decide)
  · exact install_other tOut A v 19 (by decide)
  · exact install_other tOut A v 20 (by decide)
  · exact install_other tOut A v 21 (by decide)
  · exact install_other tOut A v 22 (by decide)
  · exact install_other tOut A v 23 (by decide)
  · exact install_other tOut A v 24 (by decide)
  · exact install_other tOut A v 25 (by decide)
  · exact install_other tOut A v 26 (by decide)
  · exact install_other tOut A v 27 (by decide)
  · exact install_other tOut A v 28 (by decide)
  · exact install_other tOut A v 29 (by decide)
  · exact install_other tOut A v 30 (by decide)
  · exact install_slot tOut tOut_inj A v 0
  · exact install_other tOut A v 32 (by decide)

theorem dockH_tOut (H : Fin 33 → ℕ) (v : Fin 1 → ℕ) :
    dockH tOut H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, v 0, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tOut H v 0 (by decide)
  · exact dockH_other tOut H v 1 (by decide)
  · exact dockH_other tOut H v 2 (by decide)
  · exact dockH_other tOut H v 3 (by decide)
  · exact dockH_other tOut H v 4 (by decide)
  · exact dockH_other tOut H v 5 (by decide)
  · exact dockH_other tOut H v 6 (by decide)
  · exact dockH_other tOut H v 7 (by decide)
  · exact dockH_other tOut H v 8 (by decide)
  · exact dockH_other tOut H v 9 (by decide)
  · exact dockH_other tOut H v 10 (by decide)
  · exact dockH_other tOut H v 11 (by decide)
  · exact dockH_other tOut H v 12 (by decide)
  · exact dockH_other tOut H v 13 (by decide)
  · exact dockH_other tOut H v 14 (by decide)
  · exact dockH_other tOut H v 15 (by decide)
  · exact dockH_other tOut H v 16 (by decide)
  · exact dockH_other tOut H v 17 (by decide)
  · exact dockH_other tOut H v 18 (by decide)
  · exact dockH_other tOut H v 19 (by decide)
  · exact dockH_other tOut H v 20 (by decide)
  · exact dockH_other tOut H v 21 (by decide)
  · exact dockH_other tOut H v 22 (by decide)
  · exact dockH_other tOut H v 23 (by decide)
  · exact dockH_other tOut H v 24 (by decide)
  · exact dockH_other tOut H v 25 (by decide)
  · exact dockH_other tOut H v 26 (by decide)
  · exact dockH_other tOut H v 27 (by decide)
  · exact dockH_other tOut H v 28 (by decide)
  · exact dockH_other tOut H v 29 (by decide)
  · exact dockH_other tOut H v 30 (by decide)
  · exact dockH_slot tOut tOut_inj H v 0
  · exact dockH_other tOut H v 32 (by decide)

theorem tEmitCW_inj : Function.Injective tEmitCW := by decide

theorem install_tEmitCW (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install tEmitCW A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 2, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, v 0, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, v 1, A 32] := by
  funext i
  fin_cases i
  · exact install_other tEmitCW A v 0 (by decide)
  · exact install_other tEmitCW A v 1 (by decide)
  · exact install_other tEmitCW A v 2 (by decide)
  · exact install_other tEmitCW A v 3 (by decide)
  · exact install_other tEmitCW A v 4 (by decide)
  · exact install_other tEmitCW A v 5 (by decide)
  · exact install_other tEmitCW A v 6 (by decide)
  · exact install_other tEmitCW A v 7 (by decide)
  · exact install_slot tEmitCW tEmitCW_inj A v 2
  · exact install_other tEmitCW A v 9 (by decide)
  · exact install_other tEmitCW A v 10 (by decide)
  · exact install_other tEmitCW A v 11 (by decide)
  · exact install_other tEmitCW A v 12 (by decide)
  · exact install_other tEmitCW A v 13 (by decide)
  · exact install_other tEmitCW A v 14 (by decide)
  · exact install_other tEmitCW A v 15 (by decide)
  · exact install_other tEmitCW A v 16 (by decide)
  · exact install_other tEmitCW A v 17 (by decide)
  · exact install_other tEmitCW A v 18 (by decide)
  · exact install_other tEmitCW A v 19 (by decide)
  · exact install_slot tEmitCW tEmitCW_inj A v 0
  · exact install_other tEmitCW A v 21 (by decide)
  · exact install_other tEmitCW A v 22 (by decide)
  · exact install_other tEmitCW A v 23 (by decide)
  · exact install_other tEmitCW A v 24 (by decide)
  · exact install_other tEmitCW A v 25 (by decide)
  · exact install_other tEmitCW A v 26 (by decide)
  · exact install_other tEmitCW A v 27 (by decide)
  · exact install_other tEmitCW A v 28 (by decide)
  · exact install_other tEmitCW A v 29 (by decide)
  · exact install_other tEmitCW A v 30 (by decide)
  · exact install_slot tEmitCW tEmitCW_inj A v 1
  · exact install_other tEmitCW A v 32 (by decide)

theorem dockH_tEmitCW (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH tEmitCW H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 2, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, v 0, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, v 1, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tEmitCW H v 0 (by decide)
  · exact dockH_other tEmitCW H v 1 (by decide)
  · exact dockH_other tEmitCW H v 2 (by decide)
  · exact dockH_other tEmitCW H v 3 (by decide)
  · exact dockH_other tEmitCW H v 4 (by decide)
  · exact dockH_other tEmitCW H v 5 (by decide)
  · exact dockH_other tEmitCW H v 6 (by decide)
  · exact dockH_other tEmitCW H v 7 (by decide)
  · exact dockH_slot tEmitCW tEmitCW_inj H v 2
  · exact dockH_other tEmitCW H v 9 (by decide)
  · exact dockH_other tEmitCW H v 10 (by decide)
  · exact dockH_other tEmitCW H v 11 (by decide)
  · exact dockH_other tEmitCW H v 12 (by decide)
  · exact dockH_other tEmitCW H v 13 (by decide)
  · exact dockH_other tEmitCW H v 14 (by decide)
  · exact dockH_other tEmitCW H v 15 (by decide)
  · exact dockH_other tEmitCW H v 16 (by decide)
  · exact dockH_other tEmitCW H v 17 (by decide)
  · exact dockH_other tEmitCW H v 18 (by decide)
  · exact dockH_other tEmitCW H v 19 (by decide)
  · exact dockH_slot tEmitCW tEmitCW_inj H v 0
  · exact dockH_other tEmitCW H v 21 (by decide)
  · exact dockH_other tEmitCW H v 22 (by decide)
  · exact dockH_other tEmitCW H v 23 (by decide)
  · exact dockH_other tEmitCW H v 24 (by decide)
  · exact dockH_other tEmitCW H v 25 (by decide)
  · exact dockH_other tEmitCW H v 26 (by decide)
  · exact dockH_other tEmitCW H v 27 (by decide)
  · exact dockH_other tEmitCW H v 28 (by decide)
  · exact dockH_other tEmitCW H v 29 (by decide)
  · exact dockH_other tEmitCW H v 30 (by decide)
  · exact dockH_slot tEmitCW tEmitCW_inj H v 1
  · exact dockH_other tEmitCW H v 32 (by decide)

theorem tApp_inj : Function.Injective tApp := by decide

theorem install_tApp (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install tApp A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 2, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 0, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, v 1, A 32] := by
  funext i
  fin_cases i
  · exact install_other tApp A v 0 (by decide)
  · exact install_other tApp A v 1 (by decide)
  · exact install_other tApp A v 2 (by decide)
  · exact install_other tApp A v 3 (by decide)
  · exact install_other tApp A v 4 (by decide)
  · exact install_other tApp A v 5 (by decide)
  · exact install_other tApp A v 6 (by decide)
  · exact install_other tApp A v 7 (by decide)
  · exact install_other tApp A v 8 (by decide)
  · exact install_other tApp A v 9 (by decide)
  · exact install_slot tApp tApp_inj A v 2
  · exact install_other tApp A v 11 (by decide)
  · exact install_other tApp A v 12 (by decide)
  · exact install_other tApp A v 13 (by decide)
  · exact install_other tApp A v 14 (by decide)
  · exact install_other tApp A v 15 (by decide)
  · exact install_other tApp A v 16 (by decide)
  · exact install_other tApp A v 17 (by decide)
  · exact install_other tApp A v 18 (by decide)
  · exact install_other tApp A v 19 (by decide)
  · exact install_other tApp A v 20 (by decide)
  · exact install_slot tApp tApp_inj A v 0
  · exact install_other tApp A v 22 (by decide)
  · exact install_other tApp A v 23 (by decide)
  · exact install_other tApp A v 24 (by decide)
  · exact install_other tApp A v 25 (by decide)
  · exact install_other tApp A v 26 (by decide)
  · exact install_other tApp A v 27 (by decide)
  · exact install_other tApp A v 28 (by decide)
  · exact install_other tApp A v 29 (by decide)
  · exact install_other tApp A v 30 (by decide)
  · exact install_slot tApp tApp_inj A v 1
  · exact install_other tApp A v 32 (by decide)

theorem dockH_tApp (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH tApp H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 2, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, v 0, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, v 1, H 32] := by
  funext i
  fin_cases i
  · exact dockH_other tApp H v 0 (by decide)
  · exact dockH_other tApp H v 1 (by decide)
  · exact dockH_other tApp H v 2 (by decide)
  · exact dockH_other tApp H v 3 (by decide)
  · exact dockH_other tApp H v 4 (by decide)
  · exact dockH_other tApp H v 5 (by decide)
  · exact dockH_other tApp H v 6 (by decide)
  · exact dockH_other tApp H v 7 (by decide)
  · exact dockH_other tApp H v 8 (by decide)
  · exact dockH_other tApp H v 9 (by decide)
  · exact dockH_slot tApp tApp_inj H v 2
  · exact dockH_other tApp H v 11 (by decide)
  · exact dockH_other tApp H v 12 (by decide)
  · exact dockH_other tApp H v 13 (by decide)
  · exact dockH_other tApp H v 14 (by decide)
  · exact dockH_other tApp H v 15 (by decide)
  · exact dockH_other tApp H v 16 (by decide)
  · exact dockH_other tApp H v 17 (by decide)
  · exact dockH_other tApp H v 18 (by decide)
  · exact dockH_other tApp H v 19 (by decide)
  · exact dockH_other tApp H v 20 (by decide)
  · exact dockH_slot tApp tApp_inj H v 0
  · exact dockH_other tApp H v 22 (by decide)
  · exact dockH_other tApp H v 23 (by decide)
  · exact dockH_other tApp H v 24 (by decide)
  · exact dockH_other tApp H v 25 (by decide)
  · exact dockH_other tApp H v 26 (by decide)
  · exact dockH_other tApp H v 27 (by decide)
  · exact dockH_other tApp H v 28 (by decide)
  · exact dockH_other tApp H v 29 (by decide)
  · exact dockH_other tApp H v 30 (by decide)
  · exact dockH_slot tApp tApp_inj H v 1
  · exact dockH_other tApp H v 32 (by decide)

/-! ## Banks -/

def tHead (p o : ℕ) : Fin 33 → ℕ :=
  ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0]

/-- The fixed tapes of the term layout. -/
structure TFix where
  VT : List Bool
  TT : List Bool
  cap : ℕ
  cap2 : ℕ
  cap3 : ℕ
  cap4 : ℕ
  z : List Bool
  Jt : List Bool
  T1 : List Bool
  T2 : List Bool
  ZT : List Bool
  BWO : List Bool

/-- The varying tapes of the term layout. -/
structure TS where
  ps : PS
  PJ : Bool
  CW : List Bool
  Sp : List Bool
  Op : List Bool
  Gw : List Bool
  Rp : List Bool
  Zu : List Bool
  Z2u : List Bool
  Cu : Bool
  outs : List Bool

def tBank (x : TFix) (st : TS) : Fin 33 → List Bool :=
  ![x.VT, x.TT, st.ps.Ea, st.ps.LA, st.ps.LB, frame st.ps.R, frame st.ps.R2, frame st.ps.R3, List.replicate x.cap false,
    List.replicate x.cap2 false, List.replicate x.cap3 false, frame x.z, streamTape st.ps.G st.ps.staleG, st.ps.O,
    frame st.ps.X, frame st.ps.Y, [st.ps.Ec], [false], x.Jt, [st.PJ], st.CW, st.Sp, st.Op, frame st.Gw, frame st.Rp,
    frame st.Zu, frame st.Z2u, frame x.T1, frame x.T2, frame x.ZT, [st.Cu], overlay st.outs x.BWO,
    List.replicate x.cap4 false]

/-! ## The docked steps -/

theorem tNudgeV_step (x : TFix) (st : TS) (p o : ℕ) :
    Step tNudgeVD 1 (tHead p o) (tBank x st) (tHead (p + 1) o) (tBank x st) := by
  have e := dockRun (nudge_run x.VT p) tV tV_inj (tHead p o) (tBank x st) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [install_tV, dockH_tV] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem tLoadCW_step (x : TFix) (st : TS) (pre w post : List Bool) (o : ℕ) (hVT : x.VT = pre ++ frame w ++ post)
    (hcap : 2 * w.length + 1 ≤ x.cap) :
    Step tLoadCWD (2 * (2 * w.length + 1) + 2) (tHead pre.length o) (tBank x st)
      (tHead (pre.length + 2 * w.length) o) (tBank x { st with CW := overlay (frame w) st.CW }) := by
  have e0 := loadStep pre w post st.CW x.cap hcap
  rw [← hVT] at e0
  have e := dockRun e0 tLoadCW tLoadCW_inj (tHead pre.length o) (tBank x st) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_tLoadCW, dockH_tLoadCW] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem streamTape_cons (G : List (List Bool)) (s : List Bool) :
    ∃ b rest, streamTape G s = b :: rest ∧ streamTape [] rest = false :: rest := by
  cases G with
  | nil => exact ⟨false, s, rfl, rfl⟩
  | cons g G =>
    cases g with
    | nil => exact ⟨false, _, rfl, rfl⟩
    | cons a g => exact ⟨true, _, rfl, rfl⟩

/-- Empty the running list: a `false` in its cell 0. -/
theorem tClrG_step (x : TFix) (st : TS) (p o : ℕ) :
    Step tClrGD 1 (tHead p o) (tBank x st) (tHead p o)
      (tBank x { st with ps := { st.ps with G := [], staleG := (streamTape st.ps.G st.ps.staleG).tail } }) := by
  obtain ⟨b, rest, h1, _⟩ := streamTape_cons st.ps.G st.ps.staleG
  have e0 := write0Step false b rest
  have e := dockRun e0 tG tG_inj (tHead p o) (tBank x st) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; exact h1)
  rw [install_tG, dockH_tG] at e
  have ht : (streamTape st.ps.G st.ps.staleG).tail = rest := by rw [h1]; rfl
  rw [ht]
  refine e.congr (by funext i; fin_cases i <;> rfl) ?_
  funext i; fin_cases i <;> rfl

theorem tClrPJ_step (x : TFix) (st : TS) (p o : ℕ) :
    Step tClrPJD 1 (tHead p o) (tBank x st) (tHead p o) (tBank x { st with PJ := false }) := by
  have e := dockRun (cellStep false st.PJ) tPJ tPJ_inj (tHead p o) (tBank x st) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [install_tPJ, dockH_tPJ] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- Empty the unions stream: a `false` in its cell 0. -/
theorem tClrSp_step (x : TFix) (st : TS) (b : Bool) (rest : List Bool) (hSp : st.Sp = b :: rest) (p o : ℕ) :
    Step tClrSpD 1 (tHead p o) (tBank x st) (tHead p o) (tBank x { st with Sp := false :: rest }) := by
  have e := dockRun (write0Step false b rest) tSp tSp_inj (tHead p o) (tBank x st) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; exact hSp)
  rw [install_tSp, dockH_tSp] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- Write a bit on the output and step right. -/
theorem tPut_step (x : TFix) (st : TS) (b : Bool) (p : ℕ) :
    Step (RecoveryFocus.machine tOut (putM b)) 1 (tHead p st.outs.length) (tBank x st) (tHead p (st.outs ++ [b]).length)
      (tBank x { st with outs := st.outs ++ [b] }) := by
  have e0 := putStep b (overlay st.outs x.BWO) st.outs.length
  rw [overlay_write] at e0
  have e := dockRun e0 tOut tOut_inj (tHead p st.outs.length) (tBank x st) (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [install_tOut, dockH_tOut] at e
  exact e.congr (by funext i; fin_cases i <;> simp [tHead]) (by funext i; fin_cases i <;> rfl)

/-- Emit a register with a stale suffix (its head back at cell 0) onto a stream cursor. -/
theorem emitStepT (w tail out BW : List Bool) (cap : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step emitM (2 * (2 * w.length + 1) + 2) ![0, out.length, 0]
      ![frame w ++ tail, overlay out BW, List.replicate cap false] ![0, out.length + (2 * w.length + 1), 0]
      ![frame w ++ tail, overlay (out ++ frame w) BW, List.replicate cap false] := by
  have h0 := copyStep [] w tail out BW
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0
  have hm := h0.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem tEmitCW_step (x : TFix) (st : TS) (w tail : List Bool) (hCW : st.CW = frame w ++ tail)
    (hcap : 2 * w.length + 1 ≤ x.cap) (p : ℕ) :
    Step tEmitCWD (2 * (2 * w.length + 1) + 2) (tHead p st.outs.length) (tBank x st)
      (tHead p (st.outs ++ frame w).length) (tBank x { st with outs := st.outs ++ frame w }) := by
  have e0 := emitStepT w tail st.outs x.BWO x.cap hcap
  rw [← hCW] at e0
  have e := dockRun e0 tEmitCW tEmitCW_inj (tHead p st.outs.length) (tBank x st) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_tEmitCW, dockH_tEmitCW] at e
  exact e.congr (by funext i; fin_cases i <;> simp [tHead, frame_length]) (by funext i; fin_cases i <;> rfl)

/-- Write the parity cell's bit on the output. -/
theorem tParity_step (x : TFix) (st : TS) (p : ℕ) :
    Step tParityM (1 + 2) (tHead p st.outs.length) (tBank x st) (tHead p (st.outs ++ [st.PJ]).length)
      (tBank x { st with outs := st.outs ++ [st.PJ] }) := by
  have e := tPut_step x st st.PJ p
  cases h : st.PJ with
  | true =>
    rw [h] at e
    exact branch_true (19 : Fin 33) tPutFD e (by show readTapeBit [st.PJ] 0 = true; rw [h]; rfl)
  | false =>
    rw [h] at e
    exact branch_false (19 : Fin 33) tPutTD e (by show readTapeBit [st.PJ] 0 = false; rw [h]; rfl)

/-- Replace the pipeline state and the parity cell. -/
def setPS (st : TS) (ps : PS) (PJ : Bool) : TS := { st with ps := ps, PJ := PJ }

/-- The counter's pass over a term's factors, docked. -/
theorem tJB_step (Q : ℕ) (pool : List (List SynEq)) (fs : List (F2Poly ℕ)) (j m : ℕ) (P post staleT : List Bool)
    (x : TFix) (st : TS) (d B NF CB o : ℕ) (hVT : x.VT = P ++ fs.flatMap factorRec ++ false :: post)
    (hTT : x.TT = tableTape (childTable Q pool) staleT) (hz : x.z = z0 Q pool.flatten.length)
    (hJt : x.Jt = frame (binary m j)) (hm : fs.length = m)
    (hp : ∀ f ∈ fs, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (hd : ∀ f ∈ fs, ∀ mono ∈ f, mono.length ≤ d)
    (hNF : ∀ f ∈ fs, f.length ≤ NF) (hCB : ∀ f ∈ fs, ∀ mono ∈ f, (codeBits mono).length ≤ CB)
    (hinv : PInv (Q + pool.flatten.length + 1) st.ps)
    (hB : st.ps.G.length + (fs.flatten.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B x.cap x.cap2 x.cap3)
    (hcap4 : 1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1) ≤ x.cap4) :
    Step tJBD (2 * (1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1)) + 2)
      (tHead P.length o) (tBank x st) (tHead (P.length + (fs.flatMap factorRec).length) o)
      (tBank x (setPS st (fs.foldl (f2i Q pool j) (st.ps, st.PJ, 0)).1 (fs.foldl (f2i Q pool j) (st.ps, st.PJ, 0)).2.1)) := by
  have e0 := jblock_run Q pool fs j m P post staleT st.ps st.PJ x.cap x.cap2 x.cap3 x.cap4 d B NF CB hm hp hd hNF hCB
    hinv hB hc hcap4
  rw [← hVT, ← hTT, ← hz, ← hJt] at e0
  have e := dockRun e0 tJB tJB_inj (tHead P.length o) (tBank x st) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_tJB, dockH_tJB] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- The unions of the cancelled polynomial, docked (the unions stream starts empty). -/
theorem tUn_step (Q W : ℕ) (x : TFix) (st : TS) (rest : List Bool) (p o : ℕ) (hSp : st.Sp = false :: rest)
    (hT1 : x.T1 = lastT Q W) (hT2 : x.T2 = levelT Q W) (hZT : x.ZT = zeroT Q W) (hQ : 1 ≤ Q)
    (hG : ∀ g ∈ st.ps.G, g.length = Q + W + 1) (h0 : UInv (Q + W + 1) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩)
    (hcap : 2 * (Q + W + 1) + 1 ≤ x.cap)
    (hcap2 : pass1Cost (st.ps.G.foldl (liftStepW Q W) []).length (Q + W + 1) ≤ x.cap2 ∧
      appendCost (st.ps.G.foldl (liftStepW Q W) []).length ((st.ps.G.foldl (liftStepW Q W) []).length + 1) (Q + W + 1)
        ≤ x.cap2)
    (hcap3 : st.ps.G.length * (aCost (st.ps.G.foldl (liftStepW Q W) []).length (Q + W + 1) + 2) + 1 ≤ x.cap3) :
    Step tUnD (unionsCost st.ps.G.length (st.ps.G.foldl (liftStepW Q W) []).length (Q + W + 1)) (tHead p o) (tBank x st)
      (tHead p o)
      (tBank x { st with
        Sp := streamTape (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).E
          (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).staleS,
        Op := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).O,
        Gw := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).g,
        Rp := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).R,
        Zu := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).Z,
        Z2u := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).Z2,
        Cu := (st.ps.G.foldl (ustep Q W) ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩).C }) := by
  have e0 := unionsAll_run st.ps.G st.ps.staleG Q W x.cap x.cap2 x.cap3 ⟨[], rest, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩
    hQ hG h0 hcap hcap2 hcap3
  rw [← hT1, ← hT2, ← hZT] at e0
  have e := dockKeep e0 tUn tUn_inj (tHead p o) (tBank x st) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> first | rfl | exact hSp)
  rw [install_tUn] at e
  exact e.congr rfl (by funext i; fin_cases i <;> rfl)

/-- Append the unions stream to the output, docked. -/
theorem tApp_step (x : TFix) (st : TS) (E : List (List Bool)) (staleE : List Bool) (W : ℕ) (p : ℕ)
    (hSp : st.Sp = streamTape E staleE) (hE : ∀ r ∈ E, r.length = W) (hW : 1 ≤ W)
    (hcap : E.length * (2 * W + 1 + 1 + 1 + 2) + 1 ≤ x.cap3) :
    Step tAppD (2 * (E.length * (2 * W + 1 + 1 + 1 + 2) + 1) + 2) (tHead p st.outs.length) (tBank x st)
      (tHead p (st.outs ++ E.flatMap frame).length) (tBank x { st with outs := st.outs ++ E.flatMap frame }) := by
  have e0 := appOut_run E staleE st.outs x.BWO W x.cap3 hE hW hcap
  rw [← hSp] at e0
  have e := dockRun e0 tApp tApp_inj (tHead p st.outs.length) (tBank x st) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_tApp, dockH_tApp] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
