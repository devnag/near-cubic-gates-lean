import Proof.Wire_3_5.CompilerMachineEmitGroup

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits groupWord)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def gGR : Fin 1 → Fin 30 := ![0]
def gLoad : Fin 3 → Fin 30 := ![0, 7, 24]
def gPar : Fin 2 → Fin 30 := ![0, 8]

theorem gGR_inj : Function.Injective gGR := by decide

theorem install_gGR (A : Fin 30 → List Bool) (v : Fin 1 → List Bool) :
    install gGR A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29] := by
  funext i
  fin_cases i
  · exact install_slot gGR gGR_inj A v 0
  · exact install_other gGR A v 1 (by decide)
  · exact install_other gGR A v 2 (by decide)
  · exact install_other gGR A v 3 (by decide)
  · exact install_other gGR A v 4 (by decide)
  · exact install_other gGR A v 5 (by decide)
  · exact install_other gGR A v 6 (by decide)
  · exact install_other gGR A v 7 (by decide)
  · exact install_other gGR A v 8 (by decide)
  · exact install_other gGR A v 9 (by decide)
  · exact install_other gGR A v 10 (by decide)
  · exact install_other gGR A v 11 (by decide)
  · exact install_other gGR A v 12 (by decide)
  · exact install_other gGR A v 13 (by decide)
  · exact install_other gGR A v 14 (by decide)
  · exact install_other gGR A v 15 (by decide)
  · exact install_other gGR A v 16 (by decide)
  · exact install_other gGR A v 17 (by decide)
  · exact install_other gGR A v 18 (by decide)
  · exact install_other gGR A v 19 (by decide)
  · exact install_other gGR A v 20 (by decide)
  · exact install_other gGR A v 21 (by decide)
  · exact install_other gGR A v 22 (by decide)
  · exact install_other gGR A v 23 (by decide)
  · exact install_other gGR A v 24 (by decide)
  · exact install_other gGR A v 25 (by decide)
  · exact install_other gGR A v 26 (by decide)
  · exact install_other gGR A v 27 (by decide)
  · exact install_other gGR A v 28 (by decide)
  · exact install_other gGR A v 29 (by decide)

theorem dockH_gGR (H : Fin 30 → ℕ) (v : Fin 1 → ℕ) :
    dockH gGR H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29] := by
  funext i
  fin_cases i
  · exact dockH_slot gGR gGR_inj H v 0
  · exact dockH_other gGR H v 1 (by decide)
  · exact dockH_other gGR H v 2 (by decide)
  · exact dockH_other gGR H v 3 (by decide)
  · exact dockH_other gGR H v 4 (by decide)
  · exact dockH_other gGR H v 5 (by decide)
  · exact dockH_other gGR H v 6 (by decide)
  · exact dockH_other gGR H v 7 (by decide)
  · exact dockH_other gGR H v 8 (by decide)
  · exact dockH_other gGR H v 9 (by decide)
  · exact dockH_other gGR H v 10 (by decide)
  · exact dockH_other gGR H v 11 (by decide)
  · exact dockH_other gGR H v 12 (by decide)
  · exact dockH_other gGR H v 13 (by decide)
  · exact dockH_other gGR H v 14 (by decide)
  · exact dockH_other gGR H v 15 (by decide)
  · exact dockH_other gGR H v 16 (by decide)
  · exact dockH_other gGR H v 17 (by decide)
  · exact dockH_other gGR H v 18 (by decide)
  · exact dockH_other gGR H v 19 (by decide)
  · exact dockH_other gGR H v 20 (by decide)
  · exact dockH_other gGR H v 21 (by decide)
  · exact dockH_other gGR H v 22 (by decide)
  · exact dockH_other gGR H v 23 (by decide)
  · exact dockH_other gGR H v 24 (by decide)
  · exact dockH_other gGR H v 25 (by decide)
  · exact dockH_other gGR H v 26 (by decide)
  · exact dockH_other gGR H v 27 (by decide)
  · exact dockH_other gGR H v 28 (by decide)
  · exact dockH_other gGR H v 29 (by decide)

theorem gLoad_inj : Function.Injective gLoad := by decide

theorem install_gLoad (A : Fin 30 → List Bool) (v : Fin 3 → List Bool) :
    install gLoad A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, v 1, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 2, A 25, A 26, A 27, A 28, A 29] := by
  funext i
  fin_cases i
  · exact install_slot gLoad gLoad_inj A v 0
  · exact install_other gLoad A v 1 (by decide)
  · exact install_other gLoad A v 2 (by decide)
  · exact install_other gLoad A v 3 (by decide)
  · exact install_other gLoad A v 4 (by decide)
  · exact install_other gLoad A v 5 (by decide)
  · exact install_other gLoad A v 6 (by decide)
  · exact install_slot gLoad gLoad_inj A v 1
  · exact install_other gLoad A v 8 (by decide)
  · exact install_other gLoad A v 9 (by decide)
  · exact install_other gLoad A v 10 (by decide)
  · exact install_other gLoad A v 11 (by decide)
  · exact install_other gLoad A v 12 (by decide)
  · exact install_other gLoad A v 13 (by decide)
  · exact install_other gLoad A v 14 (by decide)
  · exact install_other gLoad A v 15 (by decide)
  · exact install_other gLoad A v 16 (by decide)
  · exact install_other gLoad A v 17 (by decide)
  · exact install_other gLoad A v 18 (by decide)
  · exact install_other gLoad A v 19 (by decide)
  · exact install_other gLoad A v 20 (by decide)
  · exact install_other gLoad A v 21 (by decide)
  · exact install_other gLoad A v 22 (by decide)
  · exact install_other gLoad A v 23 (by decide)
  · exact install_slot gLoad gLoad_inj A v 2
  · exact install_other gLoad A v 25 (by decide)
  · exact install_other gLoad A v 26 (by decide)
  · exact install_other gLoad A v 27 (by decide)
  · exact install_other gLoad A v 28 (by decide)
  · exact install_other gLoad A v 29 (by decide)

theorem dockH_gLoad (H : Fin 30 → ℕ) (v : Fin 3 → ℕ) :
    dockH gLoad H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, v 1, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 2, H 25, H 26, H 27, H 28, H 29] := by
  funext i
  fin_cases i
  · exact dockH_slot gLoad gLoad_inj H v 0
  · exact dockH_other gLoad H v 1 (by decide)
  · exact dockH_other gLoad H v 2 (by decide)
  · exact dockH_other gLoad H v 3 (by decide)
  · exact dockH_other gLoad H v 4 (by decide)
  · exact dockH_other gLoad H v 5 (by decide)
  · exact dockH_other gLoad H v 6 (by decide)
  · exact dockH_slot gLoad gLoad_inj H v 1
  · exact dockH_other gLoad H v 8 (by decide)
  · exact dockH_other gLoad H v 9 (by decide)
  · exact dockH_other gLoad H v 10 (by decide)
  · exact dockH_other gLoad H v 11 (by decide)
  · exact dockH_other gLoad H v 12 (by decide)
  · exact dockH_other gLoad H v 13 (by decide)
  · exact dockH_other gLoad H v 14 (by decide)
  · exact dockH_other gLoad H v 15 (by decide)
  · exact dockH_other gLoad H v 16 (by decide)
  · exact dockH_other gLoad H v 17 (by decide)
  · exact dockH_other gLoad H v 18 (by decide)
  · exact dockH_other gLoad H v 19 (by decide)
  · exact dockH_other gLoad H v 20 (by decide)
  · exact dockH_other gLoad H v 21 (by decide)
  · exact dockH_other gLoad H v 22 (by decide)
  · exact dockH_other gLoad H v 23 (by decide)
  · exact dockH_slot gLoad gLoad_inj H v 2
  · exact dockH_other gLoad H v 25 (by decide)
  · exact dockH_other gLoad H v 26 (by decide)
  · exact dockH_other gLoad H v 27 (by decide)
  · exact dockH_other gLoad H v 28 (by decide)
  · exact dockH_other gLoad H v 29 (by decide)

theorem gPar_inj : Function.Injective gPar := by decide

theorem install_gPar (A : Fin 30 → List Bool) (v : Fin 2 → List Bool) :
    install gPar A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 1, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29] := by
  funext i
  fin_cases i
  · exact install_slot gPar gPar_inj A v 0
  · exact install_other gPar A v 1 (by decide)
  · exact install_other gPar A v 2 (by decide)
  · exact install_other gPar A v 3 (by decide)
  · exact install_other gPar A v 4 (by decide)
  · exact install_other gPar A v 5 (by decide)
  · exact install_other gPar A v 6 (by decide)
  · exact install_other gPar A v 7 (by decide)
  · exact install_slot gPar gPar_inj A v 1
  · exact install_other gPar A v 9 (by decide)
  · exact install_other gPar A v 10 (by decide)
  · exact install_other gPar A v 11 (by decide)
  · exact install_other gPar A v 12 (by decide)
  · exact install_other gPar A v 13 (by decide)
  · exact install_other gPar A v 14 (by decide)
  · exact install_other gPar A v 15 (by decide)
  · exact install_other gPar A v 16 (by decide)
  · exact install_other gPar A v 17 (by decide)
  · exact install_other gPar A v 18 (by decide)
  · exact install_other gPar A v 19 (by decide)
  · exact install_other gPar A v 20 (by decide)
  · exact install_other gPar A v 21 (by decide)
  · exact install_other gPar A v 22 (by decide)
  · exact install_other gPar A v 23 (by decide)
  · exact install_other gPar A v 24 (by decide)
  · exact install_other gPar A v 25 (by decide)
  · exact install_other gPar A v 26 (by decide)
  · exact install_other gPar A v 27 (by decide)
  · exact install_other gPar A v 28 (by decide)
  · exact install_other gPar A v 29 (by decide)

theorem dockH_gPar (H : Fin 30 → ℕ) (v : Fin 2 → ℕ) :
    dockH gPar H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 1, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29] := by
  funext i
  fin_cases i
  · exact dockH_slot gPar gPar_inj H v 0
  · exact dockH_other gPar H v 1 (by decide)
  · exact dockH_other gPar H v 2 (by decide)
  · exact dockH_other gPar H v 3 (by decide)
  · exact dockH_other gPar H v 4 (by decide)
  · exact dockH_other gPar H v 5 (by decide)
  · exact dockH_other gPar H v 6 (by decide)
  · exact dockH_other gPar H v 7 (by decide)
  · exact dockH_slot gPar gPar_inj H v 1
  · exact dockH_other gPar H v 9 (by decide)
  · exact dockH_other gPar H v 10 (by decide)
  · exact dockH_other gPar H v 11 (by decide)
  · exact dockH_other gPar H v 12 (by decide)
  · exact dockH_other gPar H v 13 (by decide)
  · exact dockH_other gPar H v 14 (by decide)
  · exact dockH_other gPar H v 15 (by decide)
  · exact dockH_other gPar H v 16 (by decide)
  · exact dockH_other gPar H v 17 (by decide)
  · exact dockH_other gPar H v 18 (by decide)
  · exact dockH_other gPar H v 19 (by decide)
  · exact dockH_other gPar H v 20 (by decide)
  · exact dockH_other gPar H v 21 (by decide)
  · exact dockH_other gPar H v 22 (by decide)
  · exact dockH_other gPar H v 23 (by decide)
  · exact dockH_other gPar H v 24 (by decide)
  · exact dockH_other gPar H v 25 (by decide)
  · exact dockH_other gPar H v 26 (by decide)
  · exact dockH_other gPar H v 27 (by decide)
  · exact dockH_other gPar H v 28 (by decide)
  · exact dockH_other gPar H v 29 (by decide)

noncomputable def gMvD := RecoveryFocus.machine gGR moveM
noncomputable def gLoadD := RecoveryFocus.machine gLoad loadM
noncomputable def gParD := RecoveryFocus.machine gPar cpbM
/-- **One group**: the marker, the coefficient word, the parity bit, the entries, the stream's terminator. -/
noncomputable def groupBodyM :=
  Composition.machine gMvD (Composition.machine gLoadD (Composition.machine gMvD (Composition.machine gMvD
    (Composition.machine gParD (Composition.machine gMvD (Composition.machine gMvD
      (Composition.machine (StreamController.machine entryM 0) gMvD)))))))

theorem group_split (A R cb : List Bool) (par : Bool) (E : List (List Bool)) :
    A ++ groupWord cb par E ++ R =
      (A ++ [true]) ++ frame cb ++ ([true, par, false] ++ (E.flatMap frame ++ false :: R)) := by
  simp [groupWord, List.append_assoc]

theorem group_splitE (A R cb : List Bool) (par : Bool) (E : List (List Bool)) :
    A ++ groupWord cb par E ++ R = (A ++ [true] ++ frame cb ++ [true, par, false]) ++ streamTape E R := by
  simp [groupWord, streamTape, List.append_assoc]

theorem group_par (A R cb : List Bool) (par : Bool) (E : List (List Bool)) :
    readTapeBit (A ++ groupWord cb par E ++ R) ((A ++ [true]).length + 2 * cb.length + 1 + 1) = par := by
  rw [group_split]
  have : (A ++ [true]).length + 2 * cb.length + 1 + 1 = ((A ++ [true]) ++ frame cb ++ [true]).length := by simp; omega
  rw [this]
  simp only [List.append_assoc, readTapeBit]
  simp

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
