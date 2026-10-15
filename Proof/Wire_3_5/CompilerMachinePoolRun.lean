import Proof.Wire_3_5.CompilerMachinePoolGlue

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- Phase A with the normalized cursor returned to `0` (log on local tape 9). -/
noncomputable def normR := MaskedReset.machine normM (fun i => decide (i = 4))
/-- Phase B with the flip cursor returned to `0` (log on local tape 19). -/
noncomputable def flipsR := MaskedReset.machine flipsM (fun i => decide (i = 18))

def zA : Fin 10 → Fin 38 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 36]
def zB : Fin 20 → Fin 38 := ![4, 9, 10, 11, 12, 13, 14, 15, 16, 17, 5, 18, 3, 19, 20, 21, 22, 23, 24, 37]
def zC : Fin 1 → Fin 38 := ![21]
def zD : Fin 14 → Fin 38 := ![25, 1, 26, 27, 28, 29, 30, 31, 32, 33, 34, 5, 35, 24]

theorem zA_inj : Function.Injective zA := by decide

theorem install_zA (A : Fin 38 → List Bool) (v : Fin 10 → List Bool) :
    install zA A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, v 9, A 37] := by
  funext i
  fin_cases i
  · exact install_slot zA zA_inj A v 0
  · exact install_slot zA zA_inj A v 1
  · exact install_slot zA zA_inj A v 2
  · exact install_slot zA zA_inj A v 3
  · exact install_slot zA zA_inj A v 4
  · exact install_slot zA zA_inj A v 5
  · exact install_slot zA zA_inj A v 6
  · exact install_slot zA zA_inj A v 7
  · exact install_slot zA zA_inj A v 8
  · exact install_other zA A v 9 (by decide)
  · exact install_other zA A v 10 (by decide)
  · exact install_other zA A v 11 (by decide)
  · exact install_other zA A v 12 (by decide)
  · exact install_other zA A v 13 (by decide)
  · exact install_other zA A v 14 (by decide)
  · exact install_other zA A v 15 (by decide)
  · exact install_other zA A v 16 (by decide)
  · exact install_other zA A v 17 (by decide)
  · exact install_other zA A v 18 (by decide)
  · exact install_other zA A v 19 (by decide)
  · exact install_other zA A v 20 (by decide)
  · exact install_other zA A v 21 (by decide)
  · exact install_other zA A v 22 (by decide)
  · exact install_other zA A v 23 (by decide)
  · exact install_other zA A v 24 (by decide)
  · exact install_other zA A v 25 (by decide)
  · exact install_other zA A v 26 (by decide)
  · exact install_other zA A v 27 (by decide)
  · exact install_other zA A v 28 (by decide)
  · exact install_other zA A v 29 (by decide)
  · exact install_other zA A v 30 (by decide)
  · exact install_other zA A v 31 (by decide)
  · exact install_other zA A v 32 (by decide)
  · exact install_other zA A v 33 (by decide)
  · exact install_other zA A v 34 (by decide)
  · exact install_other zA A v 35 (by decide)
  · exact install_slot zA zA_inj A v 9
  · exact install_other zA A v 37 (by decide)

theorem dockH_zA (H : Fin 38 → ℕ) (v : Fin 10 → ℕ) :
    dockH zA H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, H 34, H 35, v 9, H 37] := by
  funext i
  fin_cases i
  · exact dockH_slot zA zA_inj H v 0
  · exact dockH_slot zA zA_inj H v 1
  · exact dockH_slot zA zA_inj H v 2
  · exact dockH_slot zA zA_inj H v 3
  · exact dockH_slot zA zA_inj H v 4
  · exact dockH_slot zA zA_inj H v 5
  · exact dockH_slot zA zA_inj H v 6
  · exact dockH_slot zA zA_inj H v 7
  · exact dockH_slot zA zA_inj H v 8
  · exact dockH_other zA H v 9 (by decide)
  · exact dockH_other zA H v 10 (by decide)
  · exact dockH_other zA H v 11 (by decide)
  · exact dockH_other zA H v 12 (by decide)
  · exact dockH_other zA H v 13 (by decide)
  · exact dockH_other zA H v 14 (by decide)
  · exact dockH_other zA H v 15 (by decide)
  · exact dockH_other zA H v 16 (by decide)
  · exact dockH_other zA H v 17 (by decide)
  · exact dockH_other zA H v 18 (by decide)
  · exact dockH_other zA H v 19 (by decide)
  · exact dockH_other zA H v 20 (by decide)
  · exact dockH_other zA H v 21 (by decide)
  · exact dockH_other zA H v 22 (by decide)
  · exact dockH_other zA H v 23 (by decide)
  · exact dockH_other zA H v 24 (by decide)
  · exact dockH_other zA H v 25 (by decide)
  · exact dockH_other zA H v 26 (by decide)
  · exact dockH_other zA H v 27 (by decide)
  · exact dockH_other zA H v 28 (by decide)
  · exact dockH_other zA H v 29 (by decide)
  · exact dockH_other zA H v 30 (by decide)
  · exact dockH_other zA H v 31 (by decide)
  · exact dockH_other zA H v 32 (by decide)
  · exact dockH_other zA H v 33 (by decide)
  · exact dockH_other zA H v 34 (by decide)
  · exact dockH_other zA H v 35 (by decide)
  · exact dockH_slot zA zA_inj H v 9
  · exact dockH_other zA H v 37 (by decide)

theorem zB_inj : Function.Injective zB := by decide

theorem install_zB (A : Fin 38 → List Bool) (v : Fin 20 → List Bool) :
    install zB A v = ![A 0, A 1, A 2, v 12, v 0, v 10, A 6, A 7, A 8, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 11, v 13, v 14, v 15, v 16, v 17, v 18, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, v 19] := by
  funext i
  fin_cases i
  · exact install_other zB A v 0 (by decide)
  · exact install_other zB A v 1 (by decide)
  · exact install_other zB A v 2 (by decide)
  · exact install_slot zB zB_inj A v 12
  · exact install_slot zB zB_inj A v 0
  · exact install_slot zB zB_inj A v 10
  · exact install_other zB A v 6 (by decide)
  · exact install_other zB A v 7 (by decide)
  · exact install_other zB A v 8 (by decide)
  · exact install_slot zB zB_inj A v 1
  · exact install_slot zB zB_inj A v 2
  · exact install_slot zB zB_inj A v 3
  · exact install_slot zB zB_inj A v 4
  · exact install_slot zB zB_inj A v 5
  · exact install_slot zB zB_inj A v 6
  · exact install_slot zB zB_inj A v 7
  · exact install_slot zB zB_inj A v 8
  · exact install_slot zB zB_inj A v 9
  · exact install_slot zB zB_inj A v 11
  · exact install_slot zB zB_inj A v 13
  · exact install_slot zB zB_inj A v 14
  · exact install_slot zB zB_inj A v 15
  · exact install_slot zB zB_inj A v 16
  · exact install_slot zB zB_inj A v 17
  · exact install_slot zB zB_inj A v 18
  · exact install_other zB A v 25 (by decide)
  · exact install_other zB A v 26 (by decide)
  · exact install_other zB A v 27 (by decide)
  · exact install_other zB A v 28 (by decide)
  · exact install_other zB A v 29 (by decide)
  · exact install_other zB A v 30 (by decide)
  · exact install_other zB A v 31 (by decide)
  · exact install_other zB A v 32 (by decide)
  · exact install_other zB A v 33 (by decide)
  · exact install_other zB A v 34 (by decide)
  · exact install_other zB A v 35 (by decide)
  · exact install_other zB A v 36 (by decide)
  · exact install_slot zB zB_inj A v 19

theorem dockH_zB (H : Fin 38 → ℕ) (v : Fin 20 → ℕ) :
    dockH zB H v = ![H 0, H 1, H 2, v 12, v 0, v 10, H 6, H 7, H 8, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 11, v 13, v 14, v 15, v 16, v 17, v 18, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, H 34, H 35, H 36, v 19] := by
  funext i
  fin_cases i
  · exact dockH_other zB H v 0 (by decide)
  · exact dockH_other zB H v 1 (by decide)
  · exact dockH_other zB H v 2 (by decide)
  · exact dockH_slot zB zB_inj H v 12
  · exact dockH_slot zB zB_inj H v 0
  · exact dockH_slot zB zB_inj H v 10
  · exact dockH_other zB H v 6 (by decide)
  · exact dockH_other zB H v 7 (by decide)
  · exact dockH_other zB H v 8 (by decide)
  · exact dockH_slot zB zB_inj H v 1
  · exact dockH_slot zB zB_inj H v 2
  · exact dockH_slot zB zB_inj H v 3
  · exact dockH_slot zB zB_inj H v 4
  · exact dockH_slot zB zB_inj H v 5
  · exact dockH_slot zB zB_inj H v 6
  · exact dockH_slot zB zB_inj H v 7
  · exact dockH_slot zB zB_inj H v 8
  · exact dockH_slot zB zB_inj H v 9
  · exact dockH_slot zB zB_inj H v 11
  · exact dockH_slot zB zB_inj H v 13
  · exact dockH_slot zB zB_inj H v 14
  · exact dockH_slot zB zB_inj H v 15
  · exact dockH_slot zB zB_inj H v 16
  · exact dockH_slot zB zB_inj H v 17
  · exact dockH_slot zB zB_inj H v 18
  · exact dockH_other zB H v 25 (by decide)
  · exact dockH_other zB H v 26 (by decide)
  · exact dockH_other zB H v 27 (by decide)
  · exact dockH_other zB H v 28 (by decide)
  · exact dockH_other zB H v 29 (by decide)
  · exact dockH_other zB H v 30 (by decide)
  · exact dockH_other zB H v 31 (by decide)
  · exact dockH_other zB H v 32 (by decide)
  · exact dockH_other zB H v 33 (by decide)
  · exact dockH_other zB H v 34 (by decide)
  · exact dockH_other zB H v 35 (by decide)
  · exact dockH_other zB H v 36 (by decide)
  · exact dockH_slot zB zB_inj H v 19

theorem zC_inj : Function.Injective zC := by decide

theorem install_zC (A : Fin 38 → List Bool) (v : Fin 1 → List Bool) :
    install zC A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 0, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37] := by
  funext i
  fin_cases i
  · exact install_other zC A v 0 (by decide)
  · exact install_other zC A v 1 (by decide)
  · exact install_other zC A v 2 (by decide)
  · exact install_other zC A v 3 (by decide)
  · exact install_other zC A v 4 (by decide)
  · exact install_other zC A v 5 (by decide)
  · exact install_other zC A v 6 (by decide)
  · exact install_other zC A v 7 (by decide)
  · exact install_other zC A v 8 (by decide)
  · exact install_other zC A v 9 (by decide)
  · exact install_other zC A v 10 (by decide)
  · exact install_other zC A v 11 (by decide)
  · exact install_other zC A v 12 (by decide)
  · exact install_other zC A v 13 (by decide)
  · exact install_other zC A v 14 (by decide)
  · exact install_other zC A v 15 (by decide)
  · exact install_other zC A v 16 (by decide)
  · exact install_other zC A v 17 (by decide)
  · exact install_other zC A v 18 (by decide)
  · exact install_other zC A v 19 (by decide)
  · exact install_other zC A v 20 (by decide)
  · exact install_slot zC zC_inj A v 0
  · exact install_other zC A v 22 (by decide)
  · exact install_other zC A v 23 (by decide)
  · exact install_other zC A v 24 (by decide)
  · exact install_other zC A v 25 (by decide)
  · exact install_other zC A v 26 (by decide)
  · exact install_other zC A v 27 (by decide)
  · exact install_other zC A v 28 (by decide)
  · exact install_other zC A v 29 (by decide)
  · exact install_other zC A v 30 (by decide)
  · exact install_other zC A v 31 (by decide)
  · exact install_other zC A v 32 (by decide)
  · exact install_other zC A v 33 (by decide)
  · exact install_other zC A v 34 (by decide)
  · exact install_other zC A v 35 (by decide)
  · exact install_other zC A v 36 (by decide)
  · exact install_other zC A v 37 (by decide)

theorem dockH_zC (H : Fin 38 → ℕ) (v : Fin 1 → ℕ) :
    dockH zC H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, v 0, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, H 34, H 35, H 36, H 37] := by
  funext i
  fin_cases i
  · exact dockH_other zC H v 0 (by decide)
  · exact dockH_other zC H v 1 (by decide)
  · exact dockH_other zC H v 2 (by decide)
  · exact dockH_other zC H v 3 (by decide)
  · exact dockH_other zC H v 4 (by decide)
  · exact dockH_other zC H v 5 (by decide)
  · exact dockH_other zC H v 6 (by decide)
  · exact dockH_other zC H v 7 (by decide)
  · exact dockH_other zC H v 8 (by decide)
  · exact dockH_other zC H v 9 (by decide)
  · exact dockH_other zC H v 10 (by decide)
  · exact dockH_other zC H v 11 (by decide)
  · exact dockH_other zC H v 12 (by decide)
  · exact dockH_other zC H v 13 (by decide)
  · exact dockH_other zC H v 14 (by decide)
  · exact dockH_other zC H v 15 (by decide)
  · exact dockH_other zC H v 16 (by decide)
  · exact dockH_other zC H v 17 (by decide)
  · exact dockH_other zC H v 18 (by decide)
  · exact dockH_other zC H v 19 (by decide)
  · exact dockH_other zC H v 20 (by decide)
  · exact dockH_slot zC zC_inj H v 0
  · exact dockH_other zC H v 22 (by decide)
  · exact dockH_other zC H v 23 (by decide)
  · exact dockH_other zC H v 24 (by decide)
  · exact dockH_other zC H v 25 (by decide)
  · exact dockH_other zC H v 26 (by decide)
  · exact dockH_other zC H v 27 (by decide)
  · exact dockH_other zC H v 28 (by decide)
  · exact dockH_other zC H v 29 (by decide)
  · exact dockH_other zC H v 30 (by decide)
  · exact dockH_other zC H v 31 (by decide)
  · exact dockH_other zC H v 32 (by decide)
  · exact dockH_other zC H v 33 (by decide)
  · exact dockH_other zC H v 34 (by decide)
  · exact dockH_other zC H v 35 (by decide)
  · exact dockH_other zC H v 36 (by decide)
  · exact dockH_other zC H v 37 (by decide)

theorem zD_inj : Function.Injective zD := by decide

theorem install_zD (A : Fin 38 → List Bool) (v : Fin 14 → List Bool) :
    install zD A v = ![A 0, v 1, A 2, A 3, A 4, v 11, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 13, v 0, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 12, A 36, A 37] := by
  funext i
  fin_cases i
  · exact install_other zD A v 0 (by decide)
  · exact install_slot zD zD_inj A v 1
  · exact install_other zD A v 2 (by decide)
  · exact install_other zD A v 3 (by decide)
  · exact install_other zD A v 4 (by decide)
  · exact install_slot zD zD_inj A v 11
  · exact install_other zD A v 6 (by decide)
  · exact install_other zD A v 7 (by decide)
  · exact install_other zD A v 8 (by decide)
  · exact install_other zD A v 9 (by decide)
  · exact install_other zD A v 10 (by decide)
  · exact install_other zD A v 11 (by decide)
  · exact install_other zD A v 12 (by decide)
  · exact install_other zD A v 13 (by decide)
  · exact install_other zD A v 14 (by decide)
  · exact install_other zD A v 15 (by decide)
  · exact install_other zD A v 16 (by decide)
  · exact install_other zD A v 17 (by decide)
  · exact install_other zD A v 18 (by decide)
  · exact install_other zD A v 19 (by decide)
  · exact install_other zD A v 20 (by decide)
  · exact install_other zD A v 21 (by decide)
  · exact install_other zD A v 22 (by decide)
  · exact install_other zD A v 23 (by decide)
  · exact install_slot zD zD_inj A v 13
  · exact install_slot zD zD_inj A v 0
  · exact install_slot zD zD_inj A v 2
  · exact install_slot zD zD_inj A v 3
  · exact install_slot zD zD_inj A v 4
  · exact install_slot zD zD_inj A v 5
  · exact install_slot zD zD_inj A v 6
  · exact install_slot zD zD_inj A v 7
  · exact install_slot zD zD_inj A v 8
  · exact install_slot zD zD_inj A v 9
  · exact install_slot zD zD_inj A v 10
  · exact install_slot zD zD_inj A v 12
  · exact install_other zD A v 36 (by decide)
  · exact install_other zD A v 37 (by decide)

theorem dockH_zD (H : Fin 38 → ℕ) (v : Fin 14 → ℕ) :
    dockH zD H v = ![H 0, v 1, H 2, H 3, H 4, v 11, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 13, v 0, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 12, H 36, H 37] := by
  funext i
  fin_cases i
  · exact dockH_other zD H v 0 (by decide)
  · exact dockH_slot zD zD_inj H v 1
  · exact dockH_other zD H v 2 (by decide)
  · exact dockH_other zD H v 3 (by decide)
  · exact dockH_other zD H v 4 (by decide)
  · exact dockH_slot zD zD_inj H v 11
  · exact dockH_other zD H v 6 (by decide)
  · exact dockH_other zD H v 7 (by decide)
  · exact dockH_other zD H v 8 (by decide)
  · exact dockH_other zD H v 9 (by decide)
  · exact dockH_other zD H v 10 (by decide)
  · exact dockH_other zD H v 11 (by decide)
  · exact dockH_other zD H v 12 (by decide)
  · exact dockH_other zD H v 13 (by decide)
  · exact dockH_other zD H v 14 (by decide)
  · exact dockH_other zD H v 15 (by decide)
  · exact dockH_other zD H v 16 (by decide)
  · exact dockH_other zD H v 17 (by decide)
  · exact dockH_other zD H v 18 (by decide)
  · exact dockH_other zD H v 19 (by decide)
  · exact dockH_other zD H v 20 (by decide)
  · exact dockH_other zD H v 21 (by decide)
  · exact dockH_other zD H v 22 (by decide)
  · exact dockH_other zD H v 23 (by decide)
  · exact dockH_slot zD zD_inj H v 13
  · exact dockH_slot zD zD_inj H v 0
  · exact dockH_slot zD zD_inj H v 2
  · exact dockH_slot zD zD_inj H v 3
  · exact dockH_slot zD zD_inj H v 4
  · exact dockH_slot zD zD_inj H v 5
  · exact dockH_slot zD zD_inj H v 6
  · exact dockH_slot zD zD_inj H v 7
  · exact dockH_slot zD zD_inj H v 8
  · exact dockH_slot zD zD_inj H v 9
  · exact dockH_slot zD zD_inj H v 10
  · exact dockH_slot zD zD_inj H v 12
  · exact dockH_other zD H v 36 (by decide)
  · exact dockH_other zD H v 37 (by decide)

/-- The 38 tapes of the pool build. -/
structure RT where
  gs : List Bool
  gk : List Bool
  mr : List Bool
  zh : List Bool
  nm : List Bool
  lg : List Bool
  dn : List Bool
  lg2 : List Bool
  db : List Bool
  sd : List Bool
  fr : List Bool
  rp : List Bool
  rn : List Bool
  ol : List Bool
  or : List Bool
  pa : List Bool
  na : List Bool
  tm : List Bool
  lg3 : List Bool
  zl : List Bool
  zr : List Bool
  out : List Bool
  lg4 : List Bool
  lg5 : List Bool
  fl : List Bool
  cn : List Bool
  cv : List Bool
  zw : List Bool
  jc : List Bool
  cl : List Bool
  one : List Bool
  oh : List Bool
  msk : List Bool
  tt : List Bool
  tb : List Bool
  lg6 : List Bool
  lg7 : List Bool
  lg8 : List Bool

def rA (t : RT) : Fin 38 → List Bool :=
  ![t.gs, t.gk, t.mr, t.zh, t.nm, t.lg, t.dn, t.lg2, t.db, t.sd, t.fr, t.rp, t.rn, t.ol, t.or, t.pa, t.na, t.tm, t.lg3,
    t.zl, t.zr, t.out, t.lg4, t.lg5, t.fl, t.cn, t.cv, t.zw, t.jc, t.cl, t.one, t.oh, t.msk, t.tt, t.tb, t.lg6, t.lg7, t.lg8]

/-- The pool build's heads: the children words, the child driver, the pool cursor, the flip cursor, the table
cursor. -/
def rH (g d o f b : ℕ) : Fin 38 → ℕ :=
  ![g, 0, 0, 0, 0, 0, 0, 0, d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, f, 0, 0, 0, 0, 0, 0, 0, 0, 0, b, 0, 0, 0]

/-- Phase A's constrained tapes. -/
def RT.inA (t : RT) (GSW K ZH LG DN LG2 DB LG7 : List Bool) : RT :=
  { t with gs := GSW, gk := K, zh := ZH, lg := LG, dn := DN, lg2 := LG2, db := DB, lg7 := LG7 }

/-- Phase A's outputs. -/
def RT.outA (t : RT) (MR NM : List Bool) : RT := { t with mr := MR, nm := NM }

/-- **Phase A**: the children normalized. -/
theorem pA_step (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (gs : List (ExactThresholdGate n)) (postG : List Bool) (t : RT)
    (capK cap capN2 capN7 : ℕ) (hok : ∀ e ∈ gs, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hc1 : 2 * h + 1 ≤ cap) (hc2 : innerCost h n ≤ capN2) (hc7 : normCost h n gs.length ≤ capN7) :
    Step (RecoveryFocus.machine zA normR) (2 * normCost h n gs.length + 2) (rH 0 0 0 0 0)
      (rA (t.inA (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) (frame (binary h 0))
        (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false) (List.replicate gs.length true)
        (List.replicate capN7 false)))
      (rH (gs.flatMap exactWord).length gs.length 0 0 0)
      (rA ((t.inA (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) (frame (binary h 0))
        (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false) (List.replicate gs.length true)
        (List.replicate capN7 false)).outA (mrKids h t.mr gs) (overlay (normTape h gs) t.nm))) := by
  have nr := norm_run h h1 gs [] postG t.mr [] t.nm capK cap capN2 hok hc1 hc2
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at nr
  have hm := nr.mask (fun i => decide (i = 4)) (by intro i hi; simp at hi; subst hi; rfl) hc7
  have c : Step normR (2 * normCost h n gs.length + 2) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![gs.flatMap exactWord ++ postG, false :: List.replicate capK true, t.mr, frame (binary h 0), t.nm,
        List.replicate cap false, List.replicate n true, List.replicate capN2 false, List.replicate gs.length true,
        List.replicate capN7 false]
      ![(gs.flatMap exactWord).length, 0, 0, 0, 0, 0, 0, 0, gs.length, 0]
      ![gs.flatMap exactWord ++ postG, false :: List.replicate capK true, mrKids h t.mr gs, frame (binary h 0),
        overlay (normTape h gs) t.nm, List.replicate cap false, List.replicate n true, List.replicate capN2 false,
        List.replicate gs.length true, List.replicate capN7 false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      (try fin_cases j) <;> rfl
  have e := dockRun c zA zA_inj (rH 0 0 0 0 0)
    (rA (t.inA (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) (frame (binary h 0))
      (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false) (List.replicate gs.length true)
      (List.replicate capN7 false)))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_zA, dockH_zA] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- Phase B's constrained tapes. -/
def RT.inB (t : RT) (NM SD ZH ZL ZR LG LG3 LG4 LG5 FL LG8 : List Bool) : RT :=
  { t with nm := NM, sd := SD, zh := ZH, zl := ZL, zr := ZR, lg := LG, lg3 := LG3, lg4 := LG4, lg5 := LG5, fl := FL, lg8 := LG8 }

/-- Phase B's outputs. -/
def RT.outB (t : RT) (st : FSt) (OUT : List Bool) : RT :=
  { t with fr := st.fr, rp := st.ps.rp, rn := st.ps.rn, ol := st.ps.ol, or := st.ps.or, pa := st.ps.pa, na := st.ps.na, tm := st.ps.tm, out := OUT }

/-- The flip phase's initial state from the tapes. -/
def RT.fst (t : RT) : FSt := ⟨⟨t.rp, t.rn, t.ol, t.or, t.pa, t.na, t.tm, []⟩, t.fr⟩

/-- **Phase B**: every flip pattern's dense children on the pool stream. -/
theorem pB_step (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (hn : 1 ≤ n) (gs : List (ExactThresholdGate n)) (side : List Bool)
    (width : ℕ) (flips : List (List Bool)) (hs : side.length = n) (hfl : ∀ f ∈ flips, f.length = n)
    (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width) (postN tS sZL sZR staleF : List Bool) (t : RT)
    (g d cap capC2 capC3 capC4 capF8 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcapF : 2 * n + 1 ≤ cap) (hcap2 : cloopCost h n ≤ capC2)
    (hcap3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ capC3)
    (hcap4 : kidsCost h n width (nLeft side n) (nRight side n) gs.length ≤ capC4)
    (hcap8 : flips.length * (flipCost h n width (nLeft side n) (nRight side n) gs.length + 2) + 1 ≤ capF8) :
    Step (RecoveryFocus.machine zB flipsR)
      (2 * (flips.length * (flipCost h n width (nLeft side n) (nRight side n) gs.length + 2) + 1) + 2) (rH g d 0 0 0)
      (rA (t.inB (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0))
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        (List.replicate cap false) (List.replicate capC2 false) (List.replicate capC3 false)
        (List.replicate capC4 false) (streamTape flips staleF) (List.replicate capF8 false)))
      (rH g d ((flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))).flatMap frame).length 0 0)
      (rA ((t.inB (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0))
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        (List.replicate cap false) (List.replicate capC2 false) (List.replicate capC3 false)
        (List.replicate capC4 false) (streamTape flips staleF) (List.replicate capF8 false)).outB
        (flips.foldl (fnext h gs side width) t.fst)
        (overlay ((flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))).flatMap frame) t.out))) := by
  have fr := flips_run h h1 hn gs side width flips hs hfl hL hR postN tS [] sZL sZR t.out staleF t.fst cap capC2 capC3
    capC4 hcap hcapF hcap2 hcap3 hcap4
  have hE : t.fst.ps.E = [] := rfl
  rw [hE] at fr
  simp only [List.append_nil, List.nil_append, List.flatMap_nil, List.length_nil] at fr
  have hm := fr.mask (fun i => decide (i = 18)) (by intro i hi; simp at hi; subst hi; rfl) hcap8
  have c : Step flipsR (2 * (flips.length * (flipCost h n width (nLeft side n) (nRight side n) gs.length + 2) + 1) + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![gs.flatMap (origRec h) ++ false :: postN, frame side ++ tS, t.fr, t.rp, t.rn, t.ol, t.or, t.pa, t.na, t.tm,
        List.replicate cap false, List.replicate capC2 false, frame (binary h 0),
        streamTape (zeroRecs h (width - nLeft side n)) sZL, streamTape (zeroRecs h (width - nRight side n)) sZR, t.out,
        List.replicate capC3 false, List.replicate capC4 false, streamTape flips staleF, List.replicate capF8 false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ((flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))).flatMap frame).length, 0, 0, 0, 0]
      ![gs.flatMap (origRec h) ++ false :: postN, frame side ++ tS, (flips.foldl (fnext h gs side width) t.fst).fr,
        (flips.foldl (fnext h gs side width) t.fst).ps.rp, (flips.foldl (fnext h gs side width) t.fst).ps.rn,
        (flips.foldl (fnext h gs side width) t.fst).ps.ol, (flips.foldl (fnext h gs side width) t.fst).ps.or,
        (flips.foldl (fnext h gs side width) t.fst).ps.pa, (flips.foldl (fnext h gs side width) t.fst).ps.na,
        (flips.foldl (fnext h gs side width) t.fst).ps.tm, List.replicate cap false, List.replicate capC2 false,
        frame (binary h 0), streamTape (zeroRecs h (width - nLeft side n)) sZL,
        streamTape (zeroRecs h (width - nRight side n)) sZR,
        overlay ((flips.foldl (fnext h gs side width) t.fst).ps.E.flatMap frame) t.out,
        List.replicate capC3 false, List.replicate capC4 false, streamTape flips staleF, List.replicate capF8 false] := by
    refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      (try fin_cases j) <;> rfl
  have e := dockRun c zB zB_inj (rH g d 0 0 0)
    (rA (t.inB (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0))
      (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
      (List.replicate cap false) (List.replicate capC2 false) (List.replicate capC3 false)
      (List.replicate capC4 false) (streamTape flips staleF) (List.replicate capF8 false)))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_zB, dockH_zB] at e
  have hE' : (flips.foldl (fnext h gs side width) t.fst).ps.E = flips.flatMap (fun f => gs.flatMap (denseRecs h side f width)) := by
    rw [fnext_E]; rfl
  rw [hE'] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- Phase C's output: the pool stream closed. -/
def RT.outC (t : RT) (OUT : List Bool) : RT := { t with out := OUT }

/-- **Phase C**: the pool stream closed by `false`. -/
theorem pC_step (g d f b : ℕ) (X B : List Bool) (t : RT) :
    Step (RecoveryFocus.machine zC (putM false)) 1 (rH g d X.length f b) (rA (t.outC (overlay X B)))
      (rH g d (X ++ [false]).length f b) (rA (t.outC (overlay (X ++ [false]) B))) := by
  have p0 := putStep false (overlay X B) X.length
  rw [overlay_write] at p0
  have e := dockRun p0 zC zC_inj (rH g d X.length f b) (rA (t.outC (overlay X B)))
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_zC, dockH_zC] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [rH]

/-- Phase D's constrained tapes. -/
def RT.inD (t : RT) (CN K CV ZW J CL ON OH MK TT LG LG6 FL : List Bool) : RT :=
  { t with cn := CN, gk := K, cv := CV, zw := ZW, jc := J, cl := CL, one := ON, oh := OH, msk := MK, tt := TT, lg := LG, lg6 := LG6, fl := FL }

/-- Phase D's outputs. -/
def RT.outD (t : RT) (Wc Q W : ℕ) (st : GSt) (TB : List Bool) : RT :=
  { t with cv := frame (binary Wc st.last), jc := frame (binary Wc st.last), oh := frame (entC Q W st.c), tt := frame (entC Q W st.c), tb := TB }

/-- **Phase D**: the children table. -/
theorem pD_step (Q W Wc V n : ℕ) (cs : List ℕ) (flips : List (List Bool)) (post staleF : List Bool) (t : RT)
    (g d o x0 capK cap cap5 : ℕ) (h1 : 1 ≤ Wc) (hfl : ∀ f ∈ flips, f.length = n) (hn : 1 ≤ n)
    (hcs : ∀ v ∈ cs, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK) (hc1 : 2 * (Q + W + 1) + 1 ≤ cap)
    (hc2 : 2 * Wc + 2 ≤ cap) (hc3 : 3 * Wc + 2 ≤ cap) (hc5 : gatesCost Q W Wc V cs.length ≤ cap5) :
    Step (RecoveryFocus.machine zD tflipsM) (flips.length * (tflipCost n Q W Wc V cs.length + 2) + 1) (rH g d o 0 0)
      (rA (t.inD (cs.flatMap natWord ++ false :: post) (false :: List.replicate capK true) (frame (binary Wc x0))
        (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true] (frame (entC Q W 0)) (frame (shiftMask Q W))
        (frame (entC Q W 0)) (List.replicate cap false) (List.replicate cap5 false) (streamTape flips staleF)))
      (rH g d o (flips.flatMap frame).length
        (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) ⟨0, x0, []⟩).tbl.length)
      (rA ((t.inD (cs.flatMap natWord ++ false :: post) (false :: List.replicate capK true) (frame (binary Wc x0))
        (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true] (frame (entC Q W 0)) (frame (shiftMask Q W))
        (frame (entC Q W 0)) (List.replicate cap false) (List.replicate cap5 false) (streamTape flips staleF)).outD Wc Q W
        (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) ⟨0, x0, []⟩)
        (overlay (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) ⟨0, x0, []⟩).tbl t.tb))) := by
  have tf := tflips_run Q W Wc V n cs flips post (false :: List.replicate capK true) (frame (binary Wc 0))
    (frame (shiftMask Q W)) t.tb staleF ⟨0, x0, []⟩ capK cap cap5 h1 hfl hn hcs rfl rfl rfl hc1 hc2 hc3 hc5
  have e := dockRun tf zD zD_inj (rH g d o 0 0)
    (rA (t.inD (cs.flatMap natWord ++ false :: post) (false :: List.replicate capK true) (frame (binary Wc x0))
      (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true] (frame (entC Q W 0)) (frame (shiftMask Q W))
      (frame (entC Q W 0)) (List.replicate cap false) (List.replicate cap5 false) (streamTape flips staleF)))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_zD, dockH_zD] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

/-- **The pool builder** after the decomposition: normalize, pull back every flip pattern, close the pool, build the
children table. -/
noncomputable def poolM := Composition.machine (RecoveryFocus.machine zA normR)
  (Composition.machine (RecoveryFocus.machine zB flipsR)
    (Composition.machine (RecoveryFocus.machine zC (putM false)) (RecoveryFocus.machine zD tflipsM)))

def rtPool (GSW K MR ZH NM LG DN LG2 DB SD FR RP RN OL OR PA NA TM LG3 ZL ZR OUT LG4 LG5 FL CN CV ZW J CL ON OH MK TT TB
    LG6 LG7 LG8 : List Bool) : RT :=
  ⟨GSW, K, MR, ZH, NM, LG, DN, LG2, DB, SD, FR, RP, RN, OL, OR, PA, NA, TM, LG3, ZL, ZR, OUT, LG4, LG5, FL, CN, CV, ZW, J,
    CL, ON, OH, MK, TT, TB, LG6, LG7, LG8⟩

theorem normTape_overlay (h : ℕ) {n : ℕ} (gs : List (ExactThresholdGate n)) (BWN : List Bool) :
    gs.flatMap (origRec h) ++ false :: BWN.drop (normTape h gs).length = overlay (normTape h gs) BWN := by
  simp [overlay, normTape, List.append_assoc]

variable (a : DecompositionAlgorithm)

theorem pool_run (h Q Wc V : ℕ) (h1 : 1 ≤ h) (hW1 : 1 ≤ Wc) {n : ℕ} (hn : 1 ≤ n) (gates : List (SupportedNormalizedGate n))
    (side : List Bool) (width : ℕ) (flips : List (List Bool)) (hs : side.length = n)
    (hfl : ∀ f ∈ flips, f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postG postC tS sZL sZR staleF MR FR RP RN OL OR PA NA TM NM OUT TB : List Bool)
    (x0 capK cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 : ℕ)
    (hok : ∀ e ∈ GS a gates, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hcs : ∀ v ∈ counts a gates, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK)
    (hc1 : 2 * h + 1 ≤ cap) (hcF : 2 * n + 1 ≤ cap)
    (hcT1 : 2 * (Q + flips.length * (counts a gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * Wc + 2 ≤ cap)
    (hcT3 : 3 * Wc + 2 ≤ cap)
    (hcN2 : innerCost h n ≤ capN2) (hcN7 : normCost h n (GS a gates).length ≤ capN7) (hcC2 : cloopCost h n ≤ capC2)
    (hcC3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ capC3)
    (hcC4 : kidsCost h n width (nLeft side n) (nRight side n) (GS a gates).length ≤ capC4)
    (hcF8 : flips.length * (flipCost h n width (nLeft side n) (nRight side n) (GS a gates).length + 2) + 1 ≤ capF8)
    (hc5 : gatesCost Q (flips.length * (counts a gates).sum) Wc V (counts a gates).length ≤ cap5) :
    ∃ tout : RT, ∃ cost : ℕ, tout.out = overlay ((poolRecs a h gates side width flips).flatMap frame ++ [false]) OUT ∧
      tout.tb = overlay ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream) TB ∧
      Step poolM cost (rH 0 0 0 0 0)
        (rA (rtPool ((GS a gates).flatMap exactWord ++ postG) (false :: List.replicate capK true) MR (frame (binary h 0))
          NM (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false)
          (List.replicate (GS a gates).length true) (frame side ++ tS) FR RP RN OL OR PA NA TM
          (List.replicate capC2 false) (streamTape (zeroRecs h (width - nLeft side n)) sZL)
          (streamTape (zeroRecs h (width - nRight side n)) sZR) OUT (List.replicate capC3 false)
          (List.replicate capC4 false) (streamTape flips staleF) ((counts a gates).flatMap natWord ++ false :: postC)
          (frame (binary Wc x0)) (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true]
          (frame (entC Q (flips.length * (counts a gates).sum) 0)) (frame (shiftMask Q (flips.length * (counts a gates).sum)))
          (frame (entC Q (flips.length * (counts a gates).sum) 0)) TB (List.replicate cap5 false)
          (List.replicate capN7 false) (List.replicate capF8 false)))
        (rH ((GS a gates).flatMap exactWord).length (GS a gates).length
          ((poolRecs a h gates side width flips).flatMap frame ++ [false]).length (flips.flatMap frame).length
          ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream).length)
        (rA tout) := by
  set gs := GS a gates
  set W := flips.length * (counts a gates).sum
  set t0 := rtPool (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) MR (frame (binary h 0))
    NM (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false)
    (List.replicate gs.length true) (frame side ++ tS) FR RP RN OL OR PA NA TM
    (List.replicate capC2 false) (streamTape (zeroRecs h (width - nLeft side n)) sZL)
    (streamTape (zeroRecs h (width - nRight side n)) sZR) OUT (List.replicate capC3 false)
    (List.replicate capC4 false) (streamTape flips staleF) ((counts a gates).flatMap natWord ++ false :: postC)
    (frame (binary Wc x0)) (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true]
    (frame (entC Q W 0)) (frame (shiftMask Q W)) (frame (entC Q W 0)) TB (List.replicate cap5 false)
    (List.replicate capN7 false) (List.replicate capF8 false)
  have sA := pA_step h h1 gs postG t0 capK cap capN2 capN7 hok hc1 hcN2 hcN7
  set x1 := (t0.inA (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) (frame (binary h 0))
    (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false) (List.replicate gs.length true)
    (List.replicate capN7 false)).outA (mrKids h MR gs) (overlay (normTape h gs) NM)
  have sB := pB_step h h1 hn gs side width flips hs hfl hL hR (NM.drop (normTape h gs).length) tS sZL sZR staleF x1
    (gs.flatMap exactWord).length gs.length cap capC2 capC3 capC4 capF8 hc1 hcF hcC2 hcC3 hcC4 hcF8
  rw [normTape_overlay] at sB
  set E' := flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))
  set st' := flips.foldl (fnext h gs side width) x1.fst
  set x2 := (x1.inB (overlay (normTape h gs) NM) (frame side ++ tS) (frame (binary h 0))
    (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
    (List.replicate cap false) (List.replicate capC2 false) (List.replicate capC3 false)
    (List.replicate capC4 false) (streamTape flips staleF) (List.replicate capF8 false)).outB st' (overlay (E'.flatMap frame) OUT)
  have sC := pC_step (gs.flatMap exactWord).length gs.length 0 0 (E'.flatMap frame) OUT x2
  set x3 := x2.outC (overlay (E'.flatMap frame ++ [false]) OUT)
  have sD := pD_step Q W Wc V n (counts a gates) flips postC staleF x3 (gs.flatMap exactWord).length gs.length
    (E'.flatMap frame ++ [false]).length x0 capK cap cap5 hW1 hfl hn hcs hcT1 hcT2 hcT3 hc5
  set gst := flips.foldl (fun st _ => (counts a gates).foldl (gnext Q W) st) ⟨0, x0, []⟩
  have j := sA.seq (sB.seq (sC.seq sD))
  have hE : (E'.flatMap frame ++ [false]).length = ((poolRecs a h gates side width flips).flatMap frame ++ [false]).length := by
    rw [poolRecs_eq]
  have ht := table_eq a Q gates side width flips [] x0
  simp only [List.nil_append] at ht
  have hT : gst.tbl.length = ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream).length := by
    rw [ht]
  rw [hE, hT] at j
  refine ⟨_, _, ?_, ?_, j⟩
  · show overlay (E'.flatMap frame ++ [false]) OUT = _
    rw [poolRecs_eq]
  · show overlay gst.tbl TB = _
    rw [ht]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
