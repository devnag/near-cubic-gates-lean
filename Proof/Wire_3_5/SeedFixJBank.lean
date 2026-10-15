import Proof.Wire_3_5.SeedFixEmit

/-! # C4.Sb, machine part 16: the enumeration cell's bank

One bank serves every block of a term group: the counter's fields, the cell words, the validity test, the constraint
records, the elimination (its 31 tapes), the coefficient, the eight fetches and the emission. Blocks share eight logs
`L0 … L7` (each block restores its logs to blank). The last two tapes are the enumeration's counter bank. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

namespace JBank

/-- The cell's tapes. -/
structure JT where
  BT : List Bool
  AL : List Bool
  DG : List Bool
  DN : List Bool
  CL : List Bool
  LAB : List Bool
  QM : List Bool
  CC : List Bool
  V : List Bool
  ONE : List Bool
  CT : List Bool
  ONES8 : List Bool
  SG : List Bool
  ACC : List Bool
  Y : List Bool
  ROW : List Bool
  AT : List Bool
  BAT : List Bool
  CNT : List Bool
  TGT : List Bool
  FLAG : List Bool
  TW : List Bool
  OUT : List Bool
  R8 : List Bool
  RL : List Bool
  RK : List Bool
  R1 : List Bool
  R7 : List Bool
  RK2 : List Bool
  RA : List Bool
  RC : List Bool
  RT : List Bool
  PW : List Bool
  FL : List Bool
  RX : List Bool
  RZ : List Bool
  Z9 : List Bool
  PFX : List Bool
  MC : List Bool
  RR : List Bool
  RB : List Bool
  Z18 : List Bool
  O : List Bool
  ONEW : List Bool
  W : List Bool
  P : List Bool
  K : List Bool
  CC2 : List Bool
  G : List Bool
  XE : List Bool
  L0 : List Bool
  L1 : List Bool
  L2 : List Bool
  L3 : List Bool
  L4 : List Bool
  L5 : List Bool
  L6 : List Bool
  L7 : List Bool
  C : List Bool
  CW : List Bool

/-- The tapes in order. -/
def JT.toList (T : JT) : List (List Bool) :=
  [T.BT, T.AL, T.DG, T.DN, T.CL, T.LAB, T.QM, T.CC, T.V, T.ONE, T.CT, T.ONES8, T.SG, T.ACC, T.Y, T.ROW, T.AT, T.BAT,
    T.CNT, T.TGT, T.FLAG, T.TW, T.OUT, T.R8, T.RL, T.RK, T.R1, T.R7, T.RK2, T.RA, T.RC, T.RT, T.PW, T.FL, T.RX, T.RZ,
    T.Z9, T.PFX, T.MC, T.RR, T.RB, T.Z18, T.O, T.ONEW, T.W, T.P, T.K, T.CC2, T.G, T.XE, T.L0, T.L1, T.L2, T.L3, T.L4,
    T.L5, T.L6, T.L7, T.C, T.CW]

/-- The bank (a list lookup, so that two banks differing in some tapes compare entry by entry in linear time). -/
def JT.vec (T : JT) : Fin 60 → List Bool := fun i => T.toList.getD i.val []

/-! ## Slot maps of the blocks -/

def slCells : Fin 4 → Fin 60 := ![2, 3, 4, 50]

theorem slCells_inj : Function.Injective slCells := by decide

theorem install_slCells (A : Fin 60 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install slCells A v =
      ![A 0, A 1, v 0, v 1, v 2, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 3, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCells slCells_inj A v 0
  · exact RecoveryRootRound.install_slot slCells slCells_inj A v 1
  · exact RecoveryRootRound.install_slot slCells slCells_inj A v 2
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCells slCells_inj A v 3
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)
  · exact RecoveryRootRound.install_other slCells A v _ (by decide)

def slValid : Fin 9 → Fin 60 := ![23, 1, 5, 6, 7, 8, 9, 50, 51]

theorem slValid_inj : Function.Injective slValid := by decide

theorem install_slValid (A : Fin 60 → List Bool) (v : Fin 9 → List Bool) :
    RecoveryRootRound.install slValid A v =
      ![A 0, v 1, A 2, A 3, A 4, v 2, v 3, v 4, v 5, v 6, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 0, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 7, v 8, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 1
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 2
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 3
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 4
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 5
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 6
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 0
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 7
  · exact RecoveryRootRound.install_slot slValid slValid_inj A v 8
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)
  · exact RecoveryRootRound.install_other slValid A v _ (by decide)

def slCons : Fin 5 → Fin 60 := ![0, 1, 4, 10, 50]

theorem slCons_inj : Function.Injective slCons := by decide

theorem install_slCons (A : Fin 60 → List Bool) (v : Fin 5 → List Bool) :
    RecoveryRootRound.install slCons A v =
      ![v 0, v 1, A 2, A 3, v 2, A 5, A 6, A 7, A 8, A 9, v 3, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 4, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slCons slCons_inj A v 0
  · exact RecoveryRootRound.install_slot slCons slCons_inj A v 1
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCons slCons_inj A v 2
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCons slCons_inj A v 3
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCons slCons_inj A v 4
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)
  · exact RecoveryRootRound.install_other slCons A v _ (by decide)

def slElim : Fin 31 → Fin 60 := ![23, 24, 29, 30, 31, 32, 33, 34, 35, 36, 50, 51, 52, 53, 37, 38, 39, 40, 41, 42, 43, 54, 10, 55, 56, 44, 45, 46, 47, 48, 49]

theorem slElim_inj : Function.Injective slElim := by decide

theorem install_slElim (A : Fin 60 → List Bool) (v : Fin 31 → List Bool) :
    RecoveryRootRound.install slElim A v =
      ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 22, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 0, v 1, A 25, A 26, A 27, A 28, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 25, v 26, v 27, v 28, v 29, v 30, v 10, v 11, v 12, v 13, v 21, v 23, v 24, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 22
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 0
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 1
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 2
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 3
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 4
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 5
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 6
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 7
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 8
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 9
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 14
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 15
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 16
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 17
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 18
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 19
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 20
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 25
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 26
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 27
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 28
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 29
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 30
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 10
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 11
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 12
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 13
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 21
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 23
  · exact RecoveryRootRound.install_slot slElim slElim_inj A v 24
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)
  · exact RecoveryRootRound.install_other slElim A v _ (by decide)

def slCoef : Fin 9 → Fin 60 := ![0, 11, 12, 28, 49, 13, 50, 51, 52]

theorem slCoef_inj : Function.Injective slCoef := by decide

theorem install_slCoef (A : Fin 60 → List Bool) (v : Fin 9 → List Bool) :
    RecoveryRootRound.install slCoef A v =
      ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 1, v 2, v 5, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, v 3, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, v 4, v 6, v 7, v 8, A 53, A 54, A 55, A 56, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 0
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 1
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 2
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 5
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 3
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 4
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 6
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 7
  · exact RecoveryRootRound.install_slot slCoef slCoef_inj A v 8
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)
  · exact RecoveryRootRound.install_other slCoef A v _ (by decide)

def slFetch : Fin 20 → Fin 60 := ![17, 13, 14, 15, 16, 50, 51, 52, 53, 18, 19, 20, 9, 54, 55, 4, 21, 23, 56, 57]

theorem slFetch_inj : Function.Injective slFetch := by decide

theorem install_slFetch (A : Fin 60 → List Bool) (v : Fin 20 → List Bool) :
    RecoveryRootRound.install slFetch A v =
      ![A 0, A 1, A 2, A 3, v 15, A 5, A 6, A 7, A 8, v 12, A 10, A 11, A 12, v 1, v 2, v 3, v 4, v 0, v 9, v 10, v 11, v 16, A 22, v 17, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 5, v 6, v 7, v 8, v 13, v 14, v 18, v 19, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 15
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 12
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 1
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 2
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 3
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 4
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 0
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 9
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 10
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 11
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 16
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 17
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 5
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 6
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 7
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 8
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 13
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 14
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 18
  · exact RecoveryRootRound.install_slot slFetch slFetch_inj A v 19
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)
  · exact RecoveryRootRound.install_other slFetch A v _ (by decide)

def slEmit : Fin 3 → Fin 60 := ![13, 22, 50]

theorem slEmit_inj : Function.Injective slEmit := by decide

theorem install_slEmit (A : Fin 60 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install slEmit A v =
      ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, v 0, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 1, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, v 2, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_slot slEmit slEmit_inj A v 0
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_slot slEmit slEmit_inj A v 1
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_slot slEmit slEmit_inj A v 2
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)
  · exact RecoveryRootRound.install_other slEmit A v _ (by decide)

end JBank

end NearCubicWires.WireExponent3_5.SeedFix
