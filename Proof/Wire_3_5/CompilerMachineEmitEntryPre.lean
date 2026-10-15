import Proof.Wire_3_5.CompilerMachineEmitCoefOut

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The stack's bits behind the sentinels. -/
def stackBits (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    List (List Bool) :=
  (List.range (2 * (width + width + 1))).map fun r => L.flatMap fun fe => (labRecs h side width fe).getD r []

theorem stackRecs_bits (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    stackRecs h side width L = (stackBits h side width L).map (true :: ·) := by
  simp [stackRecs, stackBits, List.map_map, Function.comp_def]

theorem stackBits_length (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    (stackBits h side width L).length = 2 * (width + width + 1) := by
  simp [stackBits]

theorem stackBits_width (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    ∀ b ∈ stackBits h side width L, b.length = L.length * h := by
  intro b hb
  have hr : (true :: b) ∈ stackRecs h side width L := by
    rw [stackRecs_bits]; exact List.mem_map_of_mem hb
  have := stackRecs_width h side width L _ hr
  simp at this
  omega

/-- The entry register behind its size field and marker: the framed mask. -/
theorem re_split (Q W k U : ℕ) (Y : List Bool) :
    overlay (frame (entryWord Q W k U)) Y =
      fpre (thermo Q k ++ [true]) ++ (frame (binary W U) ++ Y.drop (frame (entryWord Q W k U)).length) := by
  unfold overlay
  rw [show entryWord Q W k U = (thermo Q k ++ [true]) ++ binary W U by simp [entryWord], frame_append',
    List.append_assoc]

theorem pre_length (Q k : ℕ) (hk : k ≤ Q) : (fpre (thermo Q k ++ [true])).length = 2 * Q + 2 := by
  simp [fpre_length, thermo_length Q k hk]
  ring

/-- The stack as a stream of sentinel records. -/
theorem s1_split (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (X : List Bool) :
    overlay (stackStream h side width L) X =
      streamTape ((stackBits h side width L).map (true :: ·))
        (X.drop (((stackRecs h side width L).flatMap frame).length + 1)) := by
  unfold stackStream
  have e := overlay_stream (stackRecs h side width L) X
  have hs : streamTape (stackRecs h side width L) [] = (stackRecs h side width L).flatMap frame ++ [false] := rfl
  rw [hs, e, stackRecs_bits]

/-- One more occurrence counted. -/
theorem cntStep (cnt : ℕ) (C : List Bool) :
    Step (putM true) 1 ![cnt] ![overlay (List.replicate cnt true) C] ![cnt + 1]
      ![overlay (List.replicate (cnt + 1) true) C] := by
  have e := putStep true (overlay (List.replicate cnt true) C) cnt
  have hw : writeTapeBit (overlay (List.replicate cnt true) C) cnt true = overlay (List.replicate (cnt + 1) true) C := by
    have := overlay_write (List.replicate cnt true) C true
    rw [List.length_replicate] at this
    rw [this, List.replicate_succ']
  rw [hw] at e
  exact e

def eLoad : Fin 3 → Fin 29 := ![0, 9, 24]
def eGR : Fin 1 → Fin 29 := ![0]
def eS1 : Fin 3 → Fin 29 := ![10, 4, 24]
def eS2 : Fin 3 → Fin 29 := ![11, 4, 24]
def eCoef : Fin 13 → Fin 29 := ![9, 5, 7, 8, 17, 3, 18, 19, 20, 21, 22, 24, 28]
def eLab : Fin 6 → Fin 29 := ![9, 1, 10, 11, 25, 26]
def eCut : Fin 11 → Fin 29 := ![10, 3, 12, 13, 14, 15, 2, 24, 6, 16, 27]
def eEv : Fin 4 → Fin 29 := ![21, 2, 17, 24]
def eEnv : Fin 4 → Fin 29 := ![22, 2, 17, 24]
def eCnt : Fin 1 → Fin 29 := ![23]

theorem eLoad_inj : Function.Injective eLoad := by decide

theorem install_eLoad (A : Fin 29 → List Bool) (v : Fin 3 → List Bool) :
    install eLoad A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 1, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 2, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_slot eLoad eLoad_inj A v 0
  · exact install_other eLoad A v 1 (by decide)
  · exact install_other eLoad A v 2 (by decide)
  · exact install_other eLoad A v 3 (by decide)
  · exact install_other eLoad A v 4 (by decide)
  · exact install_other eLoad A v 5 (by decide)
  · exact install_other eLoad A v 6 (by decide)
  · exact install_other eLoad A v 7 (by decide)
  · exact install_other eLoad A v 8 (by decide)
  · exact install_slot eLoad eLoad_inj A v 1
  · exact install_other eLoad A v 10 (by decide)
  · exact install_other eLoad A v 11 (by decide)
  · exact install_other eLoad A v 12 (by decide)
  · exact install_other eLoad A v 13 (by decide)
  · exact install_other eLoad A v 14 (by decide)
  · exact install_other eLoad A v 15 (by decide)
  · exact install_other eLoad A v 16 (by decide)
  · exact install_other eLoad A v 17 (by decide)
  · exact install_other eLoad A v 18 (by decide)
  · exact install_other eLoad A v 19 (by decide)
  · exact install_other eLoad A v 20 (by decide)
  · exact install_other eLoad A v 21 (by decide)
  · exact install_other eLoad A v 22 (by decide)
  · exact install_other eLoad A v 23 (by decide)
  · exact install_slot eLoad eLoad_inj A v 2
  · exact install_other eLoad A v 25 (by decide)
  · exact install_other eLoad A v 26 (by decide)
  · exact install_other eLoad A v 27 (by decide)
  · exact install_other eLoad A v 28 (by decide)

theorem dockH_eLoad (H : Fin 29 → ℕ) (v : Fin 3 → ℕ) :
    dockH eLoad H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 1, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 2, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_slot eLoad eLoad_inj H v 0
  · exact dockH_other eLoad H v 1 (by decide)
  · exact dockH_other eLoad H v 2 (by decide)
  · exact dockH_other eLoad H v 3 (by decide)
  · exact dockH_other eLoad H v 4 (by decide)
  · exact dockH_other eLoad H v 5 (by decide)
  · exact dockH_other eLoad H v 6 (by decide)
  · exact dockH_other eLoad H v 7 (by decide)
  · exact dockH_other eLoad H v 8 (by decide)
  · exact dockH_slot eLoad eLoad_inj H v 1
  · exact dockH_other eLoad H v 10 (by decide)
  · exact dockH_other eLoad H v 11 (by decide)
  · exact dockH_other eLoad H v 12 (by decide)
  · exact dockH_other eLoad H v 13 (by decide)
  · exact dockH_other eLoad H v 14 (by decide)
  · exact dockH_other eLoad H v 15 (by decide)
  · exact dockH_other eLoad H v 16 (by decide)
  · exact dockH_other eLoad H v 17 (by decide)
  · exact dockH_other eLoad H v 18 (by decide)
  · exact dockH_other eLoad H v 19 (by decide)
  · exact dockH_other eLoad H v 20 (by decide)
  · exact dockH_other eLoad H v 21 (by decide)
  · exact dockH_other eLoad H v 22 (by decide)
  · exact dockH_other eLoad H v 23 (by decide)
  · exact dockH_slot eLoad eLoad_inj H v 2
  · exact dockH_other eLoad H v 25 (by decide)
  · exact dockH_other eLoad H v 26 (by decide)
  · exact dockH_other eLoad H v 27 (by decide)
  · exact dockH_other eLoad H v 28 (by decide)

theorem eGR_inj : Function.Injective eGR := by decide

theorem install_eGR (A : Fin 29 → List Bool) (v : Fin 1 → List Bool) :
    install eGR A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_slot eGR eGR_inj A v 0
  · exact install_other eGR A v 1 (by decide)
  · exact install_other eGR A v 2 (by decide)
  · exact install_other eGR A v 3 (by decide)
  · exact install_other eGR A v 4 (by decide)
  · exact install_other eGR A v 5 (by decide)
  · exact install_other eGR A v 6 (by decide)
  · exact install_other eGR A v 7 (by decide)
  · exact install_other eGR A v 8 (by decide)
  · exact install_other eGR A v 9 (by decide)
  · exact install_other eGR A v 10 (by decide)
  · exact install_other eGR A v 11 (by decide)
  · exact install_other eGR A v 12 (by decide)
  · exact install_other eGR A v 13 (by decide)
  · exact install_other eGR A v 14 (by decide)
  · exact install_other eGR A v 15 (by decide)
  · exact install_other eGR A v 16 (by decide)
  · exact install_other eGR A v 17 (by decide)
  · exact install_other eGR A v 18 (by decide)
  · exact install_other eGR A v 19 (by decide)
  · exact install_other eGR A v 20 (by decide)
  · exact install_other eGR A v 21 (by decide)
  · exact install_other eGR A v 22 (by decide)
  · exact install_other eGR A v 23 (by decide)
  · exact install_other eGR A v 24 (by decide)
  · exact install_other eGR A v 25 (by decide)
  · exact install_other eGR A v 26 (by decide)
  · exact install_other eGR A v 27 (by decide)
  · exact install_other eGR A v 28 (by decide)

theorem dockH_eGR (H : Fin 29 → ℕ) (v : Fin 1 → ℕ) :
    dockH eGR H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_slot eGR eGR_inj H v 0
  · exact dockH_other eGR H v 1 (by decide)
  · exact dockH_other eGR H v 2 (by decide)
  · exact dockH_other eGR H v 3 (by decide)
  · exact dockH_other eGR H v 4 (by decide)
  · exact dockH_other eGR H v 5 (by decide)
  · exact dockH_other eGR H v 6 (by decide)
  · exact dockH_other eGR H v 7 (by decide)
  · exact dockH_other eGR H v 8 (by decide)
  · exact dockH_other eGR H v 9 (by decide)
  · exact dockH_other eGR H v 10 (by decide)
  · exact dockH_other eGR H v 11 (by decide)
  · exact dockH_other eGR H v 12 (by decide)
  · exact dockH_other eGR H v 13 (by decide)
  · exact dockH_other eGR H v 14 (by decide)
  · exact dockH_other eGR H v 15 (by decide)
  · exact dockH_other eGR H v 16 (by decide)
  · exact dockH_other eGR H v 17 (by decide)
  · exact dockH_other eGR H v 18 (by decide)
  · exact dockH_other eGR H v 19 (by decide)
  · exact dockH_other eGR H v 20 (by decide)
  · exact dockH_other eGR H v 21 (by decide)
  · exact dockH_other eGR H v 22 (by decide)
  · exact dockH_other eGR H v 23 (by decide)
  · exact dockH_other eGR H v 24 (by decide)
  · exact dockH_other eGR H v 25 (by decide)
  · exact dockH_other eGR H v 26 (by decide)
  · exact dockH_other eGR H v 27 (by decide)
  · exact dockH_other eGR H v 28 (by decide)

theorem eS1_inj : Function.Injective eS1 := by decide

theorem install_eS1 (A : Fin 29 → List Bool) (v : Fin 3 → List Bool) :
    install eS1 A v = ![A 0, A 1, A 2, A 3, v 1, A 5, A 6, A 7, A 8, A 9, v 0, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 2, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eS1 A v 0 (by decide)
  · exact install_other eS1 A v 1 (by decide)
  · exact install_other eS1 A v 2 (by decide)
  · exact install_other eS1 A v 3 (by decide)
  · exact install_slot eS1 eS1_inj A v 1
  · exact install_other eS1 A v 5 (by decide)
  · exact install_other eS1 A v 6 (by decide)
  · exact install_other eS1 A v 7 (by decide)
  · exact install_other eS1 A v 8 (by decide)
  · exact install_other eS1 A v 9 (by decide)
  · exact install_slot eS1 eS1_inj A v 0
  · exact install_other eS1 A v 11 (by decide)
  · exact install_other eS1 A v 12 (by decide)
  · exact install_other eS1 A v 13 (by decide)
  · exact install_other eS1 A v 14 (by decide)
  · exact install_other eS1 A v 15 (by decide)
  · exact install_other eS1 A v 16 (by decide)
  · exact install_other eS1 A v 17 (by decide)
  · exact install_other eS1 A v 18 (by decide)
  · exact install_other eS1 A v 19 (by decide)
  · exact install_other eS1 A v 20 (by decide)
  · exact install_other eS1 A v 21 (by decide)
  · exact install_other eS1 A v 22 (by decide)
  · exact install_other eS1 A v 23 (by decide)
  · exact install_slot eS1 eS1_inj A v 2
  · exact install_other eS1 A v 25 (by decide)
  · exact install_other eS1 A v 26 (by decide)
  · exact install_other eS1 A v 27 (by decide)
  · exact install_other eS1 A v 28 (by decide)

theorem dockH_eS1 (H : Fin 29 → ℕ) (v : Fin 3 → ℕ) :
    dockH eS1 H v = ![H 0, H 1, H 2, H 3, v 1, H 5, H 6, H 7, H 8, H 9, v 0, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 2, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eS1 H v 0 (by decide)
  · exact dockH_other eS1 H v 1 (by decide)
  · exact dockH_other eS1 H v 2 (by decide)
  · exact dockH_other eS1 H v 3 (by decide)
  · exact dockH_slot eS1 eS1_inj H v 1
  · exact dockH_other eS1 H v 5 (by decide)
  · exact dockH_other eS1 H v 6 (by decide)
  · exact dockH_other eS1 H v 7 (by decide)
  · exact dockH_other eS1 H v 8 (by decide)
  · exact dockH_other eS1 H v 9 (by decide)
  · exact dockH_slot eS1 eS1_inj H v 0
  · exact dockH_other eS1 H v 11 (by decide)
  · exact dockH_other eS1 H v 12 (by decide)
  · exact dockH_other eS1 H v 13 (by decide)
  · exact dockH_other eS1 H v 14 (by decide)
  · exact dockH_other eS1 H v 15 (by decide)
  · exact dockH_other eS1 H v 16 (by decide)
  · exact dockH_other eS1 H v 17 (by decide)
  · exact dockH_other eS1 H v 18 (by decide)
  · exact dockH_other eS1 H v 19 (by decide)
  · exact dockH_other eS1 H v 20 (by decide)
  · exact dockH_other eS1 H v 21 (by decide)
  · exact dockH_other eS1 H v 22 (by decide)
  · exact dockH_other eS1 H v 23 (by decide)
  · exact dockH_slot eS1 eS1_inj H v 2
  · exact dockH_other eS1 H v 25 (by decide)
  · exact dockH_other eS1 H v 26 (by decide)
  · exact dockH_other eS1 H v 27 (by decide)
  · exact dockH_other eS1 H v 28 (by decide)

theorem eS2_inj : Function.Injective eS2 := by decide

theorem install_eS2 (A : Fin 29 → List Bool) (v : Fin 3 → List Bool) :
    install eS2 A v = ![A 0, A 1, A 2, A 3, v 1, A 5, A 6, A 7, A 8, A 9, A 10, v 0, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 2, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eS2 A v 0 (by decide)
  · exact install_other eS2 A v 1 (by decide)
  · exact install_other eS2 A v 2 (by decide)
  · exact install_other eS2 A v 3 (by decide)
  · exact install_slot eS2 eS2_inj A v 1
  · exact install_other eS2 A v 5 (by decide)
  · exact install_other eS2 A v 6 (by decide)
  · exact install_other eS2 A v 7 (by decide)
  · exact install_other eS2 A v 8 (by decide)
  · exact install_other eS2 A v 9 (by decide)
  · exact install_other eS2 A v 10 (by decide)
  · exact install_slot eS2 eS2_inj A v 0
  · exact install_other eS2 A v 12 (by decide)
  · exact install_other eS2 A v 13 (by decide)
  · exact install_other eS2 A v 14 (by decide)
  · exact install_other eS2 A v 15 (by decide)
  · exact install_other eS2 A v 16 (by decide)
  · exact install_other eS2 A v 17 (by decide)
  · exact install_other eS2 A v 18 (by decide)
  · exact install_other eS2 A v 19 (by decide)
  · exact install_other eS2 A v 20 (by decide)
  · exact install_other eS2 A v 21 (by decide)
  · exact install_other eS2 A v 22 (by decide)
  · exact install_other eS2 A v 23 (by decide)
  · exact install_slot eS2 eS2_inj A v 2
  · exact install_other eS2 A v 25 (by decide)
  · exact install_other eS2 A v 26 (by decide)
  · exact install_other eS2 A v 27 (by decide)
  · exact install_other eS2 A v 28 (by decide)

theorem dockH_eS2 (H : Fin 29 → ℕ) (v : Fin 3 → ℕ) :
    dockH eS2 H v = ![H 0, H 1, H 2, H 3, v 1, H 5, H 6, H 7, H 8, H 9, H 10, v 0, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 2, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eS2 H v 0 (by decide)
  · exact dockH_other eS2 H v 1 (by decide)
  · exact dockH_other eS2 H v 2 (by decide)
  · exact dockH_other eS2 H v 3 (by decide)
  · exact dockH_slot eS2 eS2_inj H v 1
  · exact dockH_other eS2 H v 5 (by decide)
  · exact dockH_other eS2 H v 6 (by decide)
  · exact dockH_other eS2 H v 7 (by decide)
  · exact dockH_other eS2 H v 8 (by decide)
  · exact dockH_other eS2 H v 9 (by decide)
  · exact dockH_other eS2 H v 10 (by decide)
  · exact dockH_slot eS2 eS2_inj H v 0
  · exact dockH_other eS2 H v 12 (by decide)
  · exact dockH_other eS2 H v 13 (by decide)
  · exact dockH_other eS2 H v 14 (by decide)
  · exact dockH_other eS2 H v 15 (by decide)
  · exact dockH_other eS2 H v 16 (by decide)
  · exact dockH_other eS2 H v 17 (by decide)
  · exact dockH_other eS2 H v 18 (by decide)
  · exact dockH_other eS2 H v 19 (by decide)
  · exact dockH_other eS2 H v 20 (by decide)
  · exact dockH_other eS2 H v 21 (by decide)
  · exact dockH_other eS2 H v 22 (by decide)
  · exact dockH_other eS2 H v 23 (by decide)
  · exact dockH_slot eS2 eS2_inj H v 2
  · exact dockH_other eS2 H v 25 (by decide)
  · exact dockH_other eS2 H v 26 (by decide)
  · exact dockH_other eS2 H v 27 (by decide)
  · exact dockH_other eS2 H v 28 (by decide)

theorem eCoef_inj : Function.Injective eCoef := by decide

theorem install_eCoef (A : Fin 29 → List Bool) (v : Fin 13 → List Bool) :
    install eCoef A v = ![A 0, A 1, A 2, v 5, A 4, v 1, A 6, v 2, v 3, v 0, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 4, v 6, v 7, v 8, v 9, v 10, A 23, v 11, A 25, A 26, A 27, v 12] := by
  funext i
  fin_cases i
  · exact install_other eCoef A v 0 (by decide)
  · exact install_other eCoef A v 1 (by decide)
  · exact install_other eCoef A v 2 (by decide)
  · exact install_slot eCoef eCoef_inj A v 5
  · exact install_other eCoef A v 4 (by decide)
  · exact install_slot eCoef eCoef_inj A v 1
  · exact install_other eCoef A v 6 (by decide)
  · exact install_slot eCoef eCoef_inj A v 2
  · exact install_slot eCoef eCoef_inj A v 3
  · exact install_slot eCoef eCoef_inj A v 0
  · exact install_other eCoef A v 10 (by decide)
  · exact install_other eCoef A v 11 (by decide)
  · exact install_other eCoef A v 12 (by decide)
  · exact install_other eCoef A v 13 (by decide)
  · exact install_other eCoef A v 14 (by decide)
  · exact install_other eCoef A v 15 (by decide)
  · exact install_other eCoef A v 16 (by decide)
  · exact install_slot eCoef eCoef_inj A v 4
  · exact install_slot eCoef eCoef_inj A v 6
  · exact install_slot eCoef eCoef_inj A v 7
  · exact install_slot eCoef eCoef_inj A v 8
  · exact install_slot eCoef eCoef_inj A v 9
  · exact install_slot eCoef eCoef_inj A v 10
  · exact install_other eCoef A v 23 (by decide)
  · exact install_slot eCoef eCoef_inj A v 11
  · exact install_other eCoef A v 25 (by decide)
  · exact install_other eCoef A v 26 (by decide)
  · exact install_other eCoef A v 27 (by decide)
  · exact install_slot eCoef eCoef_inj A v 12

theorem dockH_eCoef (H : Fin 29 → ℕ) (v : Fin 13 → ℕ) :
    dockH eCoef H v = ![H 0, H 1, H 2, v 5, H 4, v 1, H 6, v 2, v 3, v 0, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 4, v 6, v 7, v 8, v 9, v 10, H 23, v 11, H 25, H 26, H 27, v 12] := by
  funext i
  fin_cases i
  · exact dockH_other eCoef H v 0 (by decide)
  · exact dockH_other eCoef H v 1 (by decide)
  · exact dockH_other eCoef H v 2 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 5
  · exact dockH_other eCoef H v 4 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 1
  · exact dockH_other eCoef H v 6 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 2
  · exact dockH_slot eCoef eCoef_inj H v 3
  · exact dockH_slot eCoef eCoef_inj H v 0
  · exact dockH_other eCoef H v 10 (by decide)
  · exact dockH_other eCoef H v 11 (by decide)
  · exact dockH_other eCoef H v 12 (by decide)
  · exact dockH_other eCoef H v 13 (by decide)
  · exact dockH_other eCoef H v 14 (by decide)
  · exact dockH_other eCoef H v 15 (by decide)
  · exact dockH_other eCoef H v 16 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 4
  · exact dockH_slot eCoef eCoef_inj H v 6
  · exact dockH_slot eCoef eCoef_inj H v 7
  · exact dockH_slot eCoef eCoef_inj H v 8
  · exact dockH_slot eCoef eCoef_inj H v 9
  · exact dockH_slot eCoef eCoef_inj H v 10
  · exact dockH_other eCoef H v 23 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 11
  · exact dockH_other eCoef H v 25 (by decide)
  · exact dockH_other eCoef H v 26 (by decide)
  · exact dockH_other eCoef H v 27 (by decide)
  · exact dockH_slot eCoef eCoef_inj H v 12

theorem eLab_inj : Function.Injective eLab := by decide

theorem install_eLab (A : Fin 29 → List Bool) (v : Fin 6 → List Bool) :
    install eLab A v = ![A 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, v 2, v 3, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, v 4, v 5, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eLab A v 0 (by decide)
  · exact install_slot eLab eLab_inj A v 1
  · exact install_other eLab A v 2 (by decide)
  · exact install_other eLab A v 3 (by decide)
  · exact install_other eLab A v 4 (by decide)
  · exact install_other eLab A v 5 (by decide)
  · exact install_other eLab A v 6 (by decide)
  · exact install_other eLab A v 7 (by decide)
  · exact install_other eLab A v 8 (by decide)
  · exact install_slot eLab eLab_inj A v 0
  · exact install_slot eLab eLab_inj A v 2
  · exact install_slot eLab eLab_inj A v 3
  · exact install_other eLab A v 12 (by decide)
  · exact install_other eLab A v 13 (by decide)
  · exact install_other eLab A v 14 (by decide)
  · exact install_other eLab A v 15 (by decide)
  · exact install_other eLab A v 16 (by decide)
  · exact install_other eLab A v 17 (by decide)
  · exact install_other eLab A v 18 (by decide)
  · exact install_other eLab A v 19 (by decide)
  · exact install_other eLab A v 20 (by decide)
  · exact install_other eLab A v 21 (by decide)
  · exact install_other eLab A v 22 (by decide)
  · exact install_other eLab A v 23 (by decide)
  · exact install_other eLab A v 24 (by decide)
  · exact install_slot eLab eLab_inj A v 4
  · exact install_slot eLab eLab_inj A v 5
  · exact install_other eLab A v 27 (by decide)
  · exact install_other eLab A v 28 (by decide)

theorem dockH_eLab (H : Fin 29 → ℕ) (v : Fin 6 → ℕ) :
    dockH eLab H v = ![H 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 0, v 2, v 3, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, v 4, v 5, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eLab H v 0 (by decide)
  · exact dockH_slot eLab eLab_inj H v 1
  · exact dockH_other eLab H v 2 (by decide)
  · exact dockH_other eLab H v 3 (by decide)
  · exact dockH_other eLab H v 4 (by decide)
  · exact dockH_other eLab H v 5 (by decide)
  · exact dockH_other eLab H v 6 (by decide)
  · exact dockH_other eLab H v 7 (by decide)
  · exact dockH_other eLab H v 8 (by decide)
  · exact dockH_slot eLab eLab_inj H v 0
  · exact dockH_slot eLab eLab_inj H v 2
  · exact dockH_slot eLab eLab_inj H v 3
  · exact dockH_other eLab H v 12 (by decide)
  · exact dockH_other eLab H v 13 (by decide)
  · exact dockH_other eLab H v 14 (by decide)
  · exact dockH_other eLab H v 15 (by decide)
  · exact dockH_other eLab H v 16 (by decide)
  · exact dockH_other eLab H v 17 (by decide)
  · exact dockH_other eLab H v 18 (by decide)
  · exact dockH_other eLab H v 19 (by decide)
  · exact dockH_other eLab H v 20 (by decide)
  · exact dockH_other eLab H v 21 (by decide)
  · exact dockH_other eLab H v 22 (by decide)
  · exact dockH_other eLab H v 23 (by decide)
  · exact dockH_other eLab H v 24 (by decide)
  · exact dockH_slot eLab eLab_inj H v 4
  · exact dockH_slot eLab eLab_inj H v 5
  · exact dockH_other eLab H v 27 (by decide)
  · exact dockH_other eLab H v 28 (by decide)

theorem eCut_inj : Function.Injective eCut := by decide

theorem install_eCut (A : Fin 29 → List Bool) (v : Fin 11 → List Bool) :
    install eCut A v = ![A 0, A 1, v 6, v 1, A 4, A 5, v 8, A 7, A 8, A 9, v 0, A 11, v 2, v 3, v 4, v 5, v 9, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 7, A 25, A 26, v 10, A 28] := by
  funext i
  fin_cases i
  · exact install_other eCut A v 0 (by decide)
  · exact install_other eCut A v 1 (by decide)
  · exact install_slot eCut eCut_inj A v 6
  · exact install_slot eCut eCut_inj A v 1
  · exact install_other eCut A v 4 (by decide)
  · exact install_other eCut A v 5 (by decide)
  · exact install_slot eCut eCut_inj A v 8
  · exact install_other eCut A v 7 (by decide)
  · exact install_other eCut A v 8 (by decide)
  · exact install_other eCut A v 9 (by decide)
  · exact install_slot eCut eCut_inj A v 0
  · exact install_other eCut A v 11 (by decide)
  · exact install_slot eCut eCut_inj A v 2
  · exact install_slot eCut eCut_inj A v 3
  · exact install_slot eCut eCut_inj A v 4
  · exact install_slot eCut eCut_inj A v 5
  · exact install_slot eCut eCut_inj A v 9
  · exact install_other eCut A v 17 (by decide)
  · exact install_other eCut A v 18 (by decide)
  · exact install_other eCut A v 19 (by decide)
  · exact install_other eCut A v 20 (by decide)
  · exact install_other eCut A v 21 (by decide)
  · exact install_other eCut A v 22 (by decide)
  · exact install_other eCut A v 23 (by decide)
  · exact install_slot eCut eCut_inj A v 7
  · exact install_other eCut A v 25 (by decide)
  · exact install_other eCut A v 26 (by decide)
  · exact install_slot eCut eCut_inj A v 10
  · exact install_other eCut A v 28 (by decide)

theorem dockH_eCut (H : Fin 29 → ℕ) (v : Fin 11 → ℕ) :
    dockH eCut H v = ![H 0, H 1, v 6, v 1, H 4, H 5, v 8, H 7, H 8, H 9, v 0, H 11, v 2, v 3, v 4, v 5, v 9, H 17, H 18, H 19, H 20, H 21, H 22, H 23, v 7, H 25, H 26, v 10, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eCut H v 0 (by decide)
  · exact dockH_other eCut H v 1 (by decide)
  · exact dockH_slot eCut eCut_inj H v 6
  · exact dockH_slot eCut eCut_inj H v 1
  · exact dockH_other eCut H v 4 (by decide)
  · exact dockH_other eCut H v 5 (by decide)
  · exact dockH_slot eCut eCut_inj H v 8
  · exact dockH_other eCut H v 7 (by decide)
  · exact dockH_other eCut H v 8 (by decide)
  · exact dockH_other eCut H v 9 (by decide)
  · exact dockH_slot eCut eCut_inj H v 0
  · exact dockH_other eCut H v 11 (by decide)
  · exact dockH_slot eCut eCut_inj H v 2
  · exact dockH_slot eCut eCut_inj H v 3
  · exact dockH_slot eCut eCut_inj H v 4
  · exact dockH_slot eCut eCut_inj H v 5
  · exact dockH_slot eCut eCut_inj H v 9
  · exact dockH_other eCut H v 17 (by decide)
  · exact dockH_other eCut H v 18 (by decide)
  · exact dockH_other eCut H v 19 (by decide)
  · exact dockH_other eCut H v 20 (by decide)
  · exact dockH_other eCut H v 21 (by decide)
  · exact dockH_other eCut H v 22 (by decide)
  · exact dockH_other eCut H v 23 (by decide)
  · exact dockH_slot eCut eCut_inj H v 7
  · exact dockH_other eCut H v 25 (by decide)
  · exact dockH_other eCut H v 26 (by decide)
  · exact dockH_slot eCut eCut_inj H v 10
  · exact dockH_other eCut H v 28 (by decide)

theorem eEv_inj : Function.Injective eEv := by decide

theorem install_eEv (A : Fin 29 → List Bool) (v : Fin 4 → List Bool) :
    install eEv A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 2, A 18, A 19, A 20, v 0, A 22, A 23, v 3, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eEv A v 0 (by decide)
  · exact install_other eEv A v 1 (by decide)
  · exact install_slot eEv eEv_inj A v 1
  · exact install_other eEv A v 3 (by decide)
  · exact install_other eEv A v 4 (by decide)
  · exact install_other eEv A v 5 (by decide)
  · exact install_other eEv A v 6 (by decide)
  · exact install_other eEv A v 7 (by decide)
  · exact install_other eEv A v 8 (by decide)
  · exact install_other eEv A v 9 (by decide)
  · exact install_other eEv A v 10 (by decide)
  · exact install_other eEv A v 11 (by decide)
  · exact install_other eEv A v 12 (by decide)
  · exact install_other eEv A v 13 (by decide)
  · exact install_other eEv A v 14 (by decide)
  · exact install_other eEv A v 15 (by decide)
  · exact install_other eEv A v 16 (by decide)
  · exact install_slot eEv eEv_inj A v 2
  · exact install_other eEv A v 18 (by decide)
  · exact install_other eEv A v 19 (by decide)
  · exact install_other eEv A v 20 (by decide)
  · exact install_slot eEv eEv_inj A v 0
  · exact install_other eEv A v 22 (by decide)
  · exact install_other eEv A v 23 (by decide)
  · exact install_slot eEv eEv_inj A v 3
  · exact install_other eEv A v 25 (by decide)
  · exact install_other eEv A v 26 (by decide)
  · exact install_other eEv A v 27 (by decide)
  · exact install_other eEv A v 28 (by decide)

theorem dockH_eEv (H : Fin 29 → ℕ) (v : Fin 4 → ℕ) :
    dockH eEv H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 2, H 18, H 19, H 20, v 0, H 22, H 23, v 3, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eEv H v 0 (by decide)
  · exact dockH_other eEv H v 1 (by decide)
  · exact dockH_slot eEv eEv_inj H v 1
  · exact dockH_other eEv H v 3 (by decide)
  · exact dockH_other eEv H v 4 (by decide)
  · exact dockH_other eEv H v 5 (by decide)
  · exact dockH_other eEv H v 6 (by decide)
  · exact dockH_other eEv H v 7 (by decide)
  · exact dockH_other eEv H v 8 (by decide)
  · exact dockH_other eEv H v 9 (by decide)
  · exact dockH_other eEv H v 10 (by decide)
  · exact dockH_other eEv H v 11 (by decide)
  · exact dockH_other eEv H v 12 (by decide)
  · exact dockH_other eEv H v 13 (by decide)
  · exact dockH_other eEv H v 14 (by decide)
  · exact dockH_other eEv H v 15 (by decide)
  · exact dockH_other eEv H v 16 (by decide)
  · exact dockH_slot eEv eEv_inj H v 2
  · exact dockH_other eEv H v 18 (by decide)
  · exact dockH_other eEv H v 19 (by decide)
  · exact dockH_other eEv H v 20 (by decide)
  · exact dockH_slot eEv eEv_inj H v 0
  · exact dockH_other eEv H v 22 (by decide)
  · exact dockH_other eEv H v 23 (by decide)
  · exact dockH_slot eEv eEv_inj H v 3
  · exact dockH_other eEv H v 25 (by decide)
  · exact dockH_other eEv H v 26 (by decide)
  · exact dockH_other eEv H v 27 (by decide)
  · exact dockH_other eEv H v 28 (by decide)

theorem eEnv_inj : Function.Injective eEnv := by decide

theorem install_eEnv (A : Fin 29 → List Bool) (v : Fin 4 → List Bool) :
    install eEnv A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 2, A 18, A 19, A 20, A 21, v 0, A 23, v 3, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eEnv A v 0 (by decide)
  · exact install_other eEnv A v 1 (by decide)
  · exact install_slot eEnv eEnv_inj A v 1
  · exact install_other eEnv A v 3 (by decide)
  · exact install_other eEnv A v 4 (by decide)
  · exact install_other eEnv A v 5 (by decide)
  · exact install_other eEnv A v 6 (by decide)
  · exact install_other eEnv A v 7 (by decide)
  · exact install_other eEnv A v 8 (by decide)
  · exact install_other eEnv A v 9 (by decide)
  · exact install_other eEnv A v 10 (by decide)
  · exact install_other eEnv A v 11 (by decide)
  · exact install_other eEnv A v 12 (by decide)
  · exact install_other eEnv A v 13 (by decide)
  · exact install_other eEnv A v 14 (by decide)
  · exact install_other eEnv A v 15 (by decide)
  · exact install_other eEnv A v 16 (by decide)
  · exact install_slot eEnv eEnv_inj A v 2
  · exact install_other eEnv A v 18 (by decide)
  · exact install_other eEnv A v 19 (by decide)
  · exact install_other eEnv A v 20 (by decide)
  · exact install_other eEnv A v 21 (by decide)
  · exact install_slot eEnv eEnv_inj A v 0
  · exact install_other eEnv A v 23 (by decide)
  · exact install_slot eEnv eEnv_inj A v 3
  · exact install_other eEnv A v 25 (by decide)
  · exact install_other eEnv A v 26 (by decide)
  · exact install_other eEnv A v 27 (by decide)
  · exact install_other eEnv A v 28 (by decide)

theorem dockH_eEnv (H : Fin 29 → ℕ) (v : Fin 4 → ℕ) :
    dockH eEnv H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 2, H 18, H 19, H 20, H 21, v 0, H 23, v 3, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eEnv H v 0 (by decide)
  · exact dockH_other eEnv H v 1 (by decide)
  · exact dockH_slot eEnv eEnv_inj H v 1
  · exact dockH_other eEnv H v 3 (by decide)
  · exact dockH_other eEnv H v 4 (by decide)
  · exact dockH_other eEnv H v 5 (by decide)
  · exact dockH_other eEnv H v 6 (by decide)
  · exact dockH_other eEnv H v 7 (by decide)
  · exact dockH_other eEnv H v 8 (by decide)
  · exact dockH_other eEnv H v 9 (by decide)
  · exact dockH_other eEnv H v 10 (by decide)
  · exact dockH_other eEnv H v 11 (by decide)
  · exact dockH_other eEnv H v 12 (by decide)
  · exact dockH_other eEnv H v 13 (by decide)
  · exact dockH_other eEnv H v 14 (by decide)
  · exact dockH_other eEnv H v 15 (by decide)
  · exact dockH_other eEnv H v 16 (by decide)
  · exact dockH_slot eEnv eEnv_inj H v 2
  · exact dockH_other eEnv H v 18 (by decide)
  · exact dockH_other eEnv H v 19 (by decide)
  · exact dockH_other eEnv H v 20 (by decide)
  · exact dockH_other eEnv H v 21 (by decide)
  · exact dockH_slot eEnv eEnv_inj H v 0
  · exact dockH_other eEnv H v 23 (by decide)
  · exact dockH_slot eEnv eEnv_inj H v 3
  · exact dockH_other eEnv H v 25 (by decide)
  · exact dockH_other eEnv H v 26 (by decide)
  · exact dockH_other eEnv H v 27 (by decide)
  · exact dockH_other eEnv H v 28 (by decide)

theorem eCnt_inj : Function.Injective eCnt := by decide

theorem install_eCnt (A : Fin 29 → List Bool) (v : Fin 1 → List Bool) :
    install eCnt A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 0, A 24, A 25, A 26, A 27, A 28] := by
  funext i
  fin_cases i
  · exact install_other eCnt A v 0 (by decide)
  · exact install_other eCnt A v 1 (by decide)
  · exact install_other eCnt A v 2 (by decide)
  · exact install_other eCnt A v 3 (by decide)
  · exact install_other eCnt A v 4 (by decide)
  · exact install_other eCnt A v 5 (by decide)
  · exact install_other eCnt A v 6 (by decide)
  · exact install_other eCnt A v 7 (by decide)
  · exact install_other eCnt A v 8 (by decide)
  · exact install_other eCnt A v 9 (by decide)
  · exact install_other eCnt A v 10 (by decide)
  · exact install_other eCnt A v 11 (by decide)
  · exact install_other eCnt A v 12 (by decide)
  · exact install_other eCnt A v 13 (by decide)
  · exact install_other eCnt A v 14 (by decide)
  · exact install_other eCnt A v 15 (by decide)
  · exact install_other eCnt A v 16 (by decide)
  · exact install_other eCnt A v 17 (by decide)
  · exact install_other eCnt A v 18 (by decide)
  · exact install_other eCnt A v 19 (by decide)
  · exact install_other eCnt A v 20 (by decide)
  · exact install_other eCnt A v 21 (by decide)
  · exact install_other eCnt A v 22 (by decide)
  · exact install_slot eCnt eCnt_inj A v 0
  · exact install_other eCnt A v 24 (by decide)
  · exact install_other eCnt A v 25 (by decide)
  · exact install_other eCnt A v 26 (by decide)
  · exact install_other eCnt A v 27 (by decide)
  · exact install_other eCnt A v 28 (by decide)

theorem dockH_eCnt (H : Fin 29 → ℕ) (v : Fin 1 → ℕ) :
    dockH eCnt H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, v 0, H 24, H 25, H 26, H 27, H 28] := by
  funext i
  fin_cases i
  · exact dockH_other eCnt H v 0 (by decide)
  · exact dockH_other eCnt H v 1 (by decide)
  · exact dockH_other eCnt H v 2 (by decide)
  · exact dockH_other eCnt H v 3 (by decide)
  · exact dockH_other eCnt H v 4 (by decide)
  · exact dockH_other eCnt H v 5 (by decide)
  · exact dockH_other eCnt H v 6 (by decide)
  · exact dockH_other eCnt H v 7 (by decide)
  · exact dockH_other eCnt H v 8 (by decide)
  · exact dockH_other eCnt H v 9 (by decide)
  · exact dockH_other eCnt H v 10 (by decide)
  · exact dockH_other eCnt H v 11 (by decide)
  · exact dockH_other eCnt H v 12 (by decide)
  · exact dockH_other eCnt H v 13 (by decide)
  · exact dockH_other eCnt H v 14 (by decide)
  · exact dockH_other eCnt H v 15 (by decide)
  · exact dockH_other eCnt H v 16 (by decide)
  · exact dockH_other eCnt H v 17 (by decide)
  · exact dockH_other eCnt H v 18 (by decide)
  · exact dockH_other eCnt H v 19 (by decide)
  · exact dockH_other eCnt H v 20 (by decide)
  · exact dockH_other eCnt H v 21 (by decide)
  · exact dockH_other eCnt H v 22 (by decide)
  · exact dockH_slot eCnt eCnt_inj H v 0
  · exact dockH_other eCnt H v 24 (by decide)
  · exact dockH_other eCnt H v 25 (by decide)
  · exact dockH_other eCnt H v 26 (by decide)
  · exact dockH_other eCnt H v 27 (by decide)
  · exact dockH_other eCnt H v 28 (by decide)

noncomputable def eLoadD := RecoveryFocus.machine eLoad loadM
noncomputable def eGRD := RecoveryFocus.machine eGR moveM
noncomputable def eS1D := RecoveryFocus.machine eS1 copyS
noncomputable def eS2D := RecoveryFocus.machine eS2 copyS
noncomputable def eCoefD := RecoveryFocus.machine eCoef coefM
noncomputable def eLabD := RecoveryFocus.machine eLab (StreamController.machine labelBodyM 0)
noncomputable def eCut0D := RecoveryFocus.machine eCut cut0M
noncomputable def eEvD := RecoveryFocus.machine eEv coefEmitM
noncomputable def eCut1D := RecoveryFocus.machine eCut cut1M
noncomputable def eEnvD := RecoveryFocus.machine eEnv coefEmitM
noncomputable def eCntD := RecoveryFocus.machine eCnt (putM true)

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
