import Proof.Wire_3_5.CompilerMachineEmitThermo
import Proof.Wire_3_5.CompilerMachinePolyTermRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

theorem value_bits : ∀ n : ℕ, value (Nat.bits n) = n
  | 0 => by simp [value]
  | n + 1 => by
    have ih := value_bits ((n + 1) / 2)
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with hm | hm
    · have hx2 : 2 * ((n + 1) / 2) = n + 1 := by omega
      have hne : (n + 1) / 2 ≠ 0 := by omega
      have hb := Nat.bit0_bits ((n + 1) / 2) hne
      rw [hx2] at hb
      rw [hb]
      simp only [value, Bool.toNat_false, ih]
      omega
    · have hx2 : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
      have hb := Nat.bit1_bits ((n + 1) / 2)
      rw [hx2] at hb
      rw [hb]
      simp only [value, Bool.toNat_true, ih]
      omega

theorem bits_ne_nil (n : ℕ) (hn : n ≠ 0) : Nat.bits n ≠ [] := by
  intro h
  have := value_bits n
  rw [h] at this
  simp [value] at this
  omega

theorem value_zeros_append (z : ℕ) (B : List Bool) : value (List.replicate z false ++ B) = 2 ^ z * value B := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [value, Bool.toNat_false, ih, pow_succ]
    ring

/-- The magnitude register after the copy and the restored marker. -/
theorem rc_final (W z : ℕ) (n : ℕ) (Y : List Bool) (h : z + (Nat.bits n).length < W) :
    writeTapeBit (overlay (fpre (List.replicate z false) ++ frame (Nat.bits n))
        (overlay (frame (List.replicate W false)) Y)) (2 * z + 2 * (Nat.bits n).length) true =
      overlay (frame (binary W (n * 2 ^ z))) Y := by
  have hf : fpre (List.replicate z false) ++ frame (Nat.bits n) = frame (List.replicate z false ++ Nat.bits n) :=
    (frame_append' _ _).symm
  have hl : (List.replicate z false ++ Nat.bits n).length = z + (Nat.bits n).length := by simp
  have hw := pad_write (List.replicate z false ++ Nat.bits n) Y W (by rw [hl]; exact h)
  rw [hl, value_zeros_append, value_bits] at hw
  rw [hf, show 2 * z + 2 * (Nat.bits n).length = 2 * (z + (Nat.bits n).length) by ring, hw, Nat.mul_comm]

/-- The sign of `v`: `c ≠ 0 ∧ (c < 0 ⊕ par ⊕ k odd)` from the cells `NZ, SC, RPAR, PK` (tapes 0-3), into tape 4. -/
def svM : Machine 5 2 := gateM 5 4 fun sc => sc 0 && (sc 1 ^^ sc 2 ^^ sc 3)
/-- The sign of `−v`. -/
def snvM : Machine 5 2 := gateM 5 4 fun sc => sc 0 && !(sc 1 ^^ sc 2 ^^ sc 3)

theorem svStep (nz sc par pk o : Bool) :
    Step svM 1 ![0, 0, 0, 0, 0] ![[nz], [sc], [par], [pk], [o]] ![0, 0, 0, 0, 0]
      ![[nz], [sc], [par], [pk], [nz && (sc ^^ par ^^ pk)]] := by
  have e := gateStep (4 : Fin 5) (fun sc => sc 0 && (sc 1 ^^ sc 2 ^^ sc 3)) ![0, 0, 0, 0, 0] ![[nz], [sc], [par], [pk], [o]]
  refine e.congr rfl ?_
  funext i; fin_cases i <;> rfl

theorem snvStep (nz sc par pk o : Bool) :
    Step snvM 1 ![0, 0, 0, 0, 0] ![[nz], [sc], [par], [pk], [o]] ![0, 0, 0, 0, 0]
      ![[nz], [sc], [par], [pk], [nz && !(sc ^^ par ^^ pk)]] := by
  have e := gateStep (4 : Fin 5) (fun sc => sc 0 && !(sc 1 ^^ sc 2 ^^ sc 3)) ![0, 0, 0, 0, 0]
    ![[nz], [sc], [par], [pk], [o]]
  refine e.congr rfl ?_
  funext i; fin_cases i <;> rfl

def dZ : Fin 3 → Fin 12 := ![5, 4, 11]
def dPK : Fin 1 → Fin 12 := ![6]
def dRE : Fin 1 → Fin 12 := ![0]
def dRCB : Fin 1 → Fin 12 := ![2]
def dSC : Fin 2 → Fin 12 := ![2, 7]
def dNZ : Fin 2 → Fin 12 := ![2, 8]
def dRCL : Fin 1 → Fin 12 := ![4]
def dCp : Fin 2 → Fin 12 := ![2, 4]
def dPut : Fin 1 → Fin 12 := ![4]
def dSV : Fin 5 → Fin 12 := ![8, 7, 3, 6, 9]
def dSNV : Fin 5 → Fin 12 := ![8, 7, 3, 6, 10]

theorem dZ_inj : Function.Injective dZ := by decide

theorem install_dZ (A : Fin 12 → List Bool) (v : Fin 3 → List Bool) :
    install dZ A v = ![A 0, A 1, A 2, A 3, v 1, v 0, A 6, A 7, A 8, A 9, A 10, v 2] := by
  funext i
  fin_cases i
  · exact install_other dZ A v 0 (by decide)
  · exact install_other dZ A v 1 (by decide)
  · exact install_other dZ A v 2 (by decide)
  · exact install_other dZ A v 3 (by decide)
  · exact install_slot dZ dZ_inj A v 1
  · exact install_slot dZ dZ_inj A v 0
  · exact install_other dZ A v 6 (by decide)
  · exact install_other dZ A v 7 (by decide)
  · exact install_other dZ A v 8 (by decide)
  · exact install_other dZ A v 9 (by decide)
  · exact install_other dZ A v 10 (by decide)
  · exact install_slot dZ dZ_inj A v 2

theorem dockH_dZ (H : Fin 12 → ℕ) (v : Fin 3 → ℕ) :
    dockH dZ H v = ![H 0, H 1, H 2, H 3, v 1, v 0, H 6, H 7, H 8, H 9, H 10, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other dZ H v 0 (by decide)
  · exact dockH_other dZ H v 1 (by decide)
  · exact dockH_other dZ H v 2 (by decide)
  · exact dockH_other dZ H v 3 (by decide)
  · exact dockH_slot dZ dZ_inj H v 1
  · exact dockH_slot dZ dZ_inj H v 0
  · exact dockH_other dZ H v 6 (by decide)
  · exact dockH_other dZ H v 7 (by decide)
  · exact dockH_other dZ H v 8 (by decide)
  · exact dockH_other dZ H v 9 (by decide)
  · exact dockH_other dZ H v 10 (by decide)
  · exact dockH_slot dZ dZ_inj H v 2

theorem dPK_inj : Function.Injective dPK := by decide

theorem install_dPK (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install dPK A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dPK A v 0 (by decide)
  · exact install_other dPK A v 1 (by decide)
  · exact install_other dPK A v 2 (by decide)
  · exact install_other dPK A v 3 (by decide)
  · exact install_other dPK A v 4 (by decide)
  · exact install_other dPK A v 5 (by decide)
  · exact install_slot dPK dPK_inj A v 0
  · exact install_other dPK A v 7 (by decide)
  · exact install_other dPK A v 8 (by decide)
  · exact install_other dPK A v 9 (by decide)
  · exact install_other dPK A v 10 (by decide)
  · exact install_other dPK A v 11 (by decide)

theorem dockH_dPK (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH dPK H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dPK H v 0 (by decide)
  · exact dockH_other dPK H v 1 (by decide)
  · exact dockH_other dPK H v 2 (by decide)
  · exact dockH_other dPK H v 3 (by decide)
  · exact dockH_other dPK H v 4 (by decide)
  · exact dockH_other dPK H v 5 (by decide)
  · exact dockH_slot dPK dPK_inj H v 0
  · exact dockH_other dPK H v 7 (by decide)
  · exact dockH_other dPK H v 8 (by decide)
  · exact dockH_other dPK H v 9 (by decide)
  · exact dockH_other dPK H v 10 (by decide)
  · exact dockH_other dPK H v 11 (by decide)

theorem dRE_inj : Function.Injective dRE := by decide

theorem install_dRE (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install dRE A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_slot dRE dRE_inj A v 0
  · exact install_other dRE A v 1 (by decide)
  · exact install_other dRE A v 2 (by decide)
  · exact install_other dRE A v 3 (by decide)
  · exact install_other dRE A v 4 (by decide)
  · exact install_other dRE A v 5 (by decide)
  · exact install_other dRE A v 6 (by decide)
  · exact install_other dRE A v 7 (by decide)
  · exact install_other dRE A v 8 (by decide)
  · exact install_other dRE A v 9 (by decide)
  · exact install_other dRE A v 10 (by decide)
  · exact install_other dRE A v 11 (by decide)

theorem dockH_dRE (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH dRE H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_slot dRE dRE_inj H v 0
  · exact dockH_other dRE H v 1 (by decide)
  · exact dockH_other dRE H v 2 (by decide)
  · exact dockH_other dRE H v 3 (by decide)
  · exact dockH_other dRE H v 4 (by decide)
  · exact dockH_other dRE H v 5 (by decide)
  · exact dockH_other dRE H v 6 (by decide)
  · exact dockH_other dRE H v 7 (by decide)
  · exact dockH_other dRE H v 8 (by decide)
  · exact dockH_other dRE H v 9 (by decide)
  · exact dockH_other dRE H v 10 (by decide)
  · exact dockH_other dRE H v 11 (by decide)

theorem dRCB_inj : Function.Injective dRCB := by decide

theorem install_dRCB (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install dRCB A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dRCB A v 0 (by decide)
  · exact install_other dRCB A v 1 (by decide)
  · exact install_slot dRCB dRCB_inj A v 0
  · exact install_other dRCB A v 3 (by decide)
  · exact install_other dRCB A v 4 (by decide)
  · exact install_other dRCB A v 5 (by decide)
  · exact install_other dRCB A v 6 (by decide)
  · exact install_other dRCB A v 7 (by decide)
  · exact install_other dRCB A v 8 (by decide)
  · exact install_other dRCB A v 9 (by decide)
  · exact install_other dRCB A v 10 (by decide)
  · exact install_other dRCB A v 11 (by decide)

theorem dockH_dRCB (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH dRCB H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dRCB H v 0 (by decide)
  · exact dockH_other dRCB H v 1 (by decide)
  · exact dockH_slot dRCB dRCB_inj H v 0
  · exact dockH_other dRCB H v 3 (by decide)
  · exact dockH_other dRCB H v 4 (by decide)
  · exact dockH_other dRCB H v 5 (by decide)
  · exact dockH_other dRCB H v 6 (by decide)
  · exact dockH_other dRCB H v 7 (by decide)
  · exact dockH_other dRCB H v 8 (by decide)
  · exact dockH_other dRCB H v 9 (by decide)
  · exact dockH_other dRCB H v 10 (by decide)
  · exact dockH_other dRCB H v 11 (by decide)

theorem dSC_inj : Function.Injective dSC := by decide

theorem install_dSC (A : Fin 12 → List Bool) (v : Fin 2 → List Bool) :
    install dSC A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, v 1, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dSC A v 0 (by decide)
  · exact install_other dSC A v 1 (by decide)
  · exact install_slot dSC dSC_inj A v 0
  · exact install_other dSC A v 3 (by decide)
  · exact install_other dSC A v 4 (by decide)
  · exact install_other dSC A v 5 (by decide)
  · exact install_other dSC A v 6 (by decide)
  · exact install_slot dSC dSC_inj A v 1
  · exact install_other dSC A v 8 (by decide)
  · exact install_other dSC A v 9 (by decide)
  · exact install_other dSC A v 10 (by decide)
  · exact install_other dSC A v 11 (by decide)

theorem dockH_dSC (H : Fin 12 → ℕ) (v : Fin 2 → ℕ) :
    dockH dSC H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, v 1, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dSC H v 0 (by decide)
  · exact dockH_other dSC H v 1 (by decide)
  · exact dockH_slot dSC dSC_inj H v 0
  · exact dockH_other dSC H v 3 (by decide)
  · exact dockH_other dSC H v 4 (by decide)
  · exact dockH_other dSC H v 5 (by decide)
  · exact dockH_other dSC H v 6 (by decide)
  · exact dockH_slot dSC dSC_inj H v 1
  · exact dockH_other dSC H v 8 (by decide)
  · exact dockH_other dSC H v 9 (by decide)
  · exact dockH_other dSC H v 10 (by decide)
  · exact dockH_other dSC H v 11 (by decide)

theorem dNZ_inj : Function.Injective dNZ := by decide

theorem install_dNZ (A : Fin 12 → List Bool) (v : Fin 2 → List Bool) :
    install dNZ A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, v 1, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dNZ A v 0 (by decide)
  · exact install_other dNZ A v 1 (by decide)
  · exact install_slot dNZ dNZ_inj A v 0
  · exact install_other dNZ A v 3 (by decide)
  · exact install_other dNZ A v 4 (by decide)
  · exact install_other dNZ A v 5 (by decide)
  · exact install_other dNZ A v 6 (by decide)
  · exact install_other dNZ A v 7 (by decide)
  · exact install_slot dNZ dNZ_inj A v 1
  · exact install_other dNZ A v 9 (by decide)
  · exact install_other dNZ A v 10 (by decide)
  · exact install_other dNZ A v 11 (by decide)

theorem dockH_dNZ (H : Fin 12 → ℕ) (v : Fin 2 → ℕ) :
    dockH dNZ H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, v 1, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dNZ H v 0 (by decide)
  · exact dockH_other dNZ H v 1 (by decide)
  · exact dockH_slot dNZ dNZ_inj H v 0
  · exact dockH_other dNZ H v 3 (by decide)
  · exact dockH_other dNZ H v 4 (by decide)
  · exact dockH_other dNZ H v 5 (by decide)
  · exact dockH_other dNZ H v 6 (by decide)
  · exact dockH_other dNZ H v 7 (by decide)
  · exact dockH_slot dNZ dNZ_inj H v 1
  · exact dockH_other dNZ H v 9 (by decide)
  · exact dockH_other dNZ H v 10 (by decide)
  · exact dockH_other dNZ H v 11 (by decide)

theorem dRCL_inj : Function.Injective dRCL := by decide

theorem install_dRCL (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install dRCL A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dRCL A v 0 (by decide)
  · exact install_other dRCL A v 1 (by decide)
  · exact install_other dRCL A v 2 (by decide)
  · exact install_other dRCL A v 3 (by decide)
  · exact install_slot dRCL dRCL_inj A v 0
  · exact install_other dRCL A v 5 (by decide)
  · exact install_other dRCL A v 6 (by decide)
  · exact install_other dRCL A v 7 (by decide)
  · exact install_other dRCL A v 8 (by decide)
  · exact install_other dRCL A v 9 (by decide)
  · exact install_other dRCL A v 10 (by decide)
  · exact install_other dRCL A v 11 (by decide)

theorem dockH_dRCL (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH dRCL H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dRCL H v 0 (by decide)
  · exact dockH_other dRCL H v 1 (by decide)
  · exact dockH_other dRCL H v 2 (by decide)
  · exact dockH_other dRCL H v 3 (by decide)
  · exact dockH_slot dRCL dRCL_inj H v 0
  · exact dockH_other dRCL H v 5 (by decide)
  · exact dockH_other dRCL H v 6 (by decide)
  · exact dockH_other dRCL H v 7 (by decide)
  · exact dockH_other dRCL H v 8 (by decide)
  · exact dockH_other dRCL H v 9 (by decide)
  · exact dockH_other dRCL H v 10 (by decide)
  · exact dockH_other dRCL H v 11 (by decide)

theorem dCp_inj : Function.Injective dCp := by decide

theorem install_dCp (A : Fin 12 → List Bool) (v : Fin 2 → List Bool) :
    install dCp A v = ![A 0, A 1, v 0, A 3, v 1, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dCp A v 0 (by decide)
  · exact install_other dCp A v 1 (by decide)
  · exact install_slot dCp dCp_inj A v 0
  · exact install_other dCp A v 3 (by decide)
  · exact install_slot dCp dCp_inj A v 1
  · exact install_other dCp A v 5 (by decide)
  · exact install_other dCp A v 6 (by decide)
  · exact install_other dCp A v 7 (by decide)
  · exact install_other dCp A v 8 (by decide)
  · exact install_other dCp A v 9 (by decide)
  · exact install_other dCp A v 10 (by decide)
  · exact install_other dCp A v 11 (by decide)

theorem dockH_dCp (H : Fin 12 → ℕ) (v : Fin 2 → ℕ) :
    dockH dCp H v = ![H 0, H 1, v 0, H 3, v 1, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dCp H v 0 (by decide)
  · exact dockH_other dCp H v 1 (by decide)
  · exact dockH_slot dCp dCp_inj H v 0
  · exact dockH_other dCp H v 3 (by decide)
  · exact dockH_slot dCp dCp_inj H v 1
  · exact dockH_other dCp H v 5 (by decide)
  · exact dockH_other dCp H v 6 (by decide)
  · exact dockH_other dCp H v 7 (by decide)
  · exact dockH_other dCp H v 8 (by decide)
  · exact dockH_other dCp H v 9 (by decide)
  · exact dockH_other dCp H v 10 (by decide)
  · exact dockH_other dCp H v 11 (by decide)

theorem dPut_inj : Function.Injective dPut := by decide

theorem install_dPut (A : Fin 12 → List Bool) (v : Fin 1 → List Bool) :
    install dPut A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dPut A v 0 (by decide)
  · exact install_other dPut A v 1 (by decide)
  · exact install_other dPut A v 2 (by decide)
  · exact install_other dPut A v 3 (by decide)
  · exact install_slot dPut dPut_inj A v 0
  · exact install_other dPut A v 5 (by decide)
  · exact install_other dPut A v 6 (by decide)
  · exact install_other dPut A v 7 (by decide)
  · exact install_other dPut A v 8 (by decide)
  · exact install_other dPut A v 9 (by decide)
  · exact install_other dPut A v 10 (by decide)
  · exact install_other dPut A v 11 (by decide)

theorem dockH_dPut (H : Fin 12 → ℕ) (v : Fin 1 → ℕ) :
    dockH dPut H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dPut H v 0 (by decide)
  · exact dockH_other dPut H v 1 (by decide)
  · exact dockH_other dPut H v 2 (by decide)
  · exact dockH_other dPut H v 3 (by decide)
  · exact dockH_slot dPut dPut_inj H v 0
  · exact dockH_other dPut H v 5 (by decide)
  · exact dockH_other dPut H v 6 (by decide)
  · exact dockH_other dPut H v 7 (by decide)
  · exact dockH_other dPut H v 8 (by decide)
  · exact dockH_other dPut H v 9 (by decide)
  · exact dockH_other dPut H v 10 (by decide)
  · exact dockH_other dPut H v 11 (by decide)

theorem dSV_inj : Function.Injective dSV := by decide

theorem install_dSV (A : Fin 12 → List Bool) (v : Fin 5 → List Bool) :
    install dSV A v = ![A 0, A 1, A 2, v 2, A 4, A 5, v 3, v 1, v 0, v 4, A 10, A 11] := by
  funext i
  fin_cases i
  · exact install_other dSV A v 0 (by decide)
  · exact install_other dSV A v 1 (by decide)
  · exact install_other dSV A v 2 (by decide)
  · exact install_slot dSV dSV_inj A v 2
  · exact install_other dSV A v 4 (by decide)
  · exact install_other dSV A v 5 (by decide)
  · exact install_slot dSV dSV_inj A v 3
  · exact install_slot dSV dSV_inj A v 1
  · exact install_slot dSV dSV_inj A v 0
  · exact install_slot dSV dSV_inj A v 4
  · exact install_other dSV A v 10 (by decide)
  · exact install_other dSV A v 11 (by decide)

theorem dockH_dSV (H : Fin 12 → ℕ) (v : Fin 5 → ℕ) :
    dockH dSV H v = ![H 0, H 1, H 2, v 2, H 4, H 5, v 3, v 1, v 0, v 4, H 10, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dSV H v 0 (by decide)
  · exact dockH_other dSV H v 1 (by decide)
  · exact dockH_other dSV H v 2 (by decide)
  · exact dockH_slot dSV dSV_inj H v 2
  · exact dockH_other dSV H v 4 (by decide)
  · exact dockH_other dSV H v 5 (by decide)
  · exact dockH_slot dSV dSV_inj H v 3
  · exact dockH_slot dSV dSV_inj H v 1
  · exact dockH_slot dSV dSV_inj H v 0
  · exact dockH_slot dSV dSV_inj H v 4
  · exact dockH_other dSV H v 10 (by decide)
  · exact dockH_other dSV H v 11 (by decide)

theorem dSNV_inj : Function.Injective dSNV := by decide

theorem install_dSNV (A : Fin 12 → List Bool) (v : Fin 5 → List Bool) :
    install dSNV A v = ![A 0, A 1, A 2, v 2, A 4, A 5, v 3, v 1, v 0, A 9, v 4, A 11] := by
  funext i
  fin_cases i
  · exact install_other dSNV A v 0 (by decide)
  · exact install_other dSNV A v 1 (by decide)
  · exact install_other dSNV A v 2 (by decide)
  · exact install_slot dSNV dSNV_inj A v 2
  · exact install_other dSNV A v 4 (by decide)
  · exact install_other dSNV A v 5 (by decide)
  · exact install_slot dSNV dSNV_inj A v 3
  · exact install_slot dSNV dSNV_inj A v 1
  · exact install_slot dSNV dSNV_inj A v 0
  · exact install_other dSNV A v 9 (by decide)
  · exact install_slot dSNV dSNV_inj A v 4
  · exact install_other dSNV A v 11 (by decide)

theorem dockH_dSNV (H : Fin 12 → ℕ) (v : Fin 5 → ℕ) :
    dockH dSNV H v = ![H 0, H 1, H 2, v 2, H 4, H 5, v 3, v 1, v 0, H 9, v 4, H 11] := by
  funext i
  fin_cases i
  · exact dockH_other dSNV H v 0 (by decide)
  · exact dockH_other dSNV H v 1 (by decide)
  · exact dockH_other dSNV H v 2 (by decide)
  · exact dockH_slot dSNV dSNV_inj H v 2
  · exact dockH_other dSNV H v 4 (by decide)
  · exact dockH_other dSNV H v 5 (by decide)
  · exact dockH_slot dSNV dSNV_inj H v 3
  · exact dockH_slot dSNV dSNV_inj H v 1
  · exact dockH_slot dSNV dSNV_inj H v 0
  · exact dockH_other dSNV H v 9 (by decide)
  · exact dockH_slot dSNV dSNV_inj H v 4
  · exact dockH_other dSNV H v 11 (by decide)

noncomputable def dZD := RecoveryFocus.machine dZ regCopyM
noncomputable def dPKD := RecoveryFocus.machine dPK (cellM false)
noncomputable def dRED := RecoveryFocus.machine dRE moveM
noncomputable def dRCBD := RecoveryFocus.machine dRCB moveM
noncomputable def dSCD := RecoveryFocus.machine dSC cpbM
noncomputable def dNZD := RecoveryFocus.machine dNZ cpbM
noncomputable def dRCLD := RecoveryFocus.machine dRCL moveLM
noncomputable def dCpD := RecoveryFocus.machine dCp CopyO.machine
noncomputable def dPutD := RecoveryFocus.machine dPut (putM true)
noncomputable def dSVD := RecoveryFocus.machine dSV svM
noncomputable def dSNVD := RecoveryFocus.machine dSNV snvM
/-- The shifted copy of `|c|` into the magnitude register (the group's coefficient is not zero). -/
noncomputable def shiftCopyM :=
  Composition.machine dRCLD (Composition.machine dRCLD (Composition.machine dCpD (Composition.machine dRCLD dPutD)))
/-- **The coefficient phase** before the reset. -/
noncomputable def coefRaw :=
  Composition.machine dZD (Composition.machine dPKD (Composition.machine (StreamController.machine thermoBodyM 1)
    (Composition.machine dRED (Composition.machine dRED (Composition.machine dRCBD (Composition.machine dSCD
      (Composition.machine dRCBD (Composition.machine dNZD (Composition.machine (branchM 8 shiftCopyM (idle 12))
        (Composition.machine dSVD dSNVD))))))))))
/-- The heads the phase returns to cell `0`: the driver, the group's coefficient word, the magnitude register. -/
def coefSel : Fin 12 → Bool := ![false, true, true, false, true, false, false, false, false, false, false, false]
/-- **The coefficient phase**, the driver, coefficient word and magnitude register heads reset. -/
noncomputable def coefM := MaskedReset.machine coefRaw coefSel

/-- The coefficient layout's heads with the group's coefficient word cursor. -/
def cfH (re cq rcb rc : ℕ) : Fin 12 → ℕ := ![re, cq, rcb, 0, rc, 0, 0, 0, 0, 0, 0, 0]

def shiftCost (L : ℕ) : ℕ := 1 + 1 + (1 + 1 + ((2 * L + 1) + 1 + (1 + 1 + 1)))
def coefRawCost (Q W L : ℕ) : ℕ :=
  (2 * (2 * W + 1) + 2) + 1 + (1 + 1 + ((Q * (thermoCost + 2) + 1) + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 +
    (1 + 1 + (1 + 1 + ((shiftCost L + 2) + 1 + (1 + 1 + 1))))))))))

theorem read_cbits1 (c : ℤ) (t : List Bool) : readTapeBit (frame (cbits c) ++ t) 1 = decide (c < 0) := by
  simp [cbits, frame, readTapeBit]

theorem read_cbits2 (c : ℤ) (t : List Bool) : readTapeBit (frame (cbits c) ++ t) 2 = decide (c ≠ 0) := by
  by_cases hc : c = 0
  · subst hc; simp [cbits, frame, readTapeBit, Nat.zero_bits]
  · obtain ⟨b, bs, hb⟩ : ∃ b bs, Nat.bits c.natAbs = b :: bs := by
      cases h : Nat.bits c.natAbs with
      | nil => exact absurd h (bits_ne_nil _ (by omega))
      | cons b bs => exact ⟨b, bs, rfl⟩
    simp [cbits, frame, readTapeBit, hb, hc]

theorem template_prefix (W z : ℕ) (hz : z ≤ W) (Y : List Bool) :
    overlay (fpre (List.replicate z false)) (overlay (frame (List.replicate W false)) Y) =
      overlay (frame (List.replicate W false)) Y := by
  have e : List.replicate W false = List.replicate z false ++ List.replicate (W - z) false := by
    rw [← List.replicate_add]; congr 1; omega
  have hX : overlay (frame (List.replicate W false)) Y =
      fpre (List.replicate z false) ++ (frame (List.replicate (W - z) false) ++ Y.drop (2 * W + 1)) := by
    unfold overlay
    rw [show (frame (List.replicate W false)).length = 2 * W + 1 by simp, e, frame_append', List.append_assoc]
  rw [hX, show fpre (List.replicate z false) ++ (frame (List.replicate (W - z) false) ++ Y.drop (2 * W + 1)) =
    fpre (List.replicate z false) ++ (frame (List.replicate (W - z) false) ++ Y.drop (2 * W + 1)) from rfl]
  unfold overlay
  rw [List.drop_append_length]

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
