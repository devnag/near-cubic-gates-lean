import Proof.Wire_3_5.CompilerMachineEmitCoefRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- Copy the bit under tape 0's head onto tape 1 under its head (any tape 1). -/
theorem cpbGen (T : List Bool) (h : ℕ) (O : List Bool) (ho : ℕ) :
    Step cpbM 1 ![h, ho] ![T, O] ![h, ho] ![T, writeTapeBit O ho (readTapeBit T h)] := by
  have e := gateStep (1 : Fin 2) (fun sc => sc 0) ![h, ho] ![T, O]
  refine e.congr rfl ?_
  funext i; fin_cases i <;> rfl

def ePut : Fin 1 → Fin 4 := ![1]
def eCp : Fin 2 → Fin 4 := ![0, 1]
def eEm : Fin 3 → Fin 4 := ![2, 1, 3]

theorem ePut_inj : Function.Injective ePut := by decide

theorem install_ePut (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    install ePut A v = ![A 0, v 0, A 2, A 3] := by
  funext i
  fin_cases i
  · exact install_other ePut A v 0 (by decide)
  · exact install_slot ePut ePut_inj A v 0
  · exact install_other ePut A v 2 (by decide)
  · exact install_other ePut A v 3 (by decide)

theorem dockH_ePut (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH ePut H v = ![H 0, v 0, H 2, H 3] := by
  funext i
  fin_cases i
  · exact dockH_other ePut H v 0 (by decide)
  · exact dockH_slot ePut ePut_inj H v 0
  · exact dockH_other ePut H v 2 (by decide)
  · exact dockH_other ePut H v 3 (by decide)

theorem eCp_inj : Function.Injective eCp := by decide

theorem install_eCp (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    install eCp A v = ![v 0, v 1, A 2, A 3] := by
  funext i
  fin_cases i
  · exact install_slot eCp eCp_inj A v 0
  · exact install_slot eCp eCp_inj A v 1
  · exact install_other eCp A v 2 (by decide)
  · exact install_other eCp A v 3 (by decide)

theorem dockH_eCp (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) :
    dockH eCp H v = ![v 0, v 1, H 2, H 3] := by
  funext i
  fin_cases i
  · exact dockH_slot eCp eCp_inj H v 0
  · exact dockH_slot eCp eCp_inj H v 1
  · exact dockH_other eCp H v 2 (by decide)
  · exact dockH_other eCp H v 3 (by decide)

theorem eEm_inj : Function.Injective eEm := by decide

theorem install_eEm (A : Fin 4 → List Bool) (v : Fin 3 → List Bool) :
    install eEm A v = ![A 0, v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact install_other eEm A v 0 (by decide)
  · exact install_slot eEm eEm_inj A v 1
  · exact install_slot eEm eEm_inj A v 0
  · exact install_slot eEm eEm_inj A v 2

theorem dockH_eEm (H : Fin 4 → ℕ) (v : Fin 3 → ℕ) :
    dockH eEm H v = ![H 0, v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other eEm H v 0 (by decide)
  · exact dockH_slot eEm eEm_inj H v 1
  · exact dockH_slot eEm eEm_inj H v 0
  · exact dockH_slot eEm eEm_inj H v 2

noncomputable def ePutD := RecoveryFocus.machine ePut (putM true)
noncomputable def eCpD := RecoveryFocus.machine eCp cpbM
noncomputable def eMvD := RecoveryFocus.machine ePut moveM
noncomputable def eEmD := RecoveryFocus.machine eEm emitM
/-- **Write a coefficient**: the marker, the sign bit, the magnitude register. -/
noncomputable def coefEmitM := Composition.machine ePutD (Composition.machine eCpD (Composition.machine eMvD eEmD))

def coefEmitCost (W : ℕ) : ℕ := 1 + 1 + (1 + 1 + (1 + 1 + (2 * (2 * W + 1) + 2)))

/-- **The coefficient's code at the output cursor**: `frame (s :: binary W m)` after `out`. -/
theorem coefEmit_step (W m : ℕ) (s : Bool) (tRC out BW : List Bool) (cap : ℕ) (hcap : 2 * W + 1 ≤ cap) :
    Step coefEmitM (coefEmitCost W) ![0, out.length, 0, 0]
      ![[s], overlay out BW, frame (binary W m) ++ tRC, List.replicate cap false]
      ![0, (out ++ frame (s :: binary W m)).length, 0, 0]
      ![[s], overlay (out ++ frame (s :: binary W m)) BW, frame (binary W m) ++ tRC, List.replicate cap false] := by
  set RC := frame (binary W m) ++ tRC
  have p := dockRun (putStep true (overlay out BW) out.length) ePut ePut_inj ![0, out.length, 0, 0]
    ![[s], overlay out BW, RC, List.replicate cap false] (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_ePut, dockH_ePut, overlay_write] at p
  have p' : Step ePutD 1 ![0, out.length, 0, 0] ![[s], overlay out BW, RC, List.replicate cap false]
      ![0, (out ++ [true]).length, 0, 0] ![[s], overlay (out ++ [true]) BW, RC, List.replicate cap false] :=
    p.congr (by funext i; fin_cases i <;> simp) (by funext i; fin_cases i <;> rfl)
  have c := dockRun (cpbGen [s] 0 (overlay (out ++ [true]) BW) (out ++ [true]).length) eCp eCp_inj
    ![0, (out ++ [true]).length, 0, 0] ![[s], overlay (out ++ [true]) BW, RC, List.replicate cap false]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_eCp, dockH_eCp, show readTapeBit [s] 0 = s from rfl, overlay_write] at c
  have c' : Step eCpD 1 ![0, (out ++ [true]).length, 0, 0] ![[s], overlay (out ++ [true]) BW, RC, List.replicate cap false]
      ![0, (out ++ [true]).length, 0, 0] ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false] :=
    c.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have mv := dockRun (moveStep (overlay (out ++ [true] ++ [s]) BW) (out ++ [true]).length) ePut ePut_inj
    ![0, (out ++ [true]).length, 0, 0] ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_ePut, dockH_ePut] at mv
  have mv' : Step eMvD 1 ![0, (out ++ [true]).length, 0, 0]
      ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false]
      ![0, (out ++ [true] ++ [s]).length, 0, 0] ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false] :=
    mv.congr (by funext i; fin_cases i <;> simp) (by funext i; fin_cases i <;> rfl)
  have em := dockRun (emitT (binary W m) tRC (out ++ [true] ++ [s]) BW cap (by simpa using hcap)) eEm eEm_inj
    ![0, (out ++ [true] ++ [s]).length, 0, 0] ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_eEm, dockH_eEm, binary_length] at em
  have hw : out ++ [true] ++ [s] ++ frame (binary W m) = out ++ frame (s :: binary W m) := by simp [frame]
  rw [hw] at em
  have em' : Step eEmD (2 * (2 * W + 1) + 2) ![0, (out ++ [true] ++ [s]).length, 0, 0]
      ![[s], overlay (out ++ [true] ++ [s]) BW, RC, List.replicate cap false]
      ![0, (out ++ frame (s :: binary W m)).length, 0, 0]
      ![[s], overlay (out ++ frame (s :: binary W m)) BW, RC, List.replicate cap false] := by
    refine em.congr ?_ (by funext i; fin_cases i <;> rfl)
    funext i; fin_cases i <;> simp [frame]
    all_goals omega
  exact p'.seq (c'.seq (mv'.seq em'))

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
