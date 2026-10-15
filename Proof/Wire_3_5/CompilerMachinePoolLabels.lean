import Proof.Wire_3_5.CompilerMachinePoolUcopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def lbA : Fin 1 → Fin 3 := ![1]
def lbCp : Fin 3 → Fin 4 := ![1, 2, 3]
def lbMv : Fin 1 → Fin 4 := ![0]
def lbPut : Fin 1 → Fin 4 := ![2]
def lbGMv : Fin 1 → Fin 7 := ![0]
def lbLoad : Fin 3 → Fin 7 := ![0, 1, 6]
def lbBase : Fin 3 → Fin 7 := ![3, 2, 5]
def lbDg : Fin 3 → Fin 7 := ![4, 2, 5]
def lbGi : Fin 3 → Fin 7 := ![1, 2, 5]
def lbOPut : Fin 1 → Fin 7 := ![2]
def lbDPut : Fin 1 → Fin 2 := ![1]
def lgP1 : Fin 4 → Fin 11 := ![0, 2, 7, 8]
def lgP2 : Fin 5 → Fin 11 := ![2, 1, 3, 7, 9]
def lgP3 : Fin 7 → Fin 11 := ![4, 5, 6, 3, 1, 7, 10]
def lgPut : Fin 1 → Fin 11 := ![6]

theorem lbA_inj : Function.Injective lbA := by decide

theorem install_lbA (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install lbA A v = ![A 0, v 0, A 2] := by
  funext i
  fin_cases i
  · exact install_other lbA A v 0 (by decide)
  · exact install_slot lbA lbA_inj A v 0
  · exact install_other lbA A v 2 (by decide)

theorem dockH_lbA (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbA H v = ![H 0, v 0, H 2] := by
  funext i
  fin_cases i
  · exact dockH_other lbA H v 0 (by decide)
  · exact dockH_slot lbA lbA_inj H v 0
  · exact dockH_other lbA H v 2 (by decide)

theorem lbCp_inj : Function.Injective lbCp := by decide

theorem install_lbCp (A : Fin 4 → List Bool) (v : Fin 3 → List Bool) :
    install lbCp A v = ![A 0, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other lbCp A v 0 (by decide)
  · exact install_slot lbCp lbCp_inj A v 0
  · exact install_slot lbCp lbCp_inj A v 1
  · exact install_slot lbCp lbCp_inj A v 2

theorem dockH_lbCp (H : Fin 4 → ℕ) (v : Fin 3 → ℕ) :
    dockH lbCp H v = ![H 0, v 0, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other lbCp H v 0 (by decide)
  · exact dockH_slot lbCp lbCp_inj H v 0
  · exact dockH_slot lbCp lbCp_inj H v 1
  · exact dockH_slot lbCp lbCp_inj H v 2

theorem lbMv_inj : Function.Injective lbMv := by decide

theorem install_lbMv (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    install lbMv A v = ![v 0, A 1, A 2, A 3] := by
  funext i
  fin_cases i
  · exact install_slot lbMv lbMv_inj A v 0
  · exact install_other lbMv A v 1 (by decide)
  · exact install_other lbMv A v 2 (by decide)
  · exact install_other lbMv A v 3 (by decide)

theorem dockH_lbMv (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbMv H v = ![v 0, H 1, H 2, H 3] := by
  funext i
  fin_cases i
  · exact dockH_slot lbMv lbMv_inj H v 0
  · exact dockH_other lbMv H v 1 (by decide)
  · exact dockH_other lbMv H v 2 (by decide)
  · exact dockH_other lbMv H v 3 (by decide)

theorem lbPut_inj : Function.Injective lbPut := by decide

theorem install_lbPut (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    install lbPut A v = ![A 0, A 1, v 0, A 3] := by
  funext i
  fin_cases i
  · exact install_other lbPut A v 0 (by decide)
  · exact install_other lbPut A v 1 (by decide)
  · exact install_slot lbPut lbPut_inj A v 0
  · exact install_other lbPut A v 3 (by decide)

theorem dockH_lbPut (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbPut H v = ![H 0, H 1, v 0, H 3] := by
  funext i
  fin_cases i
  · exact dockH_other lbPut H v 0 (by decide)
  · exact dockH_other lbPut H v 1 (by decide)
  · exact dockH_slot lbPut lbPut_inj H v 0
  · exact dockH_other lbPut H v 3 (by decide)

theorem lbGMv_inj : Function.Injective lbGMv := by decide

theorem install_lbGMv (A : Fin 7 → List Bool) (v : Fin 1 → List Bool) :
    install lbGMv A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6] := by
  funext i
  fin_cases i
  · exact install_slot lbGMv lbGMv_inj A v 0
  · exact install_other lbGMv A v 1 (by decide)
  · exact install_other lbGMv A v 2 (by decide)
  · exact install_other lbGMv A v 3 (by decide)
  · exact install_other lbGMv A v 4 (by decide)
  · exact install_other lbGMv A v 5 (by decide)
  · exact install_other lbGMv A v 6 (by decide)

theorem dockH_lbGMv (H : Fin 7 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbGMv H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6] := by
  funext i
  fin_cases i
  · exact dockH_slot lbGMv lbGMv_inj H v 0
  · exact dockH_other lbGMv H v 1 (by decide)
  · exact dockH_other lbGMv H v 2 (by decide)
  · exact dockH_other lbGMv H v 3 (by decide)
  · exact dockH_other lbGMv H v 4 (by decide)
  · exact dockH_other lbGMv H v 5 (by decide)
  · exact dockH_other lbGMv H v 6 (by decide)

theorem lbLoad_inj : Function.Injective lbLoad := by decide

theorem install_lbLoad (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install lbLoad A v = ![v 0, v 1, A 2, A 3, A 4, A 5, v 2] := by
  funext i
  fin_cases i
  · exact install_slot lbLoad lbLoad_inj A v 0
  · exact install_slot lbLoad lbLoad_inj A v 1
  · exact install_other lbLoad A v 2 (by decide)
  · exact install_other lbLoad A v 3 (by decide)
  · exact install_other lbLoad A v 4 (by decide)
  · exact install_other lbLoad A v 5 (by decide)
  · exact install_slot lbLoad lbLoad_inj A v 2

theorem dockH_lbLoad (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH lbLoad H v = ![v 0, v 1, H 2, H 3, H 4, H 5, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot lbLoad lbLoad_inj H v 0
  · exact dockH_slot lbLoad lbLoad_inj H v 1
  · exact dockH_other lbLoad H v 2 (by decide)
  · exact dockH_other lbLoad H v 3 (by decide)
  · exact dockH_other lbLoad H v 4 (by decide)
  · exact dockH_other lbLoad H v 5 (by decide)
  · exact dockH_slot lbLoad lbLoad_inj H v 2

theorem lbBase_inj : Function.Injective lbBase := by decide

theorem install_lbBase (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install lbBase A v = ![A 0, A 1, v 1, v 0, A 4, v 2, A 6] := by
  funext i
  fin_cases i
  · exact install_other lbBase A v 0 (by decide)
  · exact install_other lbBase A v 1 (by decide)
  · exact install_slot lbBase lbBase_inj A v 1
  · exact install_slot lbBase lbBase_inj A v 0
  · exact install_other lbBase A v 4 (by decide)
  · exact install_slot lbBase lbBase_inj A v 2
  · exact install_other lbBase A v 6 (by decide)

theorem dockH_lbBase (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH lbBase H v = ![H 0, H 1, v 1, v 0, H 4, v 2, H 6] := by
  funext i
  fin_cases i
  · exact dockH_other lbBase H v 0 (by decide)
  · exact dockH_other lbBase H v 1 (by decide)
  · exact dockH_slot lbBase lbBase_inj H v 1
  · exact dockH_slot lbBase lbBase_inj H v 0
  · exact dockH_other lbBase H v 4 (by decide)
  · exact dockH_slot lbBase lbBase_inj H v 2
  · exact dockH_other lbBase H v 6 (by decide)

theorem lbDg_inj : Function.Injective lbDg := by decide

theorem install_lbDg (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install lbDg A v = ![A 0, A 1, v 1, A 3, v 0, v 2, A 6] := by
  funext i
  fin_cases i
  · exact install_other lbDg A v 0 (by decide)
  · exact install_other lbDg A v 1 (by decide)
  · exact install_slot lbDg lbDg_inj A v 1
  · exact install_other lbDg A v 3 (by decide)
  · exact install_slot lbDg lbDg_inj A v 0
  · exact install_slot lbDg lbDg_inj A v 2
  · exact install_other lbDg A v 6 (by decide)

theorem dockH_lbDg (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH lbDg H v = ![H 0, H 1, v 1, H 3, v 0, v 2, H 6] := by
  funext i
  fin_cases i
  · exact dockH_other lbDg H v 0 (by decide)
  · exact dockH_other lbDg H v 1 (by decide)
  · exact dockH_slot lbDg lbDg_inj H v 1
  · exact dockH_other lbDg H v 3 (by decide)
  · exact dockH_slot lbDg lbDg_inj H v 0
  · exact dockH_slot lbDg lbDg_inj H v 2
  · exact dockH_other lbDg H v 6 (by decide)

theorem lbGi_inj : Function.Injective lbGi := by decide

theorem install_lbGi (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install lbGi A v = ![A 0, v 0, v 1, A 3, A 4, v 2, A 6] := by
  funext i
  fin_cases i
  · exact install_other lbGi A v 0 (by decide)
  · exact install_slot lbGi lbGi_inj A v 0
  · exact install_slot lbGi lbGi_inj A v 1
  · exact install_other lbGi A v 3 (by decide)
  · exact install_other lbGi A v 4 (by decide)
  · exact install_slot lbGi lbGi_inj A v 2
  · exact install_other lbGi A v 6 (by decide)

theorem dockH_lbGi (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH lbGi H v = ![H 0, v 0, v 1, H 3, H 4, v 2, H 6] := by
  funext i
  fin_cases i
  · exact dockH_other lbGi H v 0 (by decide)
  · exact dockH_slot lbGi lbGi_inj H v 0
  · exact dockH_slot lbGi lbGi_inj H v 1
  · exact dockH_other lbGi H v 3 (by decide)
  · exact dockH_other lbGi H v 4 (by decide)
  · exact dockH_slot lbGi lbGi_inj H v 2
  · exact dockH_other lbGi H v 6 (by decide)

theorem lbOPut_inj : Function.Injective lbOPut := by decide

theorem install_lbOPut (A : Fin 7 → List Bool) (v : Fin 1 → List Bool) :
    install lbOPut A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6] := by
  funext i
  fin_cases i
  · exact install_other lbOPut A v 0 (by decide)
  · exact install_other lbOPut A v 1 (by decide)
  · exact install_slot lbOPut lbOPut_inj A v 0
  · exact install_other lbOPut A v 3 (by decide)
  · exact install_other lbOPut A v 4 (by decide)
  · exact install_other lbOPut A v 5 (by decide)
  · exact install_other lbOPut A v 6 (by decide)

theorem dockH_lbOPut (H : Fin 7 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbOPut H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6] := by
  funext i
  fin_cases i
  · exact dockH_other lbOPut H v 0 (by decide)
  · exact dockH_other lbOPut H v 1 (by decide)
  · exact dockH_slot lbOPut lbOPut_inj H v 0
  · exact dockH_other lbOPut H v 3 (by decide)
  · exact dockH_other lbOPut H v 4 (by decide)
  · exact dockH_other lbOPut H v 5 (by decide)
  · exact dockH_other lbOPut H v 6 (by decide)

theorem lbDPut_inj : Function.Injective lbDPut := by decide

theorem install_lbDPut (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install lbDPut A v = ![A 0, v 0] := by
  funext i
  fin_cases i
  · exact install_other lbDPut A v 0 (by decide)
  · exact install_slot lbDPut lbDPut_inj A v 0

theorem dockH_lbDPut (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH lbDPut H v = ![H 0, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other lbDPut H v 0 (by decide)
  · exact dockH_slot lbDPut lbDPut_inj H v 0

theorem lgP1_inj : Function.Injective lgP1 := by decide

theorem install_lgP1 (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install lgP1 A v = ![v 0, A 1, v 1, A 3, A 4, A 5, A 6, v 2, v 3, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_slot lgP1 lgP1_inj A v 0
  · exact install_other lgP1 A v 1 (by decide)
  · exact install_slot lgP1 lgP1_inj A v 1
  · exact install_other lgP1 A v 3 (by decide)
  · exact install_other lgP1 A v 4 (by decide)
  · exact install_other lgP1 A v 5 (by decide)
  · exact install_other lgP1 A v 6 (by decide)
  · exact install_slot lgP1 lgP1_inj A v 2
  · exact install_slot lgP1 lgP1_inj A v 3
  · exact install_other lgP1 A v 9 (by decide)
  · exact install_other lgP1 A v 10 (by decide)

theorem dockH_lgP1 (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH lgP1 H v = ![v 0, H 1, v 1, H 3, H 4, H 5, H 6, v 2, v 3, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_slot lgP1 lgP1_inj H v 0
  · exact dockH_other lgP1 H v 1 (by decide)
  · exact dockH_slot lgP1 lgP1_inj H v 1
  · exact dockH_other lgP1 H v 3 (by decide)
  · exact dockH_other lgP1 H v 4 (by decide)
  · exact dockH_other lgP1 H v 5 (by decide)
  · exact dockH_other lgP1 H v 6 (by decide)
  · exact dockH_slot lgP1 lgP1_inj H v 2
  · exact dockH_slot lgP1 lgP1_inj H v 3
  · exact dockH_other lgP1 H v 9 (by decide)
  · exact dockH_other lgP1 H v 10 (by decide)

theorem lgP2_inj : Function.Injective lgP2 := by decide

theorem install_lgP2 (A : Fin 11 → List Bool) (v : Fin 5 → List Bool) :
    install lgP2 A v = ![A 0, v 1, v 0, v 2, A 4, A 5, A 6, v 3, A 8, v 4, A 10] := by
  funext i
  fin_cases i
  · exact install_other lgP2 A v 0 (by decide)
  · exact install_slot lgP2 lgP2_inj A v 1
  · exact install_slot lgP2 lgP2_inj A v 0
  · exact install_slot lgP2 lgP2_inj A v 2
  · exact install_other lgP2 A v 4 (by decide)
  · exact install_other lgP2 A v 5 (by decide)
  · exact install_other lgP2 A v 6 (by decide)
  · exact install_slot lgP2 lgP2_inj A v 3
  · exact install_other lgP2 A v 8 (by decide)
  · exact install_slot lgP2 lgP2_inj A v 4
  · exact install_other lgP2 A v 10 (by decide)

theorem dockH_lgP2 (H : Fin 11 → ℕ) (v : Fin 5 → ℕ) :
    dockH lgP2 H v = ![H 0, v 1, v 0, v 2, H 4, H 5, H 6, v 3, H 8, v 4, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other lgP2 H v 0 (by decide)
  · exact dockH_slot lgP2 lgP2_inj H v 1
  · exact dockH_slot lgP2 lgP2_inj H v 0
  · exact dockH_slot lgP2 lgP2_inj H v 2
  · exact dockH_other lgP2 H v 4 (by decide)
  · exact dockH_other lgP2 H v 5 (by decide)
  · exact dockH_other lgP2 H v 6 (by decide)
  · exact dockH_slot lgP2 lgP2_inj H v 3
  · exact dockH_other lgP2 H v 8 (by decide)
  · exact dockH_slot lgP2 lgP2_inj H v 4
  · exact dockH_other lgP2 H v 10 (by decide)

theorem lgP3_inj : Function.Injective lgP3 := by decide

theorem install_lgP3 (A : Fin 11 → List Bool) (v : Fin 7 → List Bool) :
    install lgP3 A v = ![A 0, v 4, A 2, v 3, v 0, v 1, v 2, v 5, A 8, A 9, v 6] := by
  funext i
  fin_cases i
  · exact install_other lgP3 A v 0 (by decide)
  · exact install_slot lgP3 lgP3_inj A v 4
  · exact install_other lgP3 A v 2 (by decide)
  · exact install_slot lgP3 lgP3_inj A v 3
  · exact install_slot lgP3 lgP3_inj A v 0
  · exact install_slot lgP3 lgP3_inj A v 1
  · exact install_slot lgP3 lgP3_inj A v 2
  · exact install_slot lgP3 lgP3_inj A v 5
  · exact install_other lgP3 A v 8 (by decide)
  · exact install_other lgP3 A v 9 (by decide)
  · exact install_slot lgP3 lgP3_inj A v 6

theorem dockH_lgP3 (H : Fin 11 → ℕ) (v : Fin 7 → ℕ) :
    dockH lgP3 H v = ![H 0, v 4, H 2, v 3, v 0, v 1, v 2, v 5, H 8, H 9, v 6] := by
  funext i
  fin_cases i
  · exact dockH_other lgP3 H v 0 (by decide)
  · exact dockH_slot lgP3 lgP3_inj H v 4
  · exact dockH_other lgP3 H v 2 (by decide)
  · exact dockH_slot lgP3 lgP3_inj H v 3
  · exact dockH_slot lgP3 lgP3_inj H v 0
  · exact dockH_slot lgP3 lgP3_inj H v 1
  · exact dockH_slot lgP3 lgP3_inj H v 2
  · exact dockH_slot lgP3 lgP3_inj H v 5
  · exact dockH_other lgP3 H v 8 (by decide)
  · exact dockH_other lgP3 H v 9 (by decide)
  · exact dockH_slot lgP3 lgP3_inj H v 6

theorem lgPut_inj : Function.Injective lgPut := by decide

theorem install_lgPut (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install lgPut A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other lgPut A v 0 (by decide)
  · exact install_other lgPut A v 1 (by decide)
  · exact install_other lgPut A v 2 (by decide)
  · exact install_other lgPut A v 3 (by decide)
  · exact install_other lgPut A v 4 (by decide)
  · exact install_other lgPut A v 5 (by decide)
  · exact install_slot lgPut lgPut_inj A v 0
  · exact install_other lgPut A v 7 (by decide)
  · exact install_other lgPut A v 8 (by decide)
  · exact install_other lgPut A v 9 (by decide)
  · exact install_other lgPut A v 10 (by decide)

theorem dockH_lgPut (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH lgPut H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other lgPut H v 0 (by decide)
  · exact dockH_other lgPut H v 1 (by decide)
  · exact dockH_other lgPut H v 2 (by decide)
  · exact dockH_other lgPut H v 3 (by decide)
  · exact dockH_other lgPut H v 4 (by decide)
  · exact dockH_other lgPut H v 5 (by decide)
  · exact dockH_slot lgPut lgPut_inj H v 0
  · exact dockH_other lgPut H v 7 (by decide)
  · exact dockH_other lgPut H v 8 (by decide)
  · exact dockH_other lgPut H v 9 (by decide)
  · exact dockH_other lgPut H v 10 (by decide)

/-! ## Phase 1: `4·rowIdx` ones (tapes: 0 rowIdx, 1 the result, 2 a log) -/

noncomputable def p1 := Composition.machine ucopyR (Composition.machine ucopyR (Composition.machine ucopyR
  (Composition.machine ucopyR (RecoveryFocus.machine lbA (putM false)))))

theorem p1_step (r cap : ℕ) (rest Y : List Bool) (hcap : r + 1 ≤ cap) :
    Step p1 (4 * (2 * (r + 1) + 2 + 1) + 1) ![0, 0, 0]
      ![List.replicate r true ++ false :: rest, Y, List.replicate cap false]
      ![0, (List.replicate (4 * r) true ++ [false]).length, 0]
      ![List.replicate r true ++ false :: rest, overlay (List.replicate (4 * r) true ++ [false]) Y,
        List.replicate cap false] := by
  have c1 := ucopyStep rest [] Y r cap hcap
  have c2 := ucopyStep rest (List.replicate r true) Y r cap hcap
  have c3 := ucopyStep rest (List.replicate r true ++ List.replicate r true) Y r cap hcap
  have c4 := ucopyStep rest (List.replicate r true ++ List.replicate r true ++ List.replicate r true) Y r cap hcap
  have e4 : List.replicate r true ++ List.replicate r true ++ List.replicate r true ++ List.replicate r true =
      List.replicate (4 * r) true := by
    simp only [← List.replicate_add]; congr 1; ring
  rw [e4] at c4
  have p0 := putStep false (overlay (List.replicate (4 * r) true) Y) (List.replicate (4 * r) true).length
  rw [overlay_write] at p0
  have e5 := dockRun p0 lbA lbA_inj ![0, (List.replicate (4 * r) true).length, 0]
    ![List.replicate r true ++ false :: rest, overlay (List.replicate (4 * r) true) Y, List.replicate cap false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbA, dockH_lbA] at e5
  have hY : overlay [] Y = Y := by simp [overlay]
  rw [hY, List.nil_append] at c1
  have j := c1.seq (c2.seq (c3.seq (c4.seq (e5.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)))))
  refine (j.congr ?_ ?_).enlarge (le_of_eq (by ring))
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> rfl

/-- Phase 1 with the result's head returned (log on tape 3). -/
noncomputable def p1R := MaskedReset.machine p1 ![false, true, false]

theorem p1R_run (r cap cap' : ℕ) (rest Y : List Bool) (hcap : r + 1 ≤ cap)
    (hcap' : 4 * (2 * (r + 1) + 2 + 1) + 1 ≤ cap') :
    Step p1R (2 * (4 * (2 * (r + 1) + 2 + 1) + 1) + 2) ![0, 0, 0, 0]
      ![List.replicate r true ++ false :: rest, Y, List.replicate cap false, List.replicate cap' false]
      ![0, 0, 0, 0]
      ![List.replicate r true ++ false :: rest, overlay (List.replicate (4 * r) true ++ [false]) Y,
        List.replicate cap false, List.replicate cap' false] := by
  have hm := (p1_step r cap rest Y hcap).mask ![false, true, false] (by intro i hi; fin_cases i <;> simp_all) hcap'
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## Phase 2: the base `4·rowIdx·G` ones (tapes: 0 phase 1's ones, 1 `G`, 2 the base, 3 a log) -/

noncomputable def p2body := Composition.machine (RecoveryFocus.machine lbCp ucopyR) (RecoveryFocus.machine lbMv moveM)
noncomputable def p2loop := StreamController.machine p2body 0
noncomputable def p2 := Composition.machine p2loop (RecoveryFocus.machine lbPut (putM false))
/-- Phase 2 with both heads returned (log on tape 4). -/
noncomputable def p2R := MaskedReset.machine p2 ![true, false, true, false]

theorem p2_step (a G cap : ℕ) (rest gRest YB : List Bool) (hcap : G + 1 ≤ cap) :
    Step p2 ((a * (2 * (G + 1) + 2 + 1 + 1 + 2) + 1) + 1 + 1) ![0, 0, 0, 0]
      ![List.replicate a true ++ false :: rest, List.replicate G true ++ false :: gRest, YB, List.replicate cap false]
      ![a, 0, (List.replicate (a * G) true ++ [false]).length, 0]
      ![List.replicate a true ++ false :: rest, List.replicate G true ++ false :: gRest,
        overlay (List.replicate (a * G) true ++ [false]) YB, List.replicate cap false] := by
  set R := List.replicate a true ++ false :: rest
  set D := List.replicate G true ++ false :: gRest
  have hr := onesRun p2body 0 [] (false :: rest) a rfl
    (fun j => ![j, 0, j * G, 0]) (fun j => ![R, D, overlay (List.replicate (j * G) true) YB, List.replicate cap false])
    (fun j => by simp [R]) (fun j => by simp) (2 * (G + 1) + 2 + 1 + 1) (by
      intro j hj
      have c := ucopyStep gRest (List.replicate (j * G) true) YB G cap hcap
      simp only [List.length_replicate, List.length_append] at c
      have e1 := dockRun c lbCp lbCp_inj ![j, 0, j * G, 0] ![R, D, overlay (List.replicate (j * G) true) YB,
        List.replicate cap false] (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
      rw [install_lbCp, dockH_lbCp] at e1
      have e2 := dockRun (moveStep R j) lbMv lbMv_inj ![j, 0, (j + 1) * G, 0]
        ![R, D, overlay (List.replicate ((j + 1) * G) true) YB, List.replicate cap false]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_lbMv, dockH_lbMv] at e2
      have hG : List.replicate (j * G) true ++ List.replicate G true = List.replicate ((j + 1) * G) true := by
        rw [← List.replicate_add]; congr 1; ring
      rw [hG] at e1
      exact (e1.congr (by funext i; fin_cases i <;> simp [add_mul]) (by funext i; fin_cases i <;> rfl)).seq
        (e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)))
  simp only [Nat.zero_mul, List.replicate_zero] at hr
  have hY : overlay [] YB = YB := by simp [overlay]
  rw [hY] at hr
  have p0 := putStep false (overlay (List.replicate (a * G) true) YB) (List.replicate (a * G) true).length
  rw [overlay_write, List.length_replicate] at p0
  have e3 := dockRun p0 lbPut lbPut_inj ![a, 0, a * G, 0]
    ![R, D, overlay (List.replicate (a * G) true) YB, List.replicate cap false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbPut, dockH_lbPut] at e3
  refine hr.seq (e3.congr ?_ (by funext i; fin_cases i <;> rfl))
  funext i; fin_cases i <;> simp

def p2Cost (a G : ℕ) : ℕ := (a * (2 * (G + 1) + 2 + 1 + 1 + 2) + 1) + 1 + 1

theorem p2R_run (a G cap cap' : ℕ) (rest gRest YB : List Bool) (hcap : G + 1 ≤ cap) (hcap' : p2Cost a G ≤ cap') :
    Step p2R (2 * p2Cost a G + 2) ![0, 0, 0, 0, 0]
      ![List.replicate a true ++ false :: rest, List.replicate G true ++ false :: gRest, YB, List.replicate cap false,
        List.replicate cap' false]
      ![0, 0, 0, 0, 0]
      ![List.replicate a true ++ false :: rest, List.replicate G true ++ false :: gRest,
        overlay (List.replicate (a * G) true ++ [false]) YB, List.replicate cap false, List.replicate cap' false] := by
  have hm := (p2_step a G cap rest gRest YB hcap).mask ![true, false, true, false]
    (by intro i hi; fin_cases i <;> simp_all) hcap'
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## Phase 3: one occurrence's four labels (tapes: 0 the occurrences, 1 the occurrence register, 2 the output,
3 the base, 4 `G`, 5 a log, 6 the register's log) -/

noncomputable def giLoadIn := Composition.machine ucopyM (RecoveryFocus.machine lbDPut (putM false))
/-- Copy the occurrence's unary index into its register (register head returned; log on tape 2). -/
noncomputable def giLoad := MaskedReset.machine giLoadIn ![false, true]

theorem giLoad_run (pre rest Yg : List Bool) (gi cap : ℕ) (hcap : gi + 1 + 1 + 1 ≤ cap) :
    Step giLoad (2 * (gi + 1 + 1 + 1) + 2) ![pre.length, 0, 0]
      ![pre ++ List.replicate gi true ++ false :: rest, Yg, List.replicate cap false]
      ![pre.length + gi, 0, 0]
      ![pre ++ List.replicate gi true ++ false :: rest, overlay (List.replicate gi true ++ [false]) Yg,
        List.replicate cap false] := by
  have c := ucopy_run pre rest [] Yg gi
  have hY : overlay [] Yg = Yg := by simp [overlay]
  rw [hY, List.nil_append] at c
  have p0 := putStep false (overlay (List.replicate gi true) Yg) (List.replicate gi true).length
  rw [overlay_write] at p0
  have e := dockRun p0 lbDPut lbDPut_inj ![pre.length + gi, (List.replicate gi true).length]
    ![pre ++ List.replicate gi true ++ false :: rest, overlay (List.replicate gi true) Yg]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbDPut, dockH_lbDPut] at e
  have j := c.seq (e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))
  have hm := j.mask ![false, true] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

def lH (g o : ℕ) : Fin 7 → ℕ := ![g, 0, o, 0, 0, 0, 0]
def lA (GS GI OUT BASE DG LG LGc : List Bool) : Fin 7 → List Bool := ![GS, GI, OUT, BASE, DG, LG, LGc]

section Corner
variable (GS GI BASE DG LGc : List Bool) (g cap : ℕ)

theorem lb_base (x : ℕ) (rest out BW : List Bool) (hc : x + 1 ≤ cap) :
    Step (RecoveryFocus.machine lbBase ucopyR) (2 * (x + 1) + 2) (lH g out.length)
      (lA GS GI (overlay out BW) (List.replicate x true ++ false :: rest) DG (List.replicate cap false) LGc)
      (lH g (out ++ List.replicate x true).length)
      (lA GS GI (overlay (out ++ List.replicate x true) BW) (List.replicate x true ++ false :: rest) DG
        (List.replicate cap false) LGc) := by
  have e := dockRun (ucopyStep rest out BW x cap hc) lbBase lbBase_inj (lH g out.length)
    (lA GS GI (overlay out BW) (List.replicate x true ++ false :: rest) DG (List.replicate cap false) LGc)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lbBase, dockH_lbBase] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem lb_dg (x : ℕ) (rest out BW : List Bool) (hc : x + 1 ≤ cap) :
    Step (RecoveryFocus.machine lbDg ucopyR) (2 * (x + 1) + 2) (lH g out.length)
      (lA GS GI (overlay out BW) BASE (List.replicate x true ++ false :: rest) (List.replicate cap false) LGc)
      (lH g (out ++ List.replicate x true).length)
      (lA GS GI (overlay (out ++ List.replicate x true) BW) BASE (List.replicate x true ++ false :: rest)
        (List.replicate cap false) LGc) := by
  have e := dockRun (ucopyStep rest out BW x cap hc) lbDg lbDg_inj (lH g out.length)
    (lA GS GI (overlay out BW) BASE (List.replicate x true ++ false :: rest) (List.replicate cap false) LGc)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lbDg, dockH_lbDg] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem lb_gi (x : ℕ) (rest out BW : List Bool) (hc : x + 1 ≤ cap) :
    Step (RecoveryFocus.machine lbGi ucopyR) (2 * (x + 1) + 2) (lH g out.length)
      (lA GS (List.replicate x true ++ false :: rest) (overlay out BW) BASE DG (List.replicate cap false) LGc)
      (lH g (out ++ List.replicate x true).length)
      (lA GS (List.replicate x true ++ false :: rest) (overlay (out ++ List.replicate x true) BW) BASE DG
        (List.replicate cap false) LGc) := by
  have e := dockRun (ucopyStep rest out BW x cap hc) lbGi lbGi_inj (lH g out.length)
    (lA GS (List.replicate x true ++ false :: rest) (overlay out BW) BASE DG (List.replicate cap false) LGc)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lbGi, dockH_lbGi] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem lb_put (LG out BW : List Bool) :
    Step (RecoveryFocus.machine lbOPut (putM false)) 1 (lH g out.length) (lA GS GI (overlay out BW) BASE DG LG LGc)
      (lH g (out ++ [false]).length) (lA GS GI (overlay (out ++ [false]) BW) BASE DG LG LGc) := by
  have p0 := putStep false (overlay out BW) out.length
  rw [overlay_write] at p0
  have e := dockRun p0 lbOPut lbOPut_inj (lH g out.length) (lA GS GI (overlay out BW) BASE DG LG LGc)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbOPut, dockH_lbOPut] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [lH]

end Corner

noncomputable def lbTail := Composition.machine (RecoveryFocus.machine lbGi ucopyR) (RecoveryFocus.machine lbOPut (putM false))
noncomputable def lbD1 := Composition.machine (RecoveryFocus.machine lbDg ucopyR) lbTail
noncomputable def lbD2 := Composition.machine (RecoveryFocus.machine lbDg ucopyR) lbD1
noncomputable def lbD3 := Composition.machine (RecoveryFocus.machine lbDg ucopyR) lbD2
noncomputable def lbC0 := Composition.machine (RecoveryFocus.machine lbBase ucopyR) lbTail
noncomputable def lbC1 := Composition.machine (RecoveryFocus.machine lbBase ucopyR) lbD1
noncomputable def lbC2 := Composition.machine (RecoveryFocus.machine lbBase ucopyR) lbD2
noncomputable def lbC3 := Composition.machine (RecoveryFocus.machine lbBase ucopyR) lbD3
/-- The four corners of one occurrence. -/
noncomputable def lbCorners := Composition.machine lbC0 (Composition.machine lbC1 (Composition.machine lbC2 lbC3))

/-- One corner's label word. -/
def cornerWord (B G gi k : ℕ) : List Bool := List.replicate (B + k * G + gi) true ++ [false]

def ucCost (x : ℕ) : ℕ := 2 * (x + 1) + 2

section Corners
variable (GS : List Bool) (g B G gi cap : ℕ) (bRest gRest iRest LGc BW : List Bool)

/-- The corner tapes. -/
def cT (out : List Bool) : Fin 7 → List Bool :=
  lA GS (List.replicate gi true ++ false :: iRest) (overlay out BW) (List.replicate B true ++ false :: bRest)
    (List.replicate G true ++ false :: gRest) (List.replicate cap false) LGc

theorem tail_run (out : List Bool) (hc : gi + 1 ≤ cap) :
    Step lbTail (ucCost gi + 1 + 1) (lH g out.length) (cT GS B G gi cap bRest gRest iRest LGc BW out)
      (lH g (out ++ List.replicate gi true ++ [false]).length)
      (cT GS B G gi cap bRest gRest iRest LGc BW (out ++ List.replicate gi true ++ [false])) :=
  (lb_gi GS (List.replicate B true ++ false :: bRest) (List.replicate G true ++ false :: gRest) LGc g cap gi iRest out BW
    hc).seq (lb_put GS (List.replicate gi true ++ false :: iRest) (List.replicate B true ++ false :: bRest)
      (List.replicate G true ++ false :: gRest) LGc g (List.replicate cap false) (out ++ List.replicate gi true) BW)

theorem dg_step (out : List Bool) (hc : G + 1 ≤ cap) :
    Step (RecoveryFocus.machine lbDg ucopyR) (ucCost G) (lH g out.length) (cT GS B G gi cap bRest gRest iRest LGc BW out)
      (lH g (out ++ List.replicate G true).length)
      (cT GS B G gi cap bRest gRest iRest LGc BW (out ++ List.replicate G true)) :=
  lb_dg GS (List.replicate gi true ++ false :: iRest) (List.replicate B true ++ false :: bRest) LGc g cap G gRest out BW hc

theorem base_step (out : List Bool) (hc : B + 1 ≤ cap) :
    Step (RecoveryFocus.machine lbBase ucopyR) (ucCost B) (lH g out.length)
      (cT GS B G gi cap bRest gRest iRest LGc BW out) (lH g (out ++ List.replicate B true).length)
      (cT GS B G gi cap bRest gRest iRest LGc BW (out ++ List.replicate B true)) :=
  lb_base GS (List.replicate gi true ++ false :: iRest) (List.replicate G true ++ false :: gRest) LGc g cap B bRest out
    BW hc

def corner0Cost (B gi : ℕ) : ℕ := ucCost B + 1 + (ucCost gi + 1 + 1)
def corner1Cost (B G gi : ℕ) : ℕ := ucCost B + 1 + (ucCost G + 1 + (ucCost gi + 1 + 1))
def corner2Cost (B G gi : ℕ) : ℕ := ucCost B + 1 + (ucCost G + 1 + (ucCost G + 1 + (ucCost gi + 1 + 1)))
def corner3Cost (B G gi : ℕ) : ℕ := ucCost B + 1 + (ucCost G + 1 + (ucCost G + 1 + (ucCost G + 1 + (ucCost gi + 1 + 1))))
def cornersCost (B G gi : ℕ) : ℕ :=
  corner0Cost B gi + 1 + (corner1Cost B G gi + 1 + (corner2Cost B G gi + 1 + corner3Cost B G gi))

/-- **One occurrence's four corner labels** appended. -/
theorem corners_run (out : List Bool) (hB : B + 1 ≤ cap) (hG : G + 1 ≤ cap) (hi : gi + 1 ≤ cap) :
    Step lbCorners (cornersCost B G gi) (lH g out.length) (cT GS B G gi cap bRest gRest iRest LGc BW out)
      (lH g (out ++ ((List.range 4).map (cornerWord B G gi)).flatten).length)
      (cT GS B G gi cap bRest gRest iRest LGc BW (out ++ ((List.range 4).map (cornerWord B G gi)).flatten)) := by
  have hw : ∀ k : ℕ, ∀ o : List Bool, o ++ List.replicate B true ++ (List.replicate G true).flatMap (fun _ => [])
      = o ++ List.replicate B true := fun _ o => by simp
  have e0 := (base_step GS g B G gi cap bRest gRest iRest LGc BW out hB).seq
    (tail_run GS g B G gi cap bRest gRest iRest LGc BW (out ++ List.replicate B true) hi)
  set o1 := out ++ List.replicate B true ++ List.replicate gi true ++ [false]
  have e1 := (base_step GS g B G gi cap bRest gRest iRest LGc BW o1 hB).seq
    ((dg_step GS g B G gi cap bRest gRest iRest LGc BW (o1 ++ List.replicate B true) hG).seq
      (tail_run GS g B G gi cap bRest gRest iRest LGc BW (o1 ++ List.replicate B true ++ List.replicate G true) hi))
  set o2 := o1 ++ List.replicate B true ++ List.replicate G true ++ List.replicate gi true ++ [false]
  have e2 := (base_step GS g B G gi cap bRest gRest iRest LGc BW o2 hB).seq
    ((dg_step GS g B G gi cap bRest gRest iRest LGc BW (o2 ++ List.replicate B true) hG).seq
      ((dg_step GS g B G gi cap bRest gRest iRest LGc BW (o2 ++ List.replicate B true ++ List.replicate G true) hG).seq
        (tail_run GS g B G gi cap bRest gRest iRest LGc BW
          (o2 ++ List.replicate B true ++ List.replicate G true ++ List.replicate G true) hi)))
  set o3 := o2 ++ List.replicate B true ++ List.replicate G true ++ List.replicate G true ++ List.replicate gi true ++ [false]
  have e3 := (base_step GS g B G gi cap bRest gRest iRest LGc BW o3 hB).seq
    ((dg_step GS g B G gi cap bRest gRest iRest LGc BW (o3 ++ List.replicate B true) hG).seq
      ((dg_step GS g B G gi cap bRest gRest iRest LGc BW (o3 ++ List.replicate B true ++ List.replicate G true) hG).seq
        ((dg_step GS g B G gi cap bRest gRest iRest LGc BW
          (o3 ++ List.replicate B true ++ List.replicate G true ++ List.replicate G true) hG).seq
          (tail_run GS g B G gi cap bRest gRest iRest LGc BW
            (o3 ++ List.replicate B true ++ List.replicate G true ++ List.replicate G true ++ List.replicate G true) hi))))
  have j := e0.seq (e1.seq (e2.seq e3))
  have hfin : o3 ++ List.replicate B true ++ List.replicate G true ++ List.replicate G true ++ List.replicate G true ++
      List.replicate gi true ++ [false] = out ++ ((List.range 4).map (cornerWord B G gi)).flatten := by
    simp only [o3, o2, o1, cornerWord, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil, List.append_assoc,
      Nat.zero_mul, Nat.add_zero, one_mul]
    simp only [← List.append_assoc, ← List.replicate_add]
    simp [List.append_assoc, show ∀ x : ℕ, 2 * x = x + x from fun x => by ring,
      show ∀ x : ℕ, 3 * x = x + x + x from fun x => by ring, Nat.add_assoc]
  rw [hfin] at j
  exact j

end Corners

/-- One occurrence: step over its mark, load its index, step over its end, write its four corner labels. -/
noncomputable def giBody := Composition.machine (RecoveryFocus.machine lbGMv moveM)
  (Composition.machine (RecoveryFocus.machine lbLoad giLoad)
    (Composition.machine (RecoveryFocus.machine lbGMv moveM) lbCorners))

/-- An occurrence's code on the occurrence stream: a mark, its unary index, `0`. -/
def giEnc (gi : ℕ) : List Bool := true :: (List.replicate gi true ++ [false])

def giCost (B G gi : ℕ) : ℕ := 1 + 1 + ((2 * (gi + 1 + 1 + 1) + 2) + 1 + (1 + 1 + cornersCost B G gi))

theorem giBody_run (B G gi cap capC : ℕ) (P rest Yg out BW bRest gRest : List Bool) (hB : B + 1 ≤ cap)
    (hG : G + 1 ≤ cap) (hi : gi + 1 ≤ cap) (hC : gi + 1 + 1 + 1 ≤ capC) :
    Step giBody (giCost B G gi) (lH P.length out.length)
      (lA (P ++ giEnc gi ++ rest) Yg (overlay out BW) (List.replicate B true ++ false :: bRest)
        (List.replicate G true ++ false :: gRest) (List.replicate cap false) (List.replicate capC false))
      (lH (P ++ giEnc gi).length (out ++ ((List.range 4).map (cornerWord B G gi)).flatten).length)
      (lA (P ++ giEnc gi ++ rest) (overlay (List.replicate gi true ++ [false]) Yg)
        (overlay (out ++ ((List.range 4).map (cornerWord B G gi)).flatten) BW) (List.replicate B true ++ false :: bRest)
        (List.replicate G true ++ false :: gRest) (List.replicate cap false) (List.replicate capC false)) := by
  set GS := P ++ giEnc gi ++ rest
  set BA := List.replicate B true ++ false :: bRest
  set DG := List.replicate G true ++ false :: gRest
  set lg := List.replicate cap false
  set lgc := List.replicate capC false
  have e1 := dockRun (moveStep GS P.length) lbGMv lbGMv_inj (lH P.length out.length)
    (lA GS Yg (overlay out BW) BA DG lg lgc) (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbGMv, dockH_lbGMv] at e1
  have hS : GS = (P ++ [true]) ++ List.replicate gi true ++ false :: rest := by simp [GS, giEnc, List.append_assoc]
  have c2 := giLoad_run (P ++ [true]) rest Yg gi capC hC
  rw [← hS, show (P ++ [true]).length = P.length + 1 by simp] at c2
  have e2 := dockRun c2 lbLoad lbLoad_inj (lH (P.length + 1) out.length) (lA GS Yg (overlay out BW) BA DG lg lgc)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lbLoad, dockH_lbLoad] at e2
  have e3 := dockRun (moveStep GS (P.length + 1 + gi)) lbGMv lbGMv_inj (lH (P.length + 1 + gi) out.length)
    (lA GS (overlay (List.replicate gi true ++ [false]) Yg) (overlay out BW) BA DG lg lgc)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lbGMv, dockH_lbGMv] at e3
  have hG' : overlay (List.replicate gi true ++ [false]) Yg = List.replicate gi true ++ false :: Yg.drop (gi + 1) := by
    simp [overlay, List.append_assoc]
  have e4 := corners_run GS (P.length + 1 + gi + 1) B G gi cap bRest gRest (Yg.drop (gi + 1)) lgc BW out hB hG hi
  unfold cT at e4
  rw [← hG'] at e4
  have j := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      ((e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq e4))
  have hl : P.length + 1 + gi + 1 = (P ++ giEnc gi).length := by simp [giEnc]; omega
  rw [hl] at j
  exact j

/-- The loop over the occurrences (tape 0). -/
noncomputable def giLoop := StreamController.machine giBody 0

/-- The occurrences' corner labels, as the loop writes them. -/
def giWords (B G : ℕ) (gis : List ℕ) : List Bool := gis.flatMap fun gi => ((List.range 4).map (cornerWord B G gi)).flatten

theorem giCost_mono (B G gi M : ℕ) (h : gi ≤ M) : giCost B G gi ≤ giCost B G M := by
  unfold giCost cornersCost corner0Cost corner1Cost corner2Cost corner3Cost ucCost
  omega

theorem giEnc_head (gi : ℕ) : ∃ l, giEnc gi = true :: l := ⟨_, rfl⟩

/-- **Every occurrence's corner labels.** -/
theorem giLoop_run (B G M cap capC : ℕ) (gis : List ℕ) (post Yg BW bRest gRest : List Bool)
    (hB : B + 1 ≤ cap) (hG : G + 1 ≤ cap) (hM : ∀ gi ∈ gis, gi ≤ M) (hi : M + 1 ≤ cap) (hC : M + 1 + 1 + 1 ≤ capC) :
    Step giLoop (gis.length * (giCost B G M + 2) + 1) (lH 0 0)
      (lA (gis.flatMap giEnc ++ false :: post) Yg (overlay [] BW) (List.replicate B true ++ false :: bRest)
        (List.replicate G true ++ false :: gRest) (List.replicate cap false) (List.replicate capC false))
      (lH (gis.flatMap giEnc).length (giWords B G gis).length)
      (lA (gis.flatMap giEnc ++ false :: post)
        (gis.foldl (fun Y gi => overlay (List.replicate gi true ++ [false]) Y) Yg) (overlay (giWords B G gis) BW)
        (List.replicate B true ++ false :: bRest) (List.replicate G true ++ false :: gRest) (List.replicate cap false)
        (List.replicate capC false)) := by
  set GS := gis.flatMap giEnc ++ false :: post
  set fY := fun (Y : List Bool) (gi : ℕ) => overlay (List.replicate gi true ++ [false]) Y
  have hr := encRun giEnc giEnc_head giBody 0 [] gis post
    (fun (st : List Bool × List Bool) (gi : ℕ) => (st.1 ++ ((List.range 4).map (cornerWord B G gi)).flatten, fY st.2 gi))
    ([], Yg) (fun st p => lH p st.1.length)
    (fun st => lA GS st.2 (overlay st.1 BW) (List.replicate B true ++ false :: bRest)
      (List.replicate G true ++ false :: gRest) (List.replicate cap false) (List.replicate capC false))
    (fun st => rfl) (fun st p => rfl) (giCost B G M) (by
      intro j hj
      have hgi := hM gis[j] (List.getElem_mem hj)
      have hS : GS = ((gis.take j).flatMap giEnc) ++ giEnc gis[j] ++ ((gis.drop (j + 1)).flatMap giEnc ++ false :: post) := by
        simp only [GS]
        rw [enc_split giEnc gis j hj]
        simp [List.append_assoc]
      set st := (gis.take j).foldl
        (fun (st : List Bool × List Bool) (gi : ℕ) => (st.1 ++ ((List.range 4).map (cornerWord B G gi)).flatten, fY st.2 gi))
        ([], Yg)
      have b := giBody_run B G gis[j] cap capC ((gis.take j).flatMap giEnc) ((gis.drop (j + 1)).flatMap giEnc ++ false :: post)
        st.2 st.1 BW bRest gRest hB hG (by omega) (by omega)
      rw [← hS] at b
      have ht : gis.take (j + 1) = gis.take j ++ [gis[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (gis.take (j + 1)).foldl
          (fun (st : List Bool × List Bool) (gi : ℕ) => (st.1 ++ ((List.range 4).map (cornerWord B G gi)).flatten, fY st.2 gi))
          ([], Yg) = (st.1 ++ ((List.range 4).map (cornerWord B G gis[j])).flatten, fY st.2 gis[j]) := by
        rw [ht, List.foldl_append]; rfl
      have hpos : ([] : List Bool).length + ((gis.take (j + 1)).flatMap giEnc).length =
          ((gis.take j).flatMap giEnc ++ giEnc gis[j]).length := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_nil, Nat.zero_add]
      rw [hst, hpos]
      refine (b.congr_in ?_ rfl).enlarge (giCost_mono B G _ M hgi)
      simp)
  simp only [List.length_nil, Nat.zero_add] at hr
  have hfold : ∀ (l : List ℕ) (st : List Bool × List Bool), (l.foldl
      (fun (st : List Bool × List Bool) (gi : ℕ) => (st.1 ++ ((List.range 4).map (cornerWord B G gi)).flatten, fY st.2 gi))
      st) = (st.1 ++ giWords B G l, l.foldl fY st.2) := by
    intro l
    induction l with
    | nil => intro st; simp [giWords]
    | cons gi l ih => intro st; rw [List.foldl_cons, ih]; simp [giWords, List.append_assoc]
  rw [hfold] at hr
  simp only [List.nil_append] at hr
  exact hr

/-! ## The label word -/

/-- **The label-word machine** (tapes: 0 `rowIdx`, 1 `G`, 2-3 scratch, 4 the occurrences, 5 their register, 6 the
output, 7-10 logs). -/
noncomputable def labelsM := Composition.machine (RecoveryFocus.machine lgP1 p1R)
  (Composition.machine (RecoveryFocus.machine lgP2 p2R)
    (Composition.machine (RecoveryFocus.machine lgP3 giLoop) (RecoveryFocus.machine lgPut (putM false))))

/-- The machine's words are the label word of the population. -/
theorem giWords_eq (G r : ℕ) (gis : List ℕ) :
    giWords (4 * r * G) G gis ++ [false] = labelWord (labsOf G r gis) := by
  unfold giWords labelWord labsOf
  congr 1
  rw [List.flatMap_assoc]
  congr 1
  funext gi
  rw [List.flatMap_map]
  induction (List.range 4) with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
    congr 1
    unfold cornerWord atomCodeW poolIndex
    congr 2
    ring

def labelsCost (r G M B : ℕ) (n : ℕ) : ℕ :=
  (2 * (4 * (2 * (r + 1) + 2 + 1) + 1) + 2) + 1 + ((2 * p2Cost (4 * r) G + 2) + 1 +
    ((n * (giCost B G M + 2) + 1) + 1 + 1))

/-- **Word (3): the label word of a population**. -/
theorem labels_run (G r M : ℕ) (gis : List ℕ) (rRest gRest Y4 YB YG post BWO : List Bool) (cap capA capB capC : ℕ)
    (hM : ∀ gi ∈ gis, gi ≤ M) (hr : r + 1 ≤ cap) (hG : G + 1 ≤ cap) (hB : 4 * r * G + 1 ≤ cap) (hi : M + 1 ≤ cap)
    (hA : 4 * (2 * (r + 1) + 2 + 1) + 1 ≤ capA) (hBc : p2Cost (4 * r) G ≤ capB) (hC : M + 1 + 1 + 1 ≤ capC) :
    Step labelsM (labelsCost r G M (4 * r * G) gis.length) (fun _ => 0)
      ![List.replicate r true ++ false :: rRest, List.replicate G true ++ false :: gRest, Y4, YB,
        gis.flatMap giEnc ++ false :: post, YG, BWO, List.replicate cap false, List.replicate capA false,
        List.replicate capB false, List.replicate capC false]
      ![0, 0, 0, 0, (gis.flatMap giEnc).length, 0, (labelWord (labsOf G r gis)).length, 0, 0, 0, 0]
      ![List.replicate r true ++ false :: rRest, List.replicate G true ++ false :: gRest,
        overlay (List.replicate (4 * r) true ++ [false]) Y4,
        overlay (List.replicate (4 * r * G) true ++ [false]) YB, gis.flatMap giEnc ++ false :: post,
        gis.foldl (fun Y gi => overlay (List.replicate gi true ++ [false]) Y) YG,
        overlay (labelWord (labsOf G r gis)) BWO, List.replicate cap false, List.replicate capA false,
        List.replicate capB false, List.replicate capC false] := by
  set RS := List.replicate r true ++ false :: rRest
  set DG := List.replicate G true ++ false :: gRest
  set GIS := gis.flatMap giEnc ++ false :: post
  have c1 := p1R_run r cap capA rRest Y4 hr hA
  have e1 := dockRun c1 lgP1 lgP1_inj (fun _ => 0)
    ![RS, DG, Y4, YB, GIS, YG, BWO, List.replicate cap false, List.replicate capA false, List.replicate capB false,
      List.replicate capC false] (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lgP1, dockH_lgP1] at e1
  have hR4 : overlay (List.replicate (4 * r) true ++ [false]) Y4 =
      List.replicate (4 * r) true ++ false :: Y4.drop (4 * r + 1) := by simp [overlay, List.append_assoc]
  have c2 := p2R_run (4 * r) G cap capB (Y4.drop (4 * r + 1)) gRest YB hG hBc
  rw [← hR4] at c2
  have e2 := dockRun c2 lgP2 lgP2_inj (fun _ => 0)
    ![RS, DG, overlay (List.replicate (4 * r) true ++ [false]) Y4, YB, GIS, YG, BWO, List.replicate cap false,
      List.replicate capA false, List.replicate capB false, List.replicate capC false]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lgP2, dockH_lgP2] at e2
  have hBA : overlay (List.replicate (4 * r * G) true ++ [false]) YB =
      List.replicate (4 * r * G) true ++ false :: YB.drop (4 * r * G + 1) := by simp [overlay, List.append_assoc]
  have c3 := giLoop_run (4 * r * G) G M cap capC gis post YG BWO (YB.drop (4 * r * G + 1)) gRest hB hG hM hi hC
  rw [← hBA] at c3
  have hBW : overlay [] BWO = BWO := by simp [overlay]
  rw [hBW] at c3
  have e3 := dockRun c3 lgP3 lgP3_inj (fun _ => 0)
    ![RS, DG, overlay (List.replicate (4 * r) true ++ [false]) Y4, overlay (List.replicate (4 * r * G) true ++ [false]) YB,
      GIS, YG, BWO, List.replicate cap false, List.replicate capA false, List.replicate capB false,
      List.replicate capC false]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_lgP3, dockH_lgP3] at e3
  have p0 := putStep false (overlay (giWords (4 * r * G) G gis) BWO) (giWords (4 * r * G) G gis).length
  rw [overlay_write, giWords_eq] at p0
  have e4 := dockRun p0 lgPut lgPut_inj
    ![0, 0, 0, 0, (gis.flatMap giEnc).length, 0, (giWords (4 * r * G) G gis).length, 0, 0, 0, 0]
    ![RS, DG, overlay (List.replicate (4 * r) true ++ [false]) Y4, overlay (List.replicate (4 * r * G) true ++ [false]) YB,
      GIS, gis.foldl (fun Y gi => overlay (List.replicate gi true ++ [false]) Y) YG,
      overlay (giWords (4 * r * G) G gis) BWO, List.replicate cap false, List.replicate capA false,
      List.replicate capB false, List.replicate capC false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_lgPut, dockH_lgPut] at e4
  have hlen : (giWords (4 * r * G) G gis).length + 1 = (labelWord (labsOf G r gis)).length := by
    rw [← giWords_eq]; simp
  rw [hlen] at e4
  have j := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      ((e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
        (e4.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))))
  exact j

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
