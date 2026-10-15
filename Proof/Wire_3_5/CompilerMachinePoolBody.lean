import Proof.Wire_3_5.CompilerMachinePoolNorm

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- A transduced register pair with stale suffixes (all three heads back at cell `0`; log on tape 3). -/
theorem zipT (out nxt : Bool → Bool → Bool → Bool) (init : Bool) (u v tu tv Z : List Bool) (hl : u.length = v.length)
    (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (zipM out nxt init) (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0]
      ![frame u ++ tu, frame v ++ tv, Z, List.replicate cap false]
      ![0, 0, 0, 0] ![frame u ++ tu, frame v ++ tv, overlay (frame (ZipMap.map out nxt u v init)) Z,
        List.replicate cap false] := by
  have h0 := mapStepO out nxt init [] [] u v tu tv [] Z hl
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0
  have hZ : overlay [] Z = Z := by simp [overlay]
  rw [hZ] at h0
  have hm := h0.mask ![true, true, true] (by intro i _; fin_cases i <;> rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

theorem overlay_collapse (a b M : List Bool) (h : a.length = b.length) : overlay a (overlay b M) = overlay a M := by
  simp only [overlay, List.drop_append, h, Nat.sub_self, List.drop_zero, List.drop_eq_nil_of_le (le_refl b.length),
    List.nil_append]

theorem frame_tail (w Y : List Bool) : overlay (frame w) Y = frame w ++ Y.drop (frame w).length := rfl

/-- The pair a coordinate adds to the dense fields: swapped when flipped. -/
def pairF (h : ℕ) (fl : Bool) (v : ℕ × ℕ) : List Bool :=
  if fl then frame (binary h v.2) ++ frame (binary h v.1) else frame (binary h v.1) ++ frame (binary h v.2)

/-! ## The coordinate body's primitive steps (tapes 0-10) -/

def bLoadP : Fin 3 → Fin 11 := ![0, 3, 10]
def bLoadN : Fin 3 → Fin 11 := ![0, 4, 10]
def bMvN : Fin 1 → Fin 11 := ![0]
def bMvS : Fin 1 → Fin 11 := ![1]
def bMvF : Fin 1 → Fin 11 := ![2]
def bEmPL : Fin 3 → Fin 11 := ![3, 5, 10]
def bEmNL : Fin 3 → Fin 11 := ![4, 5, 10]
def bEmPR : Fin 3 → Fin 11 := ![3, 6, 10]
def bEmNR : Fin 3 → Fin 11 := ![4, 6, 10]
def bZipP : Fin 4 → Fin 11 := ![7, 4, 9, 10]
def bCpP : Fin 3 → Fin 11 := ![9, 7, 10]
def bZipN : Fin 4 → Fin 11 := ![8, 3, 9, 10]
def bCpN : Fin 3 → Fin 11 := ![9, 8, 10]

theorem bLoadP_inj : Function.Injective bLoadP := by decide

theorem install_bLoadP (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bLoadP A v = ![v 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_slot bLoadP bLoadP_inj A v 0
  · exact install_other bLoadP A v 1 (by decide)
  · exact install_other bLoadP A v 2 (by decide)
  · exact install_slot bLoadP bLoadP_inj A v 1
  · exact install_other bLoadP A v 4 (by decide)
  · exact install_other bLoadP A v 5 (by decide)
  · exact install_other bLoadP A v 6 (by decide)
  · exact install_other bLoadP A v 7 (by decide)
  · exact install_other bLoadP A v 8 (by decide)
  · exact install_other bLoadP A v 9 (by decide)
  · exact install_slot bLoadP bLoadP_inj A v 2

theorem dockH_bLoadP (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bLoadP H v = ![v 0, H 1, H 2, v 1, H 4, H 5, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot bLoadP bLoadP_inj H v 0
  · exact dockH_other bLoadP H v 1 (by decide)
  · exact dockH_other bLoadP H v 2 (by decide)
  · exact dockH_slot bLoadP bLoadP_inj H v 1
  · exact dockH_other bLoadP H v 4 (by decide)
  · exact dockH_other bLoadP H v 5 (by decide)
  · exact dockH_other bLoadP H v 6 (by decide)
  · exact dockH_other bLoadP H v 7 (by decide)
  · exact dockH_other bLoadP H v 8 (by decide)
  · exact dockH_other bLoadP H v 9 (by decide)
  · exact dockH_slot bLoadP bLoadP_inj H v 2

theorem bLoadN_inj : Function.Injective bLoadN := by decide

theorem install_bLoadN (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bLoadN A v = ![v 0, A 1, A 2, A 3, v 1, A 5, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_slot bLoadN bLoadN_inj A v 0
  · exact install_other bLoadN A v 1 (by decide)
  · exact install_other bLoadN A v 2 (by decide)
  · exact install_other bLoadN A v 3 (by decide)
  · exact install_slot bLoadN bLoadN_inj A v 1
  · exact install_other bLoadN A v 5 (by decide)
  · exact install_other bLoadN A v 6 (by decide)
  · exact install_other bLoadN A v 7 (by decide)
  · exact install_other bLoadN A v 8 (by decide)
  · exact install_other bLoadN A v 9 (by decide)
  · exact install_slot bLoadN bLoadN_inj A v 2

theorem dockH_bLoadN (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bLoadN H v = ![v 0, H 1, H 2, H 3, v 1, H 5, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_slot bLoadN bLoadN_inj H v 0
  · exact dockH_other bLoadN H v 1 (by decide)
  · exact dockH_other bLoadN H v 2 (by decide)
  · exact dockH_other bLoadN H v 3 (by decide)
  · exact dockH_slot bLoadN bLoadN_inj H v 1
  · exact dockH_other bLoadN H v 5 (by decide)
  · exact dockH_other bLoadN H v 6 (by decide)
  · exact dockH_other bLoadN H v 7 (by decide)
  · exact dockH_other bLoadN H v 8 (by decide)
  · exact dockH_other bLoadN H v 9 (by decide)
  · exact dockH_slot bLoadN bLoadN_inj H v 2

theorem bMvN_inj : Function.Injective bMvN := by decide

theorem install_bMvN (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install bMvN A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_slot bMvN bMvN_inj A v 0
  · exact install_other bMvN A v 1 (by decide)
  · exact install_other bMvN A v 2 (by decide)
  · exact install_other bMvN A v 3 (by decide)
  · exact install_other bMvN A v 4 (by decide)
  · exact install_other bMvN A v 5 (by decide)
  · exact install_other bMvN A v 6 (by decide)
  · exact install_other bMvN A v 7 (by decide)
  · exact install_other bMvN A v 8 (by decide)
  · exact install_other bMvN A v 9 (by decide)
  · exact install_other bMvN A v 10 (by decide)

theorem dockH_bMvN (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH bMvN H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_slot bMvN bMvN_inj H v 0
  · exact dockH_other bMvN H v 1 (by decide)
  · exact dockH_other bMvN H v 2 (by decide)
  · exact dockH_other bMvN H v 3 (by decide)
  · exact dockH_other bMvN H v 4 (by decide)
  · exact dockH_other bMvN H v 5 (by decide)
  · exact dockH_other bMvN H v 6 (by decide)
  · exact dockH_other bMvN H v 7 (by decide)
  · exact dockH_other bMvN H v 8 (by decide)
  · exact dockH_other bMvN H v 9 (by decide)
  · exact dockH_other bMvN H v 10 (by decide)

theorem bMvS_inj : Function.Injective bMvS := by decide

theorem install_bMvS (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install bMvS A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other bMvS A v 0 (by decide)
  · exact install_slot bMvS bMvS_inj A v 0
  · exact install_other bMvS A v 2 (by decide)
  · exact install_other bMvS A v 3 (by decide)
  · exact install_other bMvS A v 4 (by decide)
  · exact install_other bMvS A v 5 (by decide)
  · exact install_other bMvS A v 6 (by decide)
  · exact install_other bMvS A v 7 (by decide)
  · exact install_other bMvS A v 8 (by decide)
  · exact install_other bMvS A v 9 (by decide)
  · exact install_other bMvS A v 10 (by decide)

theorem dockH_bMvS (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH bMvS H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other bMvS H v 0 (by decide)
  · exact dockH_slot bMvS bMvS_inj H v 0
  · exact dockH_other bMvS H v 2 (by decide)
  · exact dockH_other bMvS H v 3 (by decide)
  · exact dockH_other bMvS H v 4 (by decide)
  · exact dockH_other bMvS H v 5 (by decide)
  · exact dockH_other bMvS H v 6 (by decide)
  · exact dockH_other bMvS H v 7 (by decide)
  · exact dockH_other bMvS H v 8 (by decide)
  · exact dockH_other bMvS H v 9 (by decide)
  · exact dockH_other bMvS H v 10 (by decide)

theorem bMvF_inj : Function.Injective bMvF := by decide

theorem install_bMvF (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install bMvF A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other bMvF A v 0 (by decide)
  · exact install_other bMvF A v 1 (by decide)
  · exact install_slot bMvF bMvF_inj A v 0
  · exact install_other bMvF A v 3 (by decide)
  · exact install_other bMvF A v 4 (by decide)
  · exact install_other bMvF A v 5 (by decide)
  · exact install_other bMvF A v 6 (by decide)
  · exact install_other bMvF A v 7 (by decide)
  · exact install_other bMvF A v 8 (by decide)
  · exact install_other bMvF A v 9 (by decide)
  · exact install_other bMvF A v 10 (by decide)

theorem dockH_bMvF (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH bMvF H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other bMvF H v 0 (by decide)
  · exact dockH_other bMvF H v 1 (by decide)
  · exact dockH_slot bMvF bMvF_inj H v 0
  · exact dockH_other bMvF H v 3 (by decide)
  · exact dockH_other bMvF H v 4 (by decide)
  · exact dockH_other bMvF H v 5 (by decide)
  · exact dockH_other bMvF H v 6 (by decide)
  · exact dockH_other bMvF H v 7 (by decide)
  · exact dockH_other bMvF H v 8 (by decide)
  · exact dockH_other bMvF H v 9 (by decide)
  · exact dockH_other bMvF H v 10 (by decide)

theorem bEmPL_inj : Function.Injective bEmPL := by decide

theorem install_bEmPL (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bEmPL A v = ![A 0, A 1, A 2, v 0, A 4, v 1, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other bEmPL A v 0 (by decide)
  · exact install_other bEmPL A v 1 (by decide)
  · exact install_other bEmPL A v 2 (by decide)
  · exact install_slot bEmPL bEmPL_inj A v 0
  · exact install_other bEmPL A v 4 (by decide)
  · exact install_slot bEmPL bEmPL_inj A v 1
  · exact install_other bEmPL A v 6 (by decide)
  · exact install_other bEmPL A v 7 (by decide)
  · exact install_other bEmPL A v 8 (by decide)
  · exact install_other bEmPL A v 9 (by decide)
  · exact install_slot bEmPL bEmPL_inj A v 2

theorem dockH_bEmPL (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bEmPL H v = ![H 0, H 1, H 2, v 0, H 4, v 1, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bEmPL H v 0 (by decide)
  · exact dockH_other bEmPL H v 1 (by decide)
  · exact dockH_other bEmPL H v 2 (by decide)
  · exact dockH_slot bEmPL bEmPL_inj H v 0
  · exact dockH_other bEmPL H v 4 (by decide)
  · exact dockH_slot bEmPL bEmPL_inj H v 1
  · exact dockH_other bEmPL H v 6 (by decide)
  · exact dockH_other bEmPL H v 7 (by decide)
  · exact dockH_other bEmPL H v 8 (by decide)
  · exact dockH_other bEmPL H v 9 (by decide)
  · exact dockH_slot bEmPL bEmPL_inj H v 2

theorem bEmNL_inj : Function.Injective bEmNL := by decide

theorem install_bEmNL (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bEmNL A v = ![A 0, A 1, A 2, A 3, v 0, v 1, A 6, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other bEmNL A v 0 (by decide)
  · exact install_other bEmNL A v 1 (by decide)
  · exact install_other bEmNL A v 2 (by decide)
  · exact install_other bEmNL A v 3 (by decide)
  · exact install_slot bEmNL bEmNL_inj A v 0
  · exact install_slot bEmNL bEmNL_inj A v 1
  · exact install_other bEmNL A v 6 (by decide)
  · exact install_other bEmNL A v 7 (by decide)
  · exact install_other bEmNL A v 8 (by decide)
  · exact install_other bEmNL A v 9 (by decide)
  · exact install_slot bEmNL bEmNL_inj A v 2

theorem dockH_bEmNL (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bEmNL H v = ![H 0, H 1, H 2, H 3, v 0, v 1, H 6, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bEmNL H v 0 (by decide)
  · exact dockH_other bEmNL H v 1 (by decide)
  · exact dockH_other bEmNL H v 2 (by decide)
  · exact dockH_other bEmNL H v 3 (by decide)
  · exact dockH_slot bEmNL bEmNL_inj H v 0
  · exact dockH_slot bEmNL bEmNL_inj H v 1
  · exact dockH_other bEmNL H v 6 (by decide)
  · exact dockH_other bEmNL H v 7 (by decide)
  · exact dockH_other bEmNL H v 8 (by decide)
  · exact dockH_other bEmNL H v 9 (by decide)
  · exact dockH_slot bEmNL bEmNL_inj H v 2

theorem bEmPR_inj : Function.Injective bEmPR := by decide

theorem install_bEmPR (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bEmPR A v = ![A 0, A 1, A 2, v 0, A 4, A 5, v 1, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other bEmPR A v 0 (by decide)
  · exact install_other bEmPR A v 1 (by decide)
  · exact install_other bEmPR A v 2 (by decide)
  · exact install_slot bEmPR bEmPR_inj A v 0
  · exact install_other bEmPR A v 4 (by decide)
  · exact install_other bEmPR A v 5 (by decide)
  · exact install_slot bEmPR bEmPR_inj A v 1
  · exact install_other bEmPR A v 7 (by decide)
  · exact install_other bEmPR A v 8 (by decide)
  · exact install_other bEmPR A v 9 (by decide)
  · exact install_slot bEmPR bEmPR_inj A v 2

theorem dockH_bEmPR (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bEmPR H v = ![H 0, H 1, H 2, v 0, H 4, H 5, v 1, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bEmPR H v 0 (by decide)
  · exact dockH_other bEmPR H v 1 (by decide)
  · exact dockH_other bEmPR H v 2 (by decide)
  · exact dockH_slot bEmPR bEmPR_inj H v 0
  · exact dockH_other bEmPR H v 4 (by decide)
  · exact dockH_other bEmPR H v 5 (by decide)
  · exact dockH_slot bEmPR bEmPR_inj H v 1
  · exact dockH_other bEmPR H v 7 (by decide)
  · exact dockH_other bEmPR H v 8 (by decide)
  · exact dockH_other bEmPR H v 9 (by decide)
  · exact dockH_slot bEmPR bEmPR_inj H v 2

theorem bEmNR_inj : Function.Injective bEmNR := by decide

theorem install_bEmNR (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bEmNR A v = ![A 0, A 1, A 2, A 3, v 0, A 5, v 1, A 7, A 8, A 9, v 2] := by
  funext i
  fin_cases i
  · exact install_other bEmNR A v 0 (by decide)
  · exact install_other bEmNR A v 1 (by decide)
  · exact install_other bEmNR A v 2 (by decide)
  · exact install_other bEmNR A v 3 (by decide)
  · exact install_slot bEmNR bEmNR_inj A v 0
  · exact install_other bEmNR A v 5 (by decide)
  · exact install_slot bEmNR bEmNR_inj A v 1
  · exact install_other bEmNR A v 7 (by decide)
  · exact install_other bEmNR A v 8 (by decide)
  · exact install_other bEmNR A v 9 (by decide)
  · exact install_slot bEmNR bEmNR_inj A v 2

theorem dockH_bEmNR (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bEmNR H v = ![H 0, H 1, H 2, H 3, v 0, H 5, v 1, H 7, H 8, H 9, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bEmNR H v 0 (by decide)
  · exact dockH_other bEmNR H v 1 (by decide)
  · exact dockH_other bEmNR H v 2 (by decide)
  · exact dockH_other bEmNR H v 3 (by decide)
  · exact dockH_slot bEmNR bEmNR_inj H v 0
  · exact dockH_other bEmNR H v 5 (by decide)
  · exact dockH_slot bEmNR bEmNR_inj H v 1
  · exact dockH_other bEmNR H v 7 (by decide)
  · exact dockH_other bEmNR H v 8 (by decide)
  · exact dockH_other bEmNR H v 9 (by decide)
  · exact dockH_slot bEmNR bEmNR_inj H v 2

theorem bZipP_inj : Function.Injective bZipP := by decide

theorem install_bZipP (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install bZipP A v = ![A 0, A 1, A 2, A 3, v 1, A 5, A 6, v 0, A 8, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other bZipP A v 0 (by decide)
  · exact install_other bZipP A v 1 (by decide)
  · exact install_other bZipP A v 2 (by decide)
  · exact install_other bZipP A v 3 (by decide)
  · exact install_slot bZipP bZipP_inj A v 1
  · exact install_other bZipP A v 5 (by decide)
  · exact install_other bZipP A v 6 (by decide)
  · exact install_slot bZipP bZipP_inj A v 0
  · exact install_other bZipP A v 8 (by decide)
  · exact install_slot bZipP bZipP_inj A v 2
  · exact install_slot bZipP bZipP_inj A v 3

theorem dockH_bZipP (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH bZipP H v = ![H 0, H 1, H 2, H 3, v 1, H 5, H 6, v 0, H 8, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other bZipP H v 0 (by decide)
  · exact dockH_other bZipP H v 1 (by decide)
  · exact dockH_other bZipP H v 2 (by decide)
  · exact dockH_other bZipP H v 3 (by decide)
  · exact dockH_slot bZipP bZipP_inj H v 1
  · exact dockH_other bZipP H v 5 (by decide)
  · exact dockH_other bZipP H v 6 (by decide)
  · exact dockH_slot bZipP bZipP_inj H v 0
  · exact dockH_other bZipP H v 8 (by decide)
  · exact dockH_slot bZipP bZipP_inj H v 2
  · exact dockH_slot bZipP bZipP_inj H v 3

theorem bCpP_inj : Function.Injective bCpP := by decide

theorem install_bCpP (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bCpP A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 1, A 8, v 0, v 2] := by
  funext i
  fin_cases i
  · exact install_other bCpP A v 0 (by decide)
  · exact install_other bCpP A v 1 (by decide)
  · exact install_other bCpP A v 2 (by decide)
  · exact install_other bCpP A v 3 (by decide)
  · exact install_other bCpP A v 4 (by decide)
  · exact install_other bCpP A v 5 (by decide)
  · exact install_other bCpP A v 6 (by decide)
  · exact install_slot bCpP bCpP_inj A v 1
  · exact install_other bCpP A v 8 (by decide)
  · exact install_slot bCpP bCpP_inj A v 0
  · exact install_slot bCpP bCpP_inj A v 2

theorem dockH_bCpP (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bCpP H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 1, H 8, v 0, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bCpP H v 0 (by decide)
  · exact dockH_other bCpP H v 1 (by decide)
  · exact dockH_other bCpP H v 2 (by decide)
  · exact dockH_other bCpP H v 3 (by decide)
  · exact dockH_other bCpP H v 4 (by decide)
  · exact dockH_other bCpP H v 5 (by decide)
  · exact dockH_other bCpP H v 6 (by decide)
  · exact dockH_slot bCpP bCpP_inj H v 1
  · exact dockH_other bCpP H v 8 (by decide)
  · exact dockH_slot bCpP bCpP_inj H v 0
  · exact dockH_slot bCpP bCpP_inj H v 2

theorem bZipN_inj : Function.Injective bZipN := by decide

theorem install_bZipN (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install bZipN A v = ![A 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, v 0, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other bZipN A v 0 (by decide)
  · exact install_other bZipN A v 1 (by decide)
  · exact install_other bZipN A v 2 (by decide)
  · exact install_slot bZipN bZipN_inj A v 1
  · exact install_other bZipN A v 4 (by decide)
  · exact install_other bZipN A v 5 (by decide)
  · exact install_other bZipN A v 6 (by decide)
  · exact install_other bZipN A v 7 (by decide)
  · exact install_slot bZipN bZipN_inj A v 0
  · exact install_slot bZipN bZipN_inj A v 2
  · exact install_slot bZipN bZipN_inj A v 3

theorem dockH_bZipN (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH bZipN H v = ![H 0, H 1, H 2, v 1, H 4, H 5, H 6, H 7, v 0, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other bZipN H v 0 (by decide)
  · exact dockH_other bZipN H v 1 (by decide)
  · exact dockH_other bZipN H v 2 (by decide)
  · exact dockH_slot bZipN bZipN_inj H v 1
  · exact dockH_other bZipN H v 4 (by decide)
  · exact dockH_other bZipN H v 5 (by decide)
  · exact dockH_other bZipN H v 6 (by decide)
  · exact dockH_other bZipN H v 7 (by decide)
  · exact dockH_slot bZipN bZipN_inj H v 0
  · exact dockH_slot bZipN bZipN_inj H v 2
  · exact dockH_slot bZipN bZipN_inj H v 3

theorem bCpN_inj : Function.Injective bCpN := by decide

theorem install_bCpN (A : Fin 11 → List Bool) (v : Fin 3 → List Bool) :
    install bCpN A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact install_other bCpN A v 0 (by decide)
  · exact install_other bCpN A v 1 (by decide)
  · exact install_other bCpN A v 2 (by decide)
  · exact install_other bCpN A v 3 (by decide)
  · exact install_other bCpN A v 4 (by decide)
  · exact install_other bCpN A v 5 (by decide)
  · exact install_other bCpN A v 6 (by decide)
  · exact install_other bCpN A v 7 (by decide)
  · exact install_slot bCpN bCpN_inj A v 1
  · exact install_slot bCpN bCpN_inj A v 0
  · exact install_slot bCpN bCpN_inj A v 2

theorem dockH_bCpN (H : Fin 11 → ℕ) (v : Fin 3 → ℕ) :
    dockH bCpN H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 1, v 0, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other bCpN H v 0 (by decide)
  · exact dockH_other bCpN H v 1 (by decide)
  · exact dockH_other bCpN H v 2 (by decide)
  · exact dockH_other bCpN H v 3 (by decide)
  · exact dockH_other bCpN H v 4 (by decide)
  · exact dockH_other bCpN H v 5 (by decide)
  · exact dockH_other bCpN H v 6 (by decide)
  · exact dockH_other bCpN H v 7 (by decide)
  · exact dockH_slot bCpN bCpN_inj H v 1
  · exact dockH_slot bCpN bCpN_inj H v 0
  · exact dockH_slot bCpN bCpN_inj H v 2

/-- The coordinate body's heads: the children cursor, the side and flip heads, the two buffer cursors. -/
def pH (a sd fr oL oR : ℕ) : Fin 11 → ℕ := ![a, sd, fr, 0, 0, oL, oR, 0, 0, 0, 0]

/-- The coordinate body's tapes. -/
def pA (NM SD FR RP RN OL OR PA NA TM LG : List Bool) : Fin 11 → List Bool := ![NM, SD, FR, RP, RN, OL, OR, PA, NA, TM, LG]

/-- The cost of one register operation of width `h`. -/
def regCost (h : ℕ) : ℕ := 2 * (2 * h + 1) + 2

section Prims
variable (NM SD FR RP RN OL OR PA NA TM : List Bool) (a sd fr oL oR cap : ℕ)

theorem ps_loadP (pre w tail : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bLoadP loadM) (2 * (2 * w.length + 1) + 2) (pH pre.length sd fr oL oR)
      (pA (pre ++ frame w ++ tail) SD FR RP RN OL OR PA NA TM (List.replicate cap false))
      (pH (pre.length + 2 * w.length) sd fr oL oR)
      (pA (pre ++ frame w ++ tail) SD FR (overlay (frame w) RP) RN OL OR PA NA TM (List.replicate cap false)) := by
  have e := dockRun (loadStep pre w tail RP cap hcap) bLoadP bLoadP_inj (pH pre.length sd fr oL oR)
    (pA (pre ++ frame w ++ tail) SD FR RP RN OL OR PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bLoadP, dockH_bLoadP] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_loadN (pre w tail : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bLoadN loadM) (2 * (2 * w.length + 1) + 2) (pH pre.length sd fr oL oR)
      (pA (pre ++ frame w ++ tail) SD FR RP RN OL OR PA NA TM (List.replicate cap false))
      (pH (pre.length + 2 * w.length) sd fr oL oR)
      (pA (pre ++ frame w ++ tail) SD FR RP (overlay (frame w) RN) OL OR PA NA TM (List.replicate cap false)) := by
  have e := dockRun (loadStep pre w tail RN cap hcap) bLoadN bLoadN_inj (pH pre.length sd fr oL oR)
    (pA (pre ++ frame w ++ tail) SD FR RP RN OL OR PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bLoadN, dockH_bLoadN] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_mvN (LG : List Bool) :
    Step (RecoveryFocus.machine bMvN moveM) 1 (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
      (pH (a + 1) sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG) := by
  have e := dockRun (moveStep NM a) bMvN bMvN_inj (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_bMvN, dockH_bMvN] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_mvS (LG : List Bool) :
    Step (RecoveryFocus.machine bMvS moveM) 1 (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
      (pH a (sd + 1) fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG) := by
  have e := dockRun (moveStep SD sd) bMvS bMvS_inj (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_bMvS, dockH_bMvS] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_mvF (LG : List Bool) :
    Step (RecoveryFocus.machine bMvF moveM) 1 (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
      (pH a sd (fr + 1) oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG) := by
  have e := dockRun (moveStep FR fr) bMvF bMvF_inj (pH a sd fr oL oR) (pA NM SD FR RP RN OL OR PA NA TM LG)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_bMvF, dockH_bMvF] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

end Prims

section Emits
variable (NM SD FR PA NA TM : List Bool) (a sd fr cap : ℕ)

theorem ps_emPL (w t RN out BW OR : List Bool) (oR : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bEmPL emitM) (2 * (2 * w.length + 1) + 2) (pH a sd fr out.length oR)
      (pA NM SD FR (frame w ++ t) RN (overlay out BW) OR PA NA TM (List.replicate cap false))
      (pH a sd fr (out ++ frame w).length oR)
      (pA NM SD FR (frame w ++ t) RN (overlay (out ++ frame w) BW) OR PA NA TM (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) bEmPL bEmPL_inj (pH a sd fr out.length oR)
    (pA NM SD FR (frame w ++ t) RN (overlay out BW) OR PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bEmPL, dockH_bEmPL] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

theorem ps_emNL (w t RP out BW OR : List Bool) (oR : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bEmNL emitM) (2 * (2 * w.length + 1) + 2) (pH a sd fr out.length oR)
      (pA NM SD FR RP (frame w ++ t) (overlay out BW) OR PA NA TM (List.replicate cap false))
      (pH a sd fr (out ++ frame w).length oR)
      (pA NM SD FR RP (frame w ++ t) (overlay (out ++ frame w) BW) OR PA NA TM (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) bEmNL bEmNL_inj (pH a sd fr out.length oR)
    (pA NM SD FR RP (frame w ++ t) (overlay out BW) OR PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bEmNL, dockH_bEmNL] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

theorem ps_emPR (w t RN out BW OL : List Bool) (oL : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bEmPR emitM) (2 * (2 * w.length + 1) + 2) (pH a sd fr oL out.length)
      (pA NM SD FR (frame w ++ t) RN OL (overlay out BW) PA NA TM (List.replicate cap false))
      (pH a sd fr oL (out ++ frame w).length)
      (pA NM SD FR (frame w ++ t) RN OL (overlay (out ++ frame w) BW) PA NA TM (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) bEmPR bEmPR_inj (pH a sd fr oL out.length)
    (pA NM SD FR (frame w ++ t) RN OL (overlay out BW) PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bEmPR, dockH_bEmPR] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

theorem ps_emNR (w t RP out BW OL : List Bool) (oL : ℕ) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bEmNR emitM) (2 * (2 * w.length + 1) + 2) (pH a sd fr oL out.length)
      (pA NM SD FR RP (frame w ++ t) OL (overlay out BW) PA NA TM (List.replicate cap false))
      (pH a sd fr oL (out ++ frame w).length)
      (pA NM SD FR RP (frame w ++ t) OL (overlay (out ++ frame w) BW) PA NA TM (List.replicate cap false)) := by
  have e := dockRun (emitT w t out BW cap hcap) bEmNR bEmNR_inj (pH a sd fr oL out.length)
    (pA NM SD FR RP (frame w ++ t) OL (overlay out BW) PA NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bEmNR, dockH_bEmNR] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

end Emits

section Adds
variable (NM SD FR OL OR : List Bool) (a sd fr oL oR cap : ℕ)

theorem ps_zipP (u tu RP v tv NA TM : List Bool) (hl : u.length = v.length) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bZipP (zipM addOut addNxt false)) (2 * (2 * u.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR RP (frame v ++ tv) OL OR (frame u ++ tu) NA TM (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR RP (frame v ++ tv) OL OR (frame u ++ tu) NA
        (overlay (frame (ZipMap.map addOut addNxt u v false)) TM) (List.replicate cap false)) := by
  have e := dockRun (zipT addOut addNxt false u v tu tv TM hl cap hcap) bZipP bZipP_inj (pH a sd fr oL oR)
    (pA NM SD FR RP (frame v ++ tv) OL OR (frame u ++ tu) NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bZipP, dockH_bZipP] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_zipN (u tu RN v tv PA TM : List Bool) (hl : u.length = v.length) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bZipN (zipM addOut addNxt false)) (2 * (2 * u.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR (frame v ++ tv) RN OL OR PA (frame u ++ tu) TM (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR (frame v ++ tv) RN OL OR PA (frame u ++ tu)
        (overlay (frame (ZipMap.map addOut addNxt u v false)) TM) (List.replicate cap false)) := by
  have e := dockRun (zipT addOut addNxt false u v tu tv TM hl cap hcap) bZipN bZipN_inj (pH a sd fr oL oR)
    (pA NM SD FR (frame v ++ tv) RN OL OR PA (frame u ++ tu) TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bZipN, dockH_bZipN] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_cpP (w t RP RN PA NA : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bCpP regCopyM) (2 * (2 * w.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR RP RN OL OR PA NA (frame w ++ t) (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR RP RN OL OR (overlay (frame w) PA) NA (frame w ++ t) (List.replicate cap false)) := by
  have e := dockRun (regCopyStep w t PA cap hcap) bCpP bCpP_inj (pH a sd fr oL oR)
    (pA NM SD FR RP RN OL OR PA NA (frame w ++ t) (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bCpP, dockH_bCpP] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_cpN (w t RP RN PA NA : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bCpN regCopyM) (2 * (2 * w.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR RP RN OL OR PA NA (frame w ++ t) (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR RP RN OL OR PA (overlay (frame w) NA) (frame w ++ t) (List.replicate cap false)) := by
  have e := dockRun (regCopyStep w t NA cap hcap) bCpN bCpN_inj (pH a sd fr oL oR)
    (pA NM SD FR RP RN OL OR PA NA (frame w ++ t) (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bCpN, dockH_bCpN] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

end Adds

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
