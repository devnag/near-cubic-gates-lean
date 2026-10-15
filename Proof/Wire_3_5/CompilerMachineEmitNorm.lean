import Proof.Wire_3_5.CompilerMachineEmitKit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The comparison with every head back at cell `0` (log on tape 3). -/
noncomputable def cmpM := MaskedReset.machine Compare.machine ![true, true, true]

theorem cmpMStep (u v tu tv : List Bool) (hl : u.length = v.length) (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) :
    Step cmpM (2 * (2 * u.length + 1) + 2) ![0, 0, 0, 0] ![frame u ++ tu, frame v ++ tv, [false], List.replicate cap false]
      ![0, 0, 0, 0] ![frame u ++ tu, frame v ++ tv, [decide (value u ≤ value v)], List.replicate cap false] := by
  have h0 := cmpStep u v tu tv hl
  have hm := h0.mask ![true, true, true] (by intro i _; fin_cases i <;> rfl) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

def nCmp : Fin 4 → Fin 6 := ![1, 0, 3, 5]
def nSubP : Fin 4 → Fin 6 := ![0, 1, 2, 5]
def nSubN : Fin 4 → Fin 6 := ![1, 0, 2, 5]
def nPut : Fin 1 → Fin 6 := ![4]
def nEm : Fin 3 → Fin 6 := ![2, 4, 5]
def nClr : Fin 1 → Fin 6 := ![3]

theorem nCmp_inj : Function.Injective nCmp := by decide

theorem install_nCmp (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    install nCmp A v = ![v 1, v 0, A 2, v 2, A 4, v 3] := by
  funext i
  fin_cases i
  · exact install_slot nCmp nCmp_inj A v 1
  · exact install_slot nCmp nCmp_inj A v 0
  · exact install_other nCmp A v 2 (by decide)
  · exact install_slot nCmp nCmp_inj A v 2
  · exact install_other nCmp A v 4 (by decide)
  · exact install_slot nCmp nCmp_inj A v 3

theorem dockH_nCmp (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH nCmp H v = ![v 1, v 0, H 2, v 2, H 4, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot nCmp nCmp_inj H v 1
  · exact dockH_slot nCmp nCmp_inj H v 0
  · exact dockH_other nCmp H v 2 (by decide)
  · exact dockH_slot nCmp nCmp_inj H v 2
  · exact dockH_other nCmp H v 4 (by decide)
  · exact dockH_slot nCmp nCmp_inj H v 3

theorem nSubP_inj : Function.Injective nSubP := by decide

theorem install_nSubP (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    install nSubP A v = ![v 0, v 1, v 2, A 3, A 4, v 3] := by
  funext i
  fin_cases i
  · exact install_slot nSubP nSubP_inj A v 0
  · exact install_slot nSubP nSubP_inj A v 1
  · exact install_slot nSubP nSubP_inj A v 2
  · exact install_other nSubP A v 3 (by decide)
  · exact install_other nSubP A v 4 (by decide)
  · exact install_slot nSubP nSubP_inj A v 3

theorem dockH_nSubP (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH nSubP H v = ![v 0, v 1, v 2, H 3, H 4, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot nSubP nSubP_inj H v 0
  · exact dockH_slot nSubP nSubP_inj H v 1
  · exact dockH_slot nSubP nSubP_inj H v 2
  · exact dockH_other nSubP H v 3 (by decide)
  · exact dockH_other nSubP H v 4 (by decide)
  · exact dockH_slot nSubP nSubP_inj H v 3

theorem nSubN_inj : Function.Injective nSubN := by decide

theorem install_nSubN (A : Fin 6 → List Bool) (v : Fin 4 → List Bool) :
    install nSubN A v = ![v 1, v 0, v 2, A 3, A 4, v 3] := by
  funext i
  fin_cases i
  · exact install_slot nSubN nSubN_inj A v 1
  · exact install_slot nSubN nSubN_inj A v 0
  · exact install_slot nSubN nSubN_inj A v 2
  · exact install_other nSubN A v 3 (by decide)
  · exact install_other nSubN A v 4 (by decide)
  · exact install_slot nSubN nSubN_inj A v 3

theorem dockH_nSubN (H : Fin 6 → ℕ) (v : Fin 4 → ℕ) :
    dockH nSubN H v = ![v 1, v 0, v 2, H 3, H 4, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot nSubN nSubN_inj H v 1
  · exact dockH_slot nSubN nSubN_inj H v 0
  · exact dockH_slot nSubN nSubN_inj H v 2
  · exact dockH_other nSubN H v 3 (by decide)
  · exact dockH_other nSubN H v 4 (by decide)
  · exact dockH_slot nSubN nSubN_inj H v 3

theorem nPut_inj : Function.Injective nPut := by decide

theorem install_nPut (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    install nPut A v = ![A 0, A 1, A 2, A 3, v 0, A 5] := by
  funext i
  fin_cases i
  · exact install_other nPut A v 0 (by decide)
  · exact install_other nPut A v 1 (by decide)
  · exact install_other nPut A v 2 (by decide)
  · exact install_other nPut A v 3 (by decide)
  · exact install_slot nPut nPut_inj A v 0
  · exact install_other nPut A v 5 (by decide)

theorem dockH_nPut (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH nPut H v = ![H 0, H 1, H 2, H 3, v 0, H 5] := by
  funext i
  fin_cases i
  · exact dockH_other nPut H v 0 (by decide)
  · exact dockH_other nPut H v 1 (by decide)
  · exact dockH_other nPut H v 2 (by decide)
  · exact dockH_other nPut H v 3 (by decide)
  · exact dockH_slot nPut nPut_inj H v 0
  · exact dockH_other nPut H v 5 (by decide)

theorem nEm_inj : Function.Injective nEm := by decide

theorem install_nEm (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    install nEm A v = ![A 0, A 1, v 0, A 3, v 1, v 2] := by
  funext i
  fin_cases i
  · exact install_other nEm A v 0 (by decide)
  · exact install_other nEm A v 1 (by decide)
  · exact install_slot nEm nEm_inj A v 0
  · exact install_other nEm A v 3 (by decide)
  · exact install_slot nEm nEm_inj A v 1
  · exact install_slot nEm nEm_inj A v 2

theorem dockH_nEm (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH nEm H v = ![H 0, H 1, v 0, H 3, v 1, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other nEm H v 0 (by decide)
  · exact dockH_other nEm H v 1 (by decide)
  · exact dockH_slot nEm nEm_inj H v 0
  · exact dockH_other nEm H v 3 (by decide)
  · exact dockH_slot nEm nEm_inj H v 1
  · exact dockH_slot nEm nEm_inj H v 2

theorem nClr_inj : Function.Injective nClr := by decide

theorem install_nClr (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    install nClr A v = ![A 0, A 1, A 2, v 0, A 4, A 5] := by
  funext i
  fin_cases i
  · exact install_other nClr A v 0 (by decide)
  · exact install_other nClr A v 1 (by decide)
  · exact install_other nClr A v 2 (by decide)
  · exact install_slot nClr nClr_inj A v 0
  · exact install_other nClr A v 4 (by decide)
  · exact install_other nClr A v 5 (by decide)

theorem dockH_nClr (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH nClr H v = ![H 0, H 1, H 2, v 0, H 4, H 5] := by
  funext i
  fin_cases i
  · exact dockH_other nClr H v 0 (by decide)
  · exact dockH_other nClr H v 1 (by decide)
  · exact dockH_other nClr H v 2 (by decide)
  · exact dockH_slot nClr nClr_inj H v 0
  · exact dockH_other nClr H v 4 (by decide)
  · exact dockH_other nClr H v 5 (by decide)

noncomputable def nCmpD := RecoveryFocus.machine nCmp cmpM
noncomputable def nSubPD := RecoveryFocus.machine nSubP (zipM subOut subNxt true)
noncomputable def nSubND := RecoveryFocus.machine nSubN (zipM subOut subNxt true)
noncomputable def nPutTD := RecoveryFocus.machine nPut (putM true)
noncomputable def nPutFD := RecoveryFocus.machine nPut (putM false)
noncomputable def nEmD := RecoveryFocus.machine nEm emitM
noncomputable def nClrD := RecoveryFocus.machine nClr (cellM false)
/-- `y ≤ x`: `x − y`, sign `false`. -/
noncomputable def normPos := Composition.machine nSubPD (Composition.machine nPutTD (Composition.machine nPutFD nEmD))
/-- `x < y`: `y − x`, sign `true`. -/
noncomputable def normNeg := Composition.machine nSubND (Composition.machine nPutTD (Composition.machine nPutTD nEmD))
/-- **One P/N pair as a signed field**: compare, branch, clear the cell. -/
noncomputable def normM := Composition.machine nCmpD (Composition.machine (branchM 3 normPos normNeg) nClrD)

/-- The normalize layout's heads (the output cursor only moves). -/
def nH (o : ℕ) : Fin 6 → ℕ := ![0, 0, 0, 0, o, 0]

/-- The normalize layout's tapes. -/
def nA (RP RN RD CMP O LG : List Bool) : Fin 6 → List Bool := ![RP, RN, RD, CMP, O, LG]

/-- The cost of one signed field of width `W`. -/
def normCost (W : ℕ) : ℕ :=
  (2 * (2 * W + 1) + 2) + 1 + (((2 * (2 * W + 1) + 2) + 1 + (1 + 1 + (1 + 1 + (2 * (2 * W + 1) + 2))) + 2) + 1 + 1)

theorem frame_sm_pos (W : ℕ) (x y : ℕ) (hyx : y ≤ x) :
    frame (signMagnitude W ((x : ℤ) - y)) = true :: false :: frame (binary W (x - y)) := by
  unfold signMagnitude
  rw [decide_eq_false (by omega), show ((x : ℤ) - y).natAbs = x - y by omega]
  rfl

theorem frame_sm_neg (W : ℕ) (x y : ℕ) (hyx : ¬ y ≤ x) :
    frame (signMagnitude W ((x : ℤ) - y)) = true :: true :: frame (binary W (y - x)) := by
  unfold signMagnitude
  rw [decide_eq_true (by omega), show ((x : ℤ) - y).natAbs = y - x by omega]
  rfl

/-- **One P/N pair as the request's signed field**: from `binary W x` and `binary W y` the machine
writes `frame (signMagnitude W (x − y))` at the output cursor; the magnitude register ends holding `|x − y|`. -/
theorem norm_step (W x y : ℕ) (hx : x < 2 ^ W) (hy : y < 2 ^ W) (tp tn YD out BW : List Bool) (cap : ℕ)
    (hcap : 2 * W + 1 ≤ cap) :
    Step normM (normCost W) (nH out.length)
      (nA (frame (binary W x) ++ tp) (frame (binary W y) ++ tn) YD [false] (overlay out BW) (List.replicate cap false))
      (nH (out ++ frame (signMagnitude W ((x : ℤ) - y))).length)
      (nA (frame (binary W x) ++ tp) (frame (binary W y) ++ tn) (overlay (frame (binary W ((x : ℤ) - y).natAbs)) YD)
        [false] (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW) (List.replicate cap false)) := by
  set RP := frame (binary W x) ++ tp
  set RN := frame (binary W y) ++ tn
  have e1 := dockRun (cmpMStep (binary W y) (binary W x) tn tp (by simp) cap (by simp; omega)) nCmp nCmp_inj
    (nH out.length) (nA RP RN YD [false] (overlay out BW) (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_nCmp, dockH_nCmp, binary_value W y hy, binary_value W x hx] at e1
  have e1' : Step nCmpD (2 * (2 * W + 1) + 2) (nH out.length)
      (nA RP RN YD [false] (overlay out BW) (List.replicate cap false)) (nH out.length)
      (nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) := by
    refine (e1.congr ?_ ?_).enlarge (by simp)
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have ec : ∀ c : Bool, Step nClrD 1 (nH (out ++ frame (signMagnitude W ((x : ℤ) - y))).length)
      (nA RP RN (overlay (frame (binary W ((x : ℤ) - y).natAbs)) YD) [c]
        (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW) (List.replicate cap false))
      (nH (out ++ frame (signMagnitude W ((x : ℤ) - y))).length)
      (nA RP RN (overlay (frame (binary W ((x : ℤ) - y).natAbs)) YD) [false]
        (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW) (List.replicate cap false)) := by
    intro c
    have e := dockRun (cellStep false c) nClr nClr_inj (nH (out ++ frame (signMagnitude W ((x : ℤ) - y))).length)
      (nA RP RN (overlay (frame (binary W ((x : ℤ) - y).natAbs)) YD) [c]
        (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW) (List.replicate cap false))
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [install_nClr, dockH_nClr] at e
    exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  by_cases hyx : y ≤ x
  · -- positive arm
    have z0 := zipT subOut subNxt true (binary W x) (binary W y) tp tn YD (by simp) cap (by simp; omega)
    rw [map_sub W x y hx hyx, binary_length] at z0
    have z1 := dockRun z0 nSubP nSubP_inj (nH out.length)
      (nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false))
      (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    rw [install_nSubP, dockH_nSubP] at z1
    have z : Step nSubPD (2 * (2 * W + 1) + 2) (nH out.length)
        (nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) (nH out.length)
        (nA RP RN (overlay (frame (binary W (x - y))) YD) [decide (y ≤ x)] (overlay out BW)
          (List.replicate cap false)) :=
      z1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
    set D := overlay (frame (binary W (x - y))) YD with hD
    have p1 := dockRun (putStep true (overlay out BW) out.length) nPut nPut_inj (nH out.length)
      (nA RP RN D [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) (by intro k; fin_cases k; rfl)
      (by intro k; fin_cases k; rfl)
    rw [install_nPut, dockH_nPut, overlay_write] at p1
    have p2 := dockRun (putStep false (overlay (out ++ [true]) BW) (out ++ [true]).length) nPut nPut_inj
      (nH (out ++ [true]).length) (nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true]) BW) (List.replicate cap false))
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [install_nPut, dockH_nPut, overlay_write] at p2
    have em := dockRun (emitT (binary W (x - y)) (YD.drop (frame (binary W (x - y))).length) (out ++ [true] ++ [false]) BW
      cap (by simp; omega)) nEm nEm_inj (nH (out ++ [true] ++ [false]).length)
      (nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true] ++ [false]) BW) (List.replicate cap false))
      (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    rw [install_nEm, dockH_nEm, binary_length] at em
    have hbit : readTapeBit ((nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) 3)
        ((nH out.length) 3) = true := by simp [nA, nH, readTapeBit, hyx]
    have p1' := p1.congr (hout' := nH (out ++ [true]).length) (by funext i; fin_cases i <;> simp [nH]) rfl
    have p2' := p2.congr (hout' := nH (out ++ [true] ++ [false]).length) (by funext i; fin_cases i <;> simp [nH]) rfl
    have em' := em.congr (hout' := nH (out ++ [true] ++ [false] ++ frame (binary W (x - y))).length)
      (tout' := nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true] ++ [false] ++ frame (binary W (x - y))) BW)
        (List.replicate cap false))
      (by funext i; fin_cases i <;> simp [nH]; omega) (by funext i; fin_cases i <;> rfl)
    have pos := z.seq (p1'.seq (p2'.seq em'))
    have br := branch_true (3 : Fin 6) normNeg pos hbit
    have hw : out ++ [true] ++ [false] ++ frame (binary W (x - y)) = out ++ frame (signMagnitude W ((x : ℤ) - y)) := by
      rw [frame_sm_pos W x y hyx]; simp
    have hn : ((x : ℤ) - y).natAbs = x - y := by omega
    rw [hw, hD] at br
    rw [← hn] at br
    have j := e1'.seq (br.seq (ec (decide (y ≤ x))))
    exact j.enlarge (le_of_eq (by unfold normCost; ring))
  · -- negative arm
    have z0 := zipT subOut subNxt true (binary W y) (binary W x) tn tp YD (by simp) cap (by simp; omega)
    rw [map_sub W y x hy (by omega), binary_length] at z0
    have z1 := dockRun z0 nSubN nSubN_inj (nH out.length)
      (nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false))
      (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    rw [install_nSubN, dockH_nSubN] at z1
    have z : Step nSubND (2 * (2 * W + 1) + 2) (nH out.length)
        (nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) (nH out.length)
        (nA RP RN (overlay (frame (binary W (y - x))) YD) [decide (y ≤ x)] (overlay out BW)
          (List.replicate cap false)) :=
      z1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
    set D := overlay (frame (binary W (y - x))) YD with hD
    have p1 := dockRun (putStep true (overlay out BW) out.length) nPut nPut_inj (nH out.length)
      (nA RP RN D [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) (by intro k; fin_cases k; rfl)
      (by intro k; fin_cases k; rfl)
    rw [install_nPut, dockH_nPut, overlay_write] at p1
    have p2 := dockRun (putStep true (overlay (out ++ [true]) BW) (out ++ [true]).length) nPut nPut_inj
      (nH (out ++ [true]).length) (nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true]) BW) (List.replicate cap false))
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [install_nPut, dockH_nPut, overlay_write] at p2
    have em := dockRun (emitT (binary W (y - x)) (YD.drop (frame (binary W (y - x))).length) (out ++ [true] ++ [true]) BW
      cap (by simp; omega)) nEm nEm_inj (nH (out ++ [true] ++ [true]).length)
      (nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true] ++ [true]) BW) (List.replicate cap false))
      (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    rw [install_nEm, dockH_nEm, binary_length] at em
    have hbit : readTapeBit ((nA RP RN YD [decide (y ≤ x)] (overlay out BW) (List.replicate cap false)) 3)
        ((nH out.length) 3) = false := by simp [nA, nH, readTapeBit, hyx]
    have p1' := p1.congr (hout' := nH (out ++ [true]).length) (by funext i; fin_cases i <;> simp [nH]) rfl
    have p2' := p2.congr (hout' := nH (out ++ [true] ++ [true]).length) (by funext i; fin_cases i <;> simp [nH]) rfl
    have em' := em.congr (hout' := nH (out ++ [true] ++ [true] ++ frame (binary W (y - x))).length)
      (tout' := nA RP RN D [decide (y ≤ x)] (overlay (out ++ [true] ++ [true] ++ frame (binary W (y - x))) BW)
        (List.replicate cap false))
      (by funext i; fin_cases i <;> simp [nH]; omega) (by funext i; fin_cases i <;> rfl)
    have neg := z.seq (p1'.seq (p2'.seq em'))
    have br := branch_false (3 : Fin 6) normPos neg hbit
    have hw : out ++ [true] ++ [true] ++ frame (binary W (y - x)) = out ++ frame (signMagnitude W ((x : ℤ) - y)) := by
      rw [frame_sm_neg W x y hyx]; simp
    have hn : ((x : ℤ) - y).natAbs = y - x := by omega
    rw [hw, hD] at br
    rw [← hn] at br
    have j := e1'.seq (br.seq (ec (decide (y ≤ x))))
    exact j.enlarge (le_of_eq (by unfold normCost; ring))

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
