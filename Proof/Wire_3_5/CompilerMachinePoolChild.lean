import Proof.Wire_3_5.CompilerMachinePoolAppend

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Stale registers collapse -/

theorem frame_len_eq (h x y : ℕ) : (frame (binary h x)).length = (frame (binary h y)).length := by simp

theorem fold_collapse_rp (h x : ℕ) : ∀ (cs : List Coord) (st : CoordSt),
    overlay (frame (binary h x)) (cs.foldl (cstep h) st).rp = overlay (frame (binary h x)) st.rp
  | [], _ => rfl
  | c :: cs, st => by
    rw [List.foldl_cons, fold_collapse_rp h x cs]
    exact overlay_collapse _ _ _ (frame_len_eq h _ _)

theorem fold_collapse_rn (h x : ℕ) : ∀ (cs : List Coord) (st : CoordSt),
    overlay (frame (binary h x)) (cs.foldl (cstep h) st).rn = overlay (frame (binary h x)) st.rn
  | [], _ => rfl
  | c :: cs, st => by
    rw [List.foldl_cons, fold_collapse_rn h x cs]
    exact overlay_collapse _ _ _ (frame_len_eq h _ _)

theorem fold_collapse_tmp (h x : ℕ) : ∀ (cs : List Coord) (st : CoordSt),
    overlay (frame (binary h x)) (cs.foldl (cstep h) st).tmp = overlay (frame (binary h x)) st.tmp
  | [], _ => rfl
  | c :: cs, st => by
    rw [List.foldl_cons, fold_collapse_tmp h x cs]
    show overlay (frame (binary h x)) (tmpAfter h c.2.1 st.P st.N (pn c.2.2).1 (pn c.2.2).2 st.tmp) = _
    unfold tmpAfter
    split_ifs
    · rw [overlay_collapse _ _ _ (frame_len_eq h _ _), overlay_collapse _ _ _ (frame_len_eq h _ _)]
    · rfl

/-! ## The child pass (tapes: 0-10 the coordinate layout, 11 its loop log, 12 the zero register, 13-14 the zero
padding streams, 15 the pool stream, 16 the append log) -/

def kInitP : Fin 3 → Fin 17 := ![12, 7, 10]
def kInitN : Fin 3 → Fin 17 := ![12, 8, 10]
def kLoop : Fin 12 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def kTgt : Fin 11 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def kApp : Fin 6 → Fin 17 := ![15, 5, 13, 6, 14, 16]
def kEmP : Fin 3 → Fin 17 := ![7, 15, 10]
def kEmN : Fin 3 → Fin 17 := ![8, 15, 10]

theorem kInitP_inj : Function.Injective kInitP := by decide

theorem install_kInitP (A : Fin 17 → List Bool) (v : Fin 3 → List Bool) :
    install kInitP A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 1, A 8, A 9, v 2, A 11, v 0, A 13, A 14, A 15, A 16] := by
  funext i
  fin_cases i
  · exact install_other kInitP A v 0 (by decide)
  · exact install_other kInitP A v 1 (by decide)
  · exact install_other kInitP A v 2 (by decide)
  · exact install_other kInitP A v 3 (by decide)
  · exact install_other kInitP A v 4 (by decide)
  · exact install_other kInitP A v 5 (by decide)
  · exact install_other kInitP A v 6 (by decide)
  · exact install_slot kInitP kInitP_inj A v 1
  · exact install_other kInitP A v 8 (by decide)
  · exact install_other kInitP A v 9 (by decide)
  · exact install_slot kInitP kInitP_inj A v 2
  · exact install_other kInitP A v 11 (by decide)
  · exact install_slot kInitP kInitP_inj A v 0
  · exact install_other kInitP A v 13 (by decide)
  · exact install_other kInitP A v 14 (by decide)
  · exact install_other kInitP A v 15 (by decide)
  · exact install_other kInitP A v 16 (by decide)

theorem dockH_kInitP (H : Fin 17 → ℕ) (v : Fin 3 → ℕ) :
    dockH kInitP H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 1, H 8, H 9, v 2, H 11, v 0, H 13, H 14, H 15, H 16] := by
  funext i
  fin_cases i
  · exact dockH_other kInitP H v 0 (by decide)
  · exact dockH_other kInitP H v 1 (by decide)
  · exact dockH_other kInitP H v 2 (by decide)
  · exact dockH_other kInitP H v 3 (by decide)
  · exact dockH_other kInitP H v 4 (by decide)
  · exact dockH_other kInitP H v 5 (by decide)
  · exact dockH_other kInitP H v 6 (by decide)
  · exact dockH_slot kInitP kInitP_inj H v 1
  · exact dockH_other kInitP H v 8 (by decide)
  · exact dockH_other kInitP H v 9 (by decide)
  · exact dockH_slot kInitP kInitP_inj H v 2
  · exact dockH_other kInitP H v 11 (by decide)
  · exact dockH_slot kInitP kInitP_inj H v 0
  · exact dockH_other kInitP H v 13 (by decide)
  · exact dockH_other kInitP H v 14 (by decide)
  · exact dockH_other kInitP H v 15 (by decide)
  · exact dockH_other kInitP H v 16 (by decide)

theorem kInitN_inj : Function.Injective kInitN := by decide

theorem install_kInitN (A : Fin 17 → List Bool) (v : Fin 3 → List Bool) :
    install kInitN A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 1, A 9, v 2, A 11, v 0, A 13, A 14, A 15, A 16] := by
  funext i
  fin_cases i
  · exact install_other kInitN A v 0 (by decide)
  · exact install_other kInitN A v 1 (by decide)
  · exact install_other kInitN A v 2 (by decide)
  · exact install_other kInitN A v 3 (by decide)
  · exact install_other kInitN A v 4 (by decide)
  · exact install_other kInitN A v 5 (by decide)
  · exact install_other kInitN A v 6 (by decide)
  · exact install_other kInitN A v 7 (by decide)
  · exact install_slot kInitN kInitN_inj A v 1
  · exact install_other kInitN A v 9 (by decide)
  · exact install_slot kInitN kInitN_inj A v 2
  · exact install_other kInitN A v 11 (by decide)
  · exact install_slot kInitN kInitN_inj A v 0
  · exact install_other kInitN A v 13 (by decide)
  · exact install_other kInitN A v 14 (by decide)
  · exact install_other kInitN A v 15 (by decide)
  · exact install_other kInitN A v 16 (by decide)

theorem dockH_kInitN (H : Fin 17 → ℕ) (v : Fin 3 → ℕ) :
    dockH kInitN H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 1, H 9, v 2, H 11, v 0, H 13, H 14, H 15, H 16] := by
  funext i
  fin_cases i
  · exact dockH_other kInitN H v 0 (by decide)
  · exact dockH_other kInitN H v 1 (by decide)
  · exact dockH_other kInitN H v 2 (by decide)
  · exact dockH_other kInitN H v 3 (by decide)
  · exact dockH_other kInitN H v 4 (by decide)
  · exact dockH_other kInitN H v 5 (by decide)
  · exact dockH_other kInitN H v 6 (by decide)
  · exact dockH_other kInitN H v 7 (by decide)
  · exact dockH_slot kInitN kInitN_inj H v 1
  · exact dockH_other kInitN H v 9 (by decide)
  · exact dockH_slot kInitN kInitN_inj H v 2
  · exact dockH_other kInitN H v 11 (by decide)
  · exact dockH_slot kInitN kInitN_inj H v 0
  · exact dockH_other kInitN H v 13 (by decide)
  · exact dockH_other kInitN H v 14 (by decide)
  · exact dockH_other kInitN H v 15 (by decide)
  · exact dockH_other kInitN H v 16 (by decide)

theorem kLoop_inj : Function.Injective kLoop := by decide

theorem install_kLoop (A : Fin 17 → List Bool) (v : Fin 12 → List Bool) :
    install kLoop A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, A 12, A 13, A 14, A 15, A 16] := by
  funext i
  fin_cases i
  · exact install_slot kLoop kLoop_inj A v 0
  · exact install_slot kLoop kLoop_inj A v 1
  · exact install_slot kLoop kLoop_inj A v 2
  · exact install_slot kLoop kLoop_inj A v 3
  · exact install_slot kLoop kLoop_inj A v 4
  · exact install_slot kLoop kLoop_inj A v 5
  · exact install_slot kLoop kLoop_inj A v 6
  · exact install_slot kLoop kLoop_inj A v 7
  · exact install_slot kLoop kLoop_inj A v 8
  · exact install_slot kLoop kLoop_inj A v 9
  · exact install_slot kLoop kLoop_inj A v 10
  · exact install_slot kLoop kLoop_inj A v 11
  · exact install_other kLoop A v 12 (by decide)
  · exact install_other kLoop A v 13 (by decide)
  · exact install_other kLoop A v 14 (by decide)
  · exact install_other kLoop A v 15 (by decide)
  · exact install_other kLoop A v 16 (by decide)

theorem dockH_kLoop (H : Fin 17 → ℕ) (v : Fin 12 → ℕ) :
    dockH kLoop H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, H 12, H 13, H 14, H 15, H 16] := by
  funext i
  fin_cases i
  · exact dockH_slot kLoop kLoop_inj H v 0
  · exact dockH_slot kLoop kLoop_inj H v 1
  · exact dockH_slot kLoop kLoop_inj H v 2
  · exact dockH_slot kLoop kLoop_inj H v 3
  · exact dockH_slot kLoop kLoop_inj H v 4
  · exact dockH_slot kLoop kLoop_inj H v 5
  · exact dockH_slot kLoop kLoop_inj H v 6
  · exact dockH_slot kLoop kLoop_inj H v 7
  · exact dockH_slot kLoop kLoop_inj H v 8
  · exact dockH_slot kLoop kLoop_inj H v 9
  · exact dockH_slot kLoop kLoop_inj H v 10
  · exact dockH_slot kLoop kLoop_inj H v 11
  · exact dockH_other kLoop H v 12 (by decide)
  · exact dockH_other kLoop H v 13 (by decide)
  · exact dockH_other kLoop H v 14 (by decide)
  · exact dockH_other kLoop H v 15 (by decide)
  · exact dockH_other kLoop H v 16 (by decide)

theorem kTgt_inj : Function.Injective kTgt := by decide

theorem install_kTgt (A : Fin 17 → List Bool) (v : Fin 11 → List Bool) :
    install kTgt A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, A 11, A 12, A 13, A 14, A 15, A 16] := by
  funext i
  fin_cases i
  · exact install_slot kTgt kTgt_inj A v 0
  · exact install_slot kTgt kTgt_inj A v 1
  · exact install_slot kTgt kTgt_inj A v 2
  · exact install_slot kTgt kTgt_inj A v 3
  · exact install_slot kTgt kTgt_inj A v 4
  · exact install_slot kTgt kTgt_inj A v 5
  · exact install_slot kTgt kTgt_inj A v 6
  · exact install_slot kTgt kTgt_inj A v 7
  · exact install_slot kTgt kTgt_inj A v 8
  · exact install_slot kTgt kTgt_inj A v 9
  · exact install_slot kTgt kTgt_inj A v 10
  · exact install_other kTgt A v 11 (by decide)
  · exact install_other kTgt A v 12 (by decide)
  · exact install_other kTgt A v 13 (by decide)
  · exact install_other kTgt A v 14 (by decide)
  · exact install_other kTgt A v 15 (by decide)
  · exact install_other kTgt A v 16 (by decide)

theorem dockH_kTgt (H : Fin 17 → ℕ) (v : Fin 11 → ℕ) :
    dockH kTgt H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, H 11, H 12, H 13, H 14, H 15, H 16] := by
  funext i
  fin_cases i
  · exact dockH_slot kTgt kTgt_inj H v 0
  · exact dockH_slot kTgt kTgt_inj H v 1
  · exact dockH_slot kTgt kTgt_inj H v 2
  · exact dockH_slot kTgt kTgt_inj H v 3
  · exact dockH_slot kTgt kTgt_inj H v 4
  · exact dockH_slot kTgt kTgt_inj H v 5
  · exact dockH_slot kTgt kTgt_inj H v 6
  · exact dockH_slot kTgt kTgt_inj H v 7
  · exact dockH_slot kTgt kTgt_inj H v 8
  · exact dockH_slot kTgt kTgt_inj H v 9
  · exact dockH_slot kTgt kTgt_inj H v 10
  · exact dockH_other kTgt H v 11 (by decide)
  · exact dockH_other kTgt H v 12 (by decide)
  · exact dockH_other kTgt H v 13 (by decide)
  · exact dockH_other kTgt H v 14 (by decide)
  · exact dockH_other kTgt H v 15 (by decide)
  · exact dockH_other kTgt H v 16 (by decide)

theorem kApp_inj : Function.Injective kApp := by decide

theorem install_kApp (A : Fin 17 → List Bool) (v : Fin 6 → List Bool) :
    install kApp A v = ![A 0, A 1, A 2, A 3, A 4, v 1, v 3, A 7, A 8, A 9, A 10, A 11, A 12, v 2, v 4, v 0, v 5] := by
  funext i
  fin_cases i
  · exact install_other kApp A v 0 (by decide)
  · exact install_other kApp A v 1 (by decide)
  · exact install_other kApp A v 2 (by decide)
  · exact install_other kApp A v 3 (by decide)
  · exact install_other kApp A v 4 (by decide)
  · exact install_slot kApp kApp_inj A v 1
  · exact install_slot kApp kApp_inj A v 3
  · exact install_other kApp A v 7 (by decide)
  · exact install_other kApp A v 8 (by decide)
  · exact install_other kApp A v 9 (by decide)
  · exact install_other kApp A v 10 (by decide)
  · exact install_other kApp A v 11 (by decide)
  · exact install_other kApp A v 12 (by decide)
  · exact install_slot kApp kApp_inj A v 2
  · exact install_slot kApp kApp_inj A v 4
  · exact install_slot kApp kApp_inj A v 0
  · exact install_slot kApp kApp_inj A v 5

theorem dockH_kApp (H : Fin 17 → ℕ) (v : Fin 6 → ℕ) :
    dockH kApp H v = ![H 0, H 1, H 2, H 3, H 4, v 1, v 3, H 7, H 8, H 9, H 10, H 11, H 12, v 2, v 4, v 0, v 5] := by
  funext i
  fin_cases i
  · exact dockH_other kApp H v 0 (by decide)
  · exact dockH_other kApp H v 1 (by decide)
  · exact dockH_other kApp H v 2 (by decide)
  · exact dockH_other kApp H v 3 (by decide)
  · exact dockH_other kApp H v 4 (by decide)
  · exact dockH_slot kApp kApp_inj H v 1
  · exact dockH_slot kApp kApp_inj H v 3
  · exact dockH_other kApp H v 7 (by decide)
  · exact dockH_other kApp H v 8 (by decide)
  · exact dockH_other kApp H v 9 (by decide)
  · exact dockH_other kApp H v 10 (by decide)
  · exact dockH_other kApp H v 11 (by decide)
  · exact dockH_other kApp H v 12 (by decide)
  · exact dockH_slot kApp kApp_inj H v 2
  · exact dockH_slot kApp kApp_inj H v 4
  · exact dockH_slot kApp kApp_inj H v 0
  · exact dockH_slot kApp kApp_inj H v 5

theorem kEmP_inj : Function.Injective kEmP := by decide

theorem install_kEmP (A : Fin 17 → List Bool) (v : Fin 3 → List Bool) :
    install kEmP A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 0, A 8, A 9, v 2, A 11, A 12, A 13, A 14, v 1, A 16] := by
  funext i
  fin_cases i
  · exact install_other kEmP A v 0 (by decide)
  · exact install_other kEmP A v 1 (by decide)
  · exact install_other kEmP A v 2 (by decide)
  · exact install_other kEmP A v 3 (by decide)
  · exact install_other kEmP A v 4 (by decide)
  · exact install_other kEmP A v 5 (by decide)
  · exact install_other kEmP A v 6 (by decide)
  · exact install_slot kEmP kEmP_inj A v 0
  · exact install_other kEmP A v 8 (by decide)
  · exact install_other kEmP A v 9 (by decide)
  · exact install_slot kEmP kEmP_inj A v 2
  · exact install_other kEmP A v 11 (by decide)
  · exact install_other kEmP A v 12 (by decide)
  · exact install_other kEmP A v 13 (by decide)
  · exact install_other kEmP A v 14 (by decide)
  · exact install_slot kEmP kEmP_inj A v 1
  · exact install_other kEmP A v 16 (by decide)

theorem dockH_kEmP (H : Fin 17 → ℕ) (v : Fin 3 → ℕ) :
    dockH kEmP H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 0, H 8, H 9, v 2, H 11, H 12, H 13, H 14, v 1, H 16] := by
  funext i
  fin_cases i
  · exact dockH_other kEmP H v 0 (by decide)
  · exact dockH_other kEmP H v 1 (by decide)
  · exact dockH_other kEmP H v 2 (by decide)
  · exact dockH_other kEmP H v 3 (by decide)
  · exact dockH_other kEmP H v 4 (by decide)
  · exact dockH_other kEmP H v 5 (by decide)
  · exact dockH_other kEmP H v 6 (by decide)
  · exact dockH_slot kEmP kEmP_inj H v 0
  · exact dockH_other kEmP H v 8 (by decide)
  · exact dockH_other kEmP H v 9 (by decide)
  · exact dockH_slot kEmP kEmP_inj H v 2
  · exact dockH_other kEmP H v 11 (by decide)
  · exact dockH_other kEmP H v 12 (by decide)
  · exact dockH_other kEmP H v 13 (by decide)
  · exact dockH_other kEmP H v 14 (by decide)
  · exact dockH_slot kEmP kEmP_inj H v 1
  · exact dockH_other kEmP H v 16 (by decide)

theorem kEmN_inj : Function.Injective kEmN := by decide

theorem install_kEmN (A : Fin 17 → List Bool) (v : Fin 3 → List Bool) :
    install kEmN A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0, A 9, v 2, A 11, A 12, A 13, A 14, v 1, A 16] := by
  funext i
  fin_cases i
  · exact install_other kEmN A v 0 (by decide)
  · exact install_other kEmN A v 1 (by decide)
  · exact install_other kEmN A v 2 (by decide)
  · exact install_other kEmN A v 3 (by decide)
  · exact install_other kEmN A v 4 (by decide)
  · exact install_other kEmN A v 5 (by decide)
  · exact install_other kEmN A v 6 (by decide)
  · exact install_other kEmN A v 7 (by decide)
  · exact install_slot kEmN kEmN_inj A v 0
  · exact install_other kEmN A v 9 (by decide)
  · exact install_slot kEmN kEmN_inj A v 2
  · exact install_other kEmN A v 11 (by decide)
  · exact install_other kEmN A v 12 (by decide)
  · exact install_other kEmN A v 13 (by decide)
  · exact install_other kEmN A v 14 (by decide)
  · exact install_slot kEmN kEmN_inj A v 1
  · exact install_other kEmN A v 16 (by decide)

theorem dockH_kEmN (H : Fin 17 → ℕ) (v : Fin 3 → ℕ) :
    dockH kEmN H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 0, H 9, v 2, H 11, H 12, H 13, H 14, v 1, H 16] := by
  funext i
  fin_cases i
  · exact dockH_other kEmN H v 0 (by decide)
  · exact dockH_other kEmN H v 1 (by decide)
  · exact dockH_other kEmN H v 2 (by decide)
  · exact dockH_other kEmN H v 3 (by decide)
  · exact dockH_other kEmN H v 4 (by decide)
  · exact dockH_other kEmN H v 5 (by decide)
  · exact dockH_other kEmN H v 6 (by decide)
  · exact dockH_other kEmN H v 7 (by decide)
  · exact dockH_slot kEmN kEmN_inj H v 0
  · exact dockH_other kEmN H v 9 (by decide)
  · exact dockH_slot kEmN kEmN_inj H v 2
  · exact dockH_other kEmN H v 11 (by decide)
  · exact dockH_other kEmN H v 12 (by decide)
  · exact dockH_other kEmN H v 13 (by decide)
  · exact dockH_other kEmN H v 14 (by decide)
  · exact dockH_slot kEmN kEmN_inj H v 1
  · exact dockH_other kEmN H v 16 (by decide)

/-- The pass's heads: the children cursor and the pool cursor. -/
def kH (a o : ℕ) : Fin 17 → ℕ := ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0]

/-- The pass's tapes. -/
def kA (NM SD FR RP RN OL OR PA NA TM LG LG2 ZH ZL ZR OUT LG3 : List Bool) : Fin 17 → List Bool :=
  ![NM, SD, FR, RP, RN, OL, OR, PA, NA, TM, LG, LG2, ZH, ZL, ZR, OUT, LG3]

/-- The number of left (right) center coordinates. -/
def nLeft (side : List Bool) (n : ℕ) : ℕ := ((List.ofFn fun i : Fin n => side.getD i false).filter id).length
def nRight (side : List Bool) (n : ℕ) : ℕ := ((List.ofFn fun i : Fin n => side.getD i false).filter (fun b => !b)).length

theorem routeL_length {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) :
    (routeL (coords side f e)).length = nLeft side n := by
  have hm : (coords side f e).map (fun c => c.1) = List.ofFn fun j : Fin n => side.getD j false := by
    simp [coords, List.map_ofFn, Function.comp_def]
  simp only [routeL, List.length_map, nLeft]
  rw [← hm, List.filter_map, List.length_map]
  rfl

theorem routeR_length {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) :
    (routeR (coords side f e)).length = nRight side n := by
  have hm : (coords side f e).map (fun c => c.1) = List.ofFn fun j : Fin n => side.getD j false := by
    simp [coords, List.map_ofFn, Function.comp_def]
  simp only [routeR, List.length_map, nRight]
  rw [← hm, List.filter_map, List.length_map]
  rfl

theorem coords_side {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) (hs : side.length = n) :
    (coords side f e).map (fun c => c.1) = side := by
  apply List.ext_getElem
  · simp [coords, hs]
  · intro i h1 h2
    simp [coords, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem coords_flip {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) (hf : f.length = n) :
    (coords side f e).map (fun c => c.2.1) = f := by
  apply List.ext_getElem
  · simp [coords, hf]
  · intro i h1 h2
    simp [coords, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem pairsOf_coords (h : ℕ) {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) :
    pairsOf h (coords side f e) = (List.ofFn e.weight).flatMap (fun z => pairEnc h (pn z)) := by
  unfold pairsOf
  have hm : (coords side f e).map (fun c => c.2.2) = List.ofFn e.weight := by
    simp [coords, List.map_ofFn, Function.comp_def]
  rw [← hm, List.flatMap_map]

/-- The left and right zero paddings as records. -/
def zeroRecs (h k : ℕ) : List (List Bool) := (List.replicate k (pnWords h 0)).flatten

theorem zeroRecs_length (h k : ℕ) : (zeroRecs h k).length = 2 * k := by
  simp [zeroRecs, pnWords, List.length_flatten, List.sum_replicate]; ring

theorem zeroRecs_width (h k : ℕ) : ∀ r ∈ zeroRecs h k, r.length = h := by
  intro r hr
  simp only [zeroRecs, List.mem_flatten, List.mem_replicate] at hr
  obtain ⟨l, ⟨_, rfl⟩, hr⟩ := hr
  simp [pnWords] at hr
  rcases hr with rfl | rfl <;> simp

theorem pnWords_width (h : ℕ) (L : List ℤ) : ∀ r ∈ L.flatMap (pnWords h), r.length = h := by
  intro r hr
  obtain ⟨z, _, hz⟩ := List.mem_flatMap.mp hr
  simp [pnWords] at hz
  rcases hz with rfl | rfl <;> simp

section KSteps
variable (h : ℕ)

theorem k_initP (a o : ℕ) (NM SD FR RP RN OL OR PA NA TM LG2 tZ ZL ZR OUT LG3 : List Bool) (cap : ℕ)
    (hc : 2 * h + 1 ≤ cap) :
    Step (RecoveryFocus.machine kInitP regCopyM) (regCost h) (kH a o)
      (kA NM SD FR RP RN OL OR PA NA TM (List.replicate cap false) LG2 (frame (binary h 0) ++ tZ) ZL ZR OUT LG3)
      (kH a o)
      (kA NM SD FR RP RN OL OR (overlay (frame (binary h 0)) PA) NA TM (List.replicate cap false) LG2
        (frame (binary h 0) ++ tZ) ZL ZR OUT LG3) := by
  have e := dockRun (regCopyStep (binary h 0) tZ PA cap (by simp; omega)) kInitP kInitP_inj (kH a o)
    (kA NM SD FR RP RN OL OR PA NA TM (List.replicate cap false) LG2 (frame (binary h 0) ++ tZ) ZL ZR OUT LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kInitP, dockH_kInitP] at e
  refine (e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).enlarge ?_
  simp [regCost]

theorem k_initN (a o : ℕ) (NM SD FR RP RN OL OR PA NA TM LG2 tZ ZL ZR OUT LG3 : List Bool) (cap : ℕ)
    (hc : 2 * h + 1 ≤ cap) :
    Step (RecoveryFocus.machine kInitN regCopyM) (regCost h) (kH a o)
      (kA NM SD FR RP RN OL OR PA NA TM (List.replicate cap false) LG2 (frame (binary h 0) ++ tZ) ZL ZR OUT LG3)
      (kH a o)
      (kA NM SD FR RP RN OL OR PA (overlay (frame (binary h 0)) NA) TM (List.replicate cap false) LG2
        (frame (binary h 0) ++ tZ) ZL ZR OUT LG3) := by
  have e := dockRun (regCopyStep (binary h 0) tZ NA cap (by simp; omega)) kInitN kInitN_inj (kH a o)
    (kA NM SD FR RP RN OL OR PA NA TM (List.replicate cap false) LG2 (frame (binary h 0) ++ tZ) ZL ZR OUT LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kInitN, dockH_kInitN] at e
  refine (e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).enlarge ?_
  simp [regCost]

theorem k_loop (cs : List Coord) (pre post tS tF BL BR PA0 NA0 RP0 RN0 T0 ZH ZL ZR OUT LG3 : List Bool) (o cap cap2 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcap2 : cloopCost h cs.length ≤ cap2) :
    Step (RecoveryFocus.machine kLoop cloopR) (2 * cloopCost h cs.length + 2) (kH pre.length o)
      (kA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        RP0 RN0 BL BR (overlay (frame (binary h 0)) PA0) (overlay (frame (binary h 0)) NA0) T0
        (List.replicate cap false) (List.replicate cap2 false) ZH ZL ZR OUT LG3)
      (kH (pre.length + (pairsOf h cs).length) o)
      (kA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        (cs.foldl (cstep h) ⟨[], [], 0, 0, RP0, RN0, T0⟩).rp (cs.foldl (cstep h) ⟨[], [], 0, 0, RP0, RN0, T0⟩).rn
        (overlay (leftPart h cs ++ [false]) BL) (overlay (rightPart h cs ++ [false]) BR)
        (overlay (frame (binary h (cs.foldl (cstep h) ⟨[], [], 0, 0, RP0, RN0, T0⟩).P)) PA0)
        (overlay (frame (binary h (cs.foldl (cstep h) ⟨[], [], 0, 0, RP0, RN0, T0⟩).N)) NA0)
        (cs.foldl (cstep h) ⟨[], [], 0, 0, RP0, RN0, T0⟩).tmp (List.replicate cap false)
        (List.replicate cap2 false) ZH ZL ZR OUT LG3) := by
  have c := cloop_run h cs pre post tS tF BL BR PA0 NA0 RP0 RN0 T0 0 0 cap cap2 hcap hcap2
  have e := dockRun c kLoop kLoop_inj (kH pre.length o)
    (kA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
      RP0 RN0 BL BR (overlay (frame (binary h 0)) PA0) (overlay (frame (binary h 0)) NA0) T0
      (List.replicate cap false) (List.replicate cap2 false) ZH ZL ZR OUT LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kLoop, dockH_kLoop] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem k_tgt (Pt Nt P N : ℕ) (pre post SD FR RPx RNx OL OR PA0 NA0 Tx LG2 ZH ZL ZR OUT LG3 : List Bool) (o cap : ℕ)
    (hcap : 2 * h + 1 ≤ cap) :
    Step (RecoveryFocus.machine kTgt tgtM) (tgtCost h) (kH pre.length o)
      (kA (pre ++ false :: (pairEnc h (Pt, Nt) ++ post)) SD FR RPx RNx OL OR (overlay (frame (binary h P)) PA0)
        (overlay (frame (binary h N)) NA0) Tx (List.replicate cap false) LG2 ZH ZL ZR OUT LG3)
      (kH (pre ++ false :: pairEnc h (Pt, Nt)).length o)
      (kA (pre ++ false :: (pairEnc h (Pt, Nt) ++ post)) SD FR (overlay (frame (binary h Pt)) RPx)
        (overlay (frame (binary h Nt)) RNx) OL OR (overlay (frame (binary h (P + Pt))) PA0)
        (overlay (frame (binary h (N + Nt))) NA0)
        (overlay (frame (binary h (N + Nt))) (overlay (frame (binary h (P + Pt))) Tx)) (List.replicate cap false)
        LG2 ZH ZL ZR OUT LG3) := by
  have c := tgt_step h Pt Nt P N pre post SD FR RPx RNx OL OR PA0 NA0 Tx 0 0 0 0 cap hcap
  have e := dockRun c kTgt kTgt_inj (kH pre.length o)
    (kA (pre ++ false :: (pairEnc h (Pt, Nt) ++ post)) SD FR RPx RNx OL OR (overlay (frame (binary h P)) PA0)
      (overlay (frame (binary h N)) NA0) Tx (List.replicate cap false) LG2 ZH ZL ZR OUT LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kTgt, dockH_kTgt] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem k_app (E NL ZL NR ZR : List (List Bool)) (Sv sL sZL sR sZR : List Bool) (cap3 : ℕ)
    (NM SD FR RP RN PA NA TM LG LG2 ZH : List Bool) (a : ℕ)
    (hNL : ∀ r ∈ NL, r.length = h) (hZL : ∀ r ∈ ZL, r.length = h) (hNR : ∀ r ∈ NR, r.length = h)
    (hZR : ∀ r ∈ ZR, r.length = h) (h1 : 1 ≤ h) (hcap : appCost h NL.length ZL.length NR.length ZR.length ≤ cap3) :
    Step (RecoveryFocus.machine kApp appR) (2 * appCost h NL.length ZL.length NR.length ZR.length + 2)
      (kH a (E.flatMap frame).length)
      (kA NM SD FR RP RN (streamTape NL sL) (streamTape NR sR) PA NA TM LG LG2 ZH (streamTape ZL sZL) (streamTape ZR sZR)
        (overlay (E.flatMap frame) Sv) (List.replicate cap3 false))
      (kH a ((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame).length)
      (kA NM SD FR RP RN (streamTape NL sL) (streamTape NR sR) PA NA TM LG LG2 ZH (streamTape ZL sZL) (streamTape ZR sZR)
        (overlay ((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame) Sv) (List.replicate cap3 false)) := by
  have c := app_run E NL ZL NR ZR Sv sL sZL sR sZR h cap3 hNL hZL hNR hZR h1 hcap
  have c' : Step appR (2 * appCost h NL.length ZL.length NR.length ZR.length + 2)
      ![(E.flatMap frame).length, 0, 0, 0, 0, 0]
      ![overlay (E.flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR, streamTape ZR sZR,
        List.replicate cap3 false]
      ![((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame).length, 0, 0, 0, 0, 0]
      ![overlay ((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR,
        streamTape ZR sZR, List.replicate cap3 false] := by
    refine (c.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have e := dockRun c' kApp kApp_inj (kH a (E.flatMap frame).length)
    (kA NM SD FR RP RN (streamTape NL sL) (streamTape NR sR) PA NA TM LG LG2 ZH (streamTape ZL sZL) (streamTape ZR sZR)
      (overlay (E.flatMap frame) Sv) (List.replicate cap3 false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kApp, dockH_kApp] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem k_emP (x : ℕ) (t : List Bool) (a : ℕ) (NM SD FR RP RN OL OR NA TM LG2 ZH ZL ZR out BW LG3 : List Bool) (cap : ℕ)
    (hc : 2 * h + 1 ≤ cap) :
    Step (RecoveryFocus.machine kEmP emitM) (regCost h) (kH a out.length)
      (kA NM SD FR RP RN OL OR (frame (binary h x) ++ t) NA TM (List.replicate cap false) LG2 ZH ZL ZR (overlay out BW) LG3)
      (kH a (out ++ frame (binary h x)).length)
      (kA NM SD FR RP RN OL OR (frame (binary h x) ++ t) NA TM (List.replicate cap false) LG2 ZH ZL ZR
        (overlay (out ++ frame (binary h x)) BW) LG3) := by
  have e := dockRun (emitT (binary h x) t out BW cap (by simp; omega)) kEmP kEmP_inj (kH a out.length)
    (kA NM SD FR RP RN OL OR (frame (binary h x) ++ t) NA TM (List.replicate cap false) LG2 ZH ZL ZR (overlay out BW) LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kEmP, dockH_kEmP] at e
  refine (e.congr ?_ (by funext i; fin_cases i <;> rfl)).enlarge (by simp [regCost])
  funext i; fin_cases i <;> simp [kH]

theorem k_emN (x : ℕ) (t : List Bool) (a : ℕ) (NM SD FR RP RN OL OR PA TM LG2 ZH ZL ZR out BW LG3 : List Bool) (cap : ℕ)
    (hc : 2 * h + 1 ≤ cap) :
    Step (RecoveryFocus.machine kEmN emitM) (regCost h) (kH a out.length)
      (kA NM SD FR RP RN OL OR PA (frame (binary h x) ++ t) TM (List.replicate cap false) LG2 ZH ZL ZR (overlay out BW) LG3)
      (kH a (out ++ frame (binary h x)).length)
      (kA NM SD FR RP RN OL OR PA (frame (binary h x) ++ t) TM (List.replicate cap false) LG2 ZH ZL ZR
        (overlay (out ++ frame (binary h x)) BW) LG3) := by
  have e := dockRun (emitT (binary h x) t out BW cap (by simp; omega)) kEmN kEmN_inj (kH a out.length)
    (kA NM SD FR RP RN OL OR PA (frame (binary h x) ++ t) TM (List.replicate cap false) LG2 ZH ZL ZR (overlay out BW) LG3)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_kEmN, dockH_kEmN] at e
  refine (e.congr ?_ (by funext i; fin_cases i <;> rfl)).enlarge (by simp [regCost])
  funext i; fin_cases i <;> simp [kH]

end KSteps

/-- **One dense child** on the pool stream. -/
noncomputable def childPass := Composition.machine (RecoveryFocus.machine kInitP regCopyM)
  (Composition.machine (RecoveryFocus.machine kInitN regCopyM) (Composition.machine (RecoveryFocus.machine kLoop cloopR)
    (Composition.machine (RecoveryFocus.machine kTgt tgtM) (Composition.machine (RecoveryFocus.machine kApp appR)
      (Composition.machine (RecoveryFocus.machine kEmP emitM) (RecoveryFocus.machine kEmN emitM))))))

def childPassCost (h n width kl kr : ℕ) : ℕ := regCost h + 1 + (regCost h + 1 + ((2 * cloopCost h n + 2) + 1 +
  (tgtCost h + 1 + ((2 * appCost h (2 * kl) (2 * (width - kl)) (2 * kr) (2 * (width - kr)) + 2) + 1 +
    (regCost h + 1 + regCost h)))))

theorem pnWords_flatMap_length (h : ℕ) (L : List ℤ) : (L.flatMap (pnWords h)).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons z L ih => simp [List.flatMap_cons, pnWords, ih]; ring

theorem child_pass (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n)
    (hs : side.length = n) (hf : f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (pre post tS tF RP RN TM PA NA BL BR tZ sZL sZR BWO : List Bool) (E : List (List Bool)) (cap cap2 cap3 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcap2 : cloopCost h n ≤ cap2)
    (hcap3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ cap3) :
    Step childPass (childPassCost h n width (nLeft side n) (nRight side n)) (kH pre.length (E.flatMap frame).length)
      (kA (pre ++ origRec h e ++ post) (frame side ++ tS) (frame f ++ tF) RP RN BL BR PA NA TM
        (List.replicate cap false) (List.replicate cap2 false) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        (overlay (E.flatMap frame) BWO) (List.replicate cap3 false))
      (kH (pre ++ origRec h e).length ((E ++ denseRecs h side f width e).flatMap frame).length)
      (kA (pre ++ origRec h e ++ post) (frame side ++ tS) (frame f ++ tF)
        (overlay (frame (binary h (pn e.target).1)) RP) (overlay (frame (binary h (pn e.target).2)) RN)
        (overlay (leftPart h (coords side f e) ++ [false]) BL) (overlay (rightPart h (coords side f e) ++ [false]) BR)
        (overlay (frame (binary h (targetP (coords side f e) e.target))) PA)
        (overlay (frame (binary h (targetN (coords side f e) e.target))) NA)
        (overlay (frame (binary h (targetN (coords side f e) e.target))) TM)
        (List.replicate cap false) (List.replicate cap2 false) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        (overlay ((E ++ denseRecs h side f width e).flatMap frame) BWO) (List.replicate cap3 false)) := by
  set cs := coords side f e
  set st0 : CoordSt := ⟨[], [], 0, 0, RP, RN, TM⟩
  set st := cs.foldl (cstep h) st0
  set Pt := (pn e.target).1
  set Nt := (pn e.target).2
  set post' := false :: (pairEnc h (Pt, Nt) ++ post)
  have hcsl : cs.length = n := by simp [cs, coords]
  have hNM : pre ++ origRec h e ++ post = pre ++ pairsOf h cs ++ post' := by
    simp [origRec, cs, pairsOf_coords, post', Pt, Nt, List.append_assoc]
  have hNM2 : pre ++ origRec h e ++ post = (pre ++ pairsOf h cs) ++ false :: (pairEnc h (Pt, Nt) ++ post) := by
    rw [hNM]
  have hSD : frame side ++ tS = frame (cs.map fun c => c.1) ++ tS := by rw [coords_side side f e hs]
  have hFR : frame f ++ tF = frame (cs.map fun c => c.2.1) ++ tF := by rw [coords_flip side f e hf]
  set NM := pre ++ origRec h e ++ post
  set SD := frame side ++ tS
  set FR := frame f ++ tF
  set lg := List.replicate cap false
  set lg2 := List.replicate cap2 false
  set lg3 := List.replicate cap3 false
  set ZH := frame (binary h 0) ++ tZ
  set ZL := streamTape (zeroRecs h (width - nLeft side n)) sZL
  set ZR := streamTape (zeroRecs h (width - nRight side n)) sZR
  set OUT0 := overlay (E.flatMap frame) BWO
  have s1 := k_initP h pre.length (E.flatMap frame).length NM SD FR RP RN BL BR PA NA TM lg2 tZ ZL ZR OUT0 lg3 cap hcap
  have s2 := k_initN h pre.length (E.flatMap frame).length NM SD FR RP RN BL BR (overlay (frame (binary h 0)) PA) NA TM
    lg2 tZ ZL ZR OUT0 lg3 cap hcap
  have s3 := k_loop h cs pre post' tS tF BL BR PA NA RP RN TM ZH ZL ZR OUT0 lg3 (E.flatMap frame).length cap cap2 hcap
    (by rw [hcsl]; exact hcap2)
  rw [← hNM, ← hSD, ← hFR] at s3
  have hPn : st.P = (cs.map fun c => if c.2.1 then (pn c.2.2).2 else 0).sum := by
    rw [cfold_P]; simp [st0]
  have hNn : st.N = (cs.map fun c => if c.2.1 then (pn c.2.2).1 else 0).sum := by
    rw [cfold_N]; simp [st0]
  have hLp : st.L = leftPart h cs := by rw [cfold_L]; rfl
  have s4 := k_tgt h Pt Nt st.P st.N (pre ++ pairsOf h cs) post SD FR st.rp st.rn (overlay (leftPart h cs ++ [false]) BL)
    (overlay (rightPart h cs ++ [false]) BR) PA NA st.tmp lg2 ZH ZL ZR OUT0 lg3 (E.flatMap frame).length cap hcap
  rw [← hNM2] at s4
  have hpre : (pre ++ pairsOf h cs).length = pre.length + (pairsOf h cs).length := by simp
  rw [hpre] at s4
  have hLS : overlay (leftPart h cs ++ [false]) BL = streamTape ((routeL cs).flatMap (pnWords h))
      (BL.drop ((((routeL cs).flatMap (pnWords h)).flatMap frame).length + 1)) := by
    rw [leftPart_eq, overlay_stream]
  have hRS : overlay (rightPart h cs ++ [false]) BR = streamTape ((routeR cs).flatMap (pnWords h))
      (BR.drop ((((routeR cs).flatMap (pnWords h)).flatMap frame).length + 1)) := by
    rw [rightPart_eq, overlay_stream]
  have s5 := k_app h E ((routeL cs).flatMap (pnWords h)) (zeroRecs h (width - nLeft side n))
    ((routeR cs).flatMap (pnWords h)) (zeroRecs h (width - nRight side n)) BWO
    (BL.drop ((((routeL cs).flatMap (pnWords h)).flatMap frame).length + 1)) sZL
    (BR.drop ((((routeR cs).flatMap (pnWords h)).flatMap frame).length + 1)) sZR cap3 NM SD FR
    (overlay (frame (binary h Pt)) st.rp) (overlay (frame (binary h Nt)) st.rn)
    (overlay (frame (binary h (st.P + Pt))) PA) (overlay (frame (binary h (st.N + Nt))) NA)
    (overlay (frame (binary h (st.N + Nt))) (overlay (frame (binary h (st.P + Pt))) st.tmp)) lg lg2 ZH
    (pre ++ origRec h e).length (pnWords_width h _) (zeroRecs_width h _) (pnWords_width h _) (zeroRecs_width h _) h1 (by
      rw [pnWords_flatMap_length, pnWords_flatMap_length, zeroRecs_length, zeroRecs_length, routeL_length, routeR_length]
      exact hcap3)
  have hOL' : (pre ++ pairsOf h cs ++ false :: pairEnc h (Pt, Nt)).length = (pre ++ origRec h e).length := by
    have h2 : pre ++ origRec h e = pre ++ pairsOf h cs ++ false :: pairEnc h (Pt, Nt) := by
      simp [origRec, cs, pairsOf_coords, Pt, Nt, List.append_assoc]
    rw [h2]
  rw [List.append_assoc pre (pairsOf h cs), ← List.append_assoc, hOL'] at s4
  rw [← hLS, ← hRS] at s5
  set NL := (routeL cs).flatMap (pnWords h)
  set NR := (routeR cs).flatMap (pnWords h)
  set ZLr := zeroRecs h (width - nLeft side n)
  set ZRr := zeroRecs h (width - nRight side n)
  set OUT1 := (E ++ NL ++ ZLr ++ NR ++ ZRr).flatMap frame
  have s6 := k_emP h (st.P + Pt) (PA.drop (frame (binary h (st.P + Pt))).length) (pre ++ origRec h e).length NM SD FR
    (overlay (frame (binary h Pt)) st.rp) (overlay (frame (binary h Nt)) st.rn)
    (overlay (leftPart h cs ++ [false]) BL) (overlay (rightPart h cs ++ [false]) BR)
    (overlay (frame (binary h (st.N + Nt))) NA)
    (overlay (frame (binary h (st.N + Nt))) (overlay (frame (binary h (st.P + Pt))) st.tmp)) lg2 ZH ZL ZR OUT1 BWO lg3
    cap hcap
  have s7 := k_emN h (st.N + Nt) (NA.drop (frame (binary h (st.N + Nt))).length) (pre ++ origRec h e).length NM SD FR
    (overlay (frame (binary h Pt)) st.rp) (overlay (frame (binary h Nt)) st.rn)
    (overlay (leftPart h cs ++ [false]) BL) (overlay (rightPart h cs ++ [false]) BR)
    (overlay (frame (binary h (st.P + Pt))) PA)
    (overlay (frame (binary h (st.N + Nt))) (overlay (frame (binary h (st.P + Pt))) st.tmp)) lg2 ZH ZL ZR
    (OUT1 ++ frame (binary h (st.P + Pt))) BWO lg3 cap hcap
  have j := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))
  have hLw : (routeL cs).length ≤ width := by rw [routeL_length]; exact hL
  have hRw : (routeR cs).length ≤ width := by rw [routeR_length]; exact hR
  have ePA : st.P + Pt = targetP cs e.target := by rw [hPn]; rfl
  have eNA : st.N + Nt = targetN cs e.target := by rw [hNn]; rfl
  have eRP : overlay (frame (binary h Pt)) st.rp = overlay (frame (binary h Pt)) RP := fold_collapse_rp h Pt cs st0
  have eRN : overlay (frame (binary h Nt)) st.rn = overlay (frame (binary h Nt)) RN := fold_collapse_rn h Nt cs st0
  have eTM : overlay (frame (binary h (st.N + Nt))) (overlay (frame (binary h (st.P + Pt))) st.tmp) =
      overlay (frame (binary h (st.N + Nt))) TM := by
    rw [overlay_collapse _ _ _ (frame_len_eq h _ _)]
    exact fold_collapse_tmp h _ cs st0
  have eOUT : OUT1 ++ frame (binary h (st.P + Pt)) ++ frame (binary h (st.N + Nt)) =
      (E ++ denseRecs h side f width e).flatMap frame := by
    rw [denseRecs_eq h side f width e hLw hRw, ePA, eNA, routeL_length, routeR_length]
    simp only [OUT1, NL, NR, ZLr, ZRr, zeroRecs, List.flatMap_append, List.append_assoc, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rfl
  rw [eRP, eRN, eTM, eOUT] at j
  rw [ePA, eNA] at j
  have hl1 : (routeL cs).length = nLeft side n := routeL_length side f e
  have hl2 : (routeR cs).length = nRight side n := routeR_length side f e
  refine j.enlarge (le_of_eq ?_)
  simp only [childPassCost, hcsl, NL, NR, ZLr, ZRr, pnWords_flatMap_length, zeroRecs_length, hl1, hl2]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
