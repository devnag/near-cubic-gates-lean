import Proof.Wire_3_5.CompilerMachinePoolKids

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The child loop with the children cursor returned to `0` (log on tape 17). -/
noncomputable def kidsR := MaskedReset.machine kidsM (fun i => decide (i = 0))

def gLoadF : Fin 3 → Fin 19 := ![18, 2, 10]
def gMvF : Fin 1 → Fin 19 := ![18]
def gKids : Fin 18 → Fin 19 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

theorem gLoadF_inj : Function.Injective gLoadF := by decide

theorem install_gLoadF (A : Fin 19 → List Bool) (v : Fin 3 → List Bool) :
    install gLoadF A v = ![A 0, A 1, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 2, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0] := by
  funext i
  fin_cases i
  · exact install_other gLoadF A v 0 (by decide)
  · exact install_other gLoadF A v 1 (by decide)
  · exact install_slot gLoadF gLoadF_inj A v 1
  · exact install_other gLoadF A v 3 (by decide)
  · exact install_other gLoadF A v 4 (by decide)
  · exact install_other gLoadF A v 5 (by decide)
  · exact install_other gLoadF A v 6 (by decide)
  · exact install_other gLoadF A v 7 (by decide)
  · exact install_other gLoadF A v 8 (by decide)
  · exact install_other gLoadF A v 9 (by decide)
  · exact install_slot gLoadF gLoadF_inj A v 2
  · exact install_other gLoadF A v 11 (by decide)
  · exact install_other gLoadF A v 12 (by decide)
  · exact install_other gLoadF A v 13 (by decide)
  · exact install_other gLoadF A v 14 (by decide)
  · exact install_other gLoadF A v 15 (by decide)
  · exact install_other gLoadF A v 16 (by decide)
  · exact install_other gLoadF A v 17 (by decide)
  · exact install_slot gLoadF gLoadF_inj A v 0

theorem dockH_gLoadF (H : Fin 19 → ℕ) (v : Fin 3 → ℕ) :
    dockH gLoadF H v = ![H 0, H 1, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 2, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other gLoadF H v 0 (by decide)
  · exact dockH_other gLoadF H v 1 (by decide)
  · exact dockH_slot gLoadF gLoadF_inj H v 1
  · exact dockH_other gLoadF H v 3 (by decide)
  · exact dockH_other gLoadF H v 4 (by decide)
  · exact dockH_other gLoadF H v 5 (by decide)
  · exact dockH_other gLoadF H v 6 (by decide)
  · exact dockH_other gLoadF H v 7 (by decide)
  · exact dockH_other gLoadF H v 8 (by decide)
  · exact dockH_other gLoadF H v 9 (by decide)
  · exact dockH_slot gLoadF gLoadF_inj H v 2
  · exact dockH_other gLoadF H v 11 (by decide)
  · exact dockH_other gLoadF H v 12 (by decide)
  · exact dockH_other gLoadF H v 13 (by decide)
  · exact dockH_other gLoadF H v 14 (by decide)
  · exact dockH_other gLoadF H v 15 (by decide)
  · exact dockH_other gLoadF H v 16 (by decide)
  · exact dockH_other gLoadF H v 17 (by decide)
  · exact dockH_slot gLoadF gLoadF_inj H v 0

theorem gMvF_inj : Function.Injective gMvF := by decide

theorem install_gMvF (A : Fin 19 → List Bool) (v : Fin 1 → List Bool) :
    install gMvF A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 0] := by
  funext i
  fin_cases i
  · exact install_other gMvF A v 0 (by decide)
  · exact install_other gMvF A v 1 (by decide)
  · exact install_other gMvF A v 2 (by decide)
  · exact install_other gMvF A v 3 (by decide)
  · exact install_other gMvF A v 4 (by decide)
  · exact install_other gMvF A v 5 (by decide)
  · exact install_other gMvF A v 6 (by decide)
  · exact install_other gMvF A v 7 (by decide)
  · exact install_other gMvF A v 8 (by decide)
  · exact install_other gMvF A v 9 (by decide)
  · exact install_other gMvF A v 10 (by decide)
  · exact install_other gMvF A v 11 (by decide)
  · exact install_other gMvF A v 12 (by decide)
  · exact install_other gMvF A v 13 (by decide)
  · exact install_other gMvF A v 14 (by decide)
  · exact install_other gMvF A v 15 (by decide)
  · exact install_other gMvF A v 16 (by decide)
  · exact install_other gMvF A v 17 (by decide)
  · exact install_slot gMvF gMvF_inj A v 0

theorem dockH_gMvF (H : Fin 19 → ℕ) (v : Fin 1 → ℕ) :
    dockH gMvF H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other gMvF H v 0 (by decide)
  · exact dockH_other gMvF H v 1 (by decide)
  · exact dockH_other gMvF H v 2 (by decide)
  · exact dockH_other gMvF H v 3 (by decide)
  · exact dockH_other gMvF H v 4 (by decide)
  · exact dockH_other gMvF H v 5 (by decide)
  · exact dockH_other gMvF H v 6 (by decide)
  · exact dockH_other gMvF H v 7 (by decide)
  · exact dockH_other gMvF H v 8 (by decide)
  · exact dockH_other gMvF H v 9 (by decide)
  · exact dockH_other gMvF H v 10 (by decide)
  · exact dockH_other gMvF H v 11 (by decide)
  · exact dockH_other gMvF H v 12 (by decide)
  · exact dockH_other gMvF H v 13 (by decide)
  · exact dockH_other gMvF H v 14 (by decide)
  · exact dockH_other gMvF H v 15 (by decide)
  · exact dockH_other gMvF H v 16 (by decide)
  · exact dockH_other gMvF H v 17 (by decide)
  · exact dockH_slot gMvF gMvF_inj H v 0

theorem gKids_inj : Function.Injective gKids := by decide

theorem install_gKids (A : Fin 19 → List Bool) (v : Fin 18 → List Bool) :
    install gKids A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, A 18] := by
  funext i
  fin_cases i
  · exact install_slot gKids gKids_inj A v 0
  · exact install_slot gKids gKids_inj A v 1
  · exact install_slot gKids gKids_inj A v 2
  · exact install_slot gKids gKids_inj A v 3
  · exact install_slot gKids gKids_inj A v 4
  · exact install_slot gKids gKids_inj A v 5
  · exact install_slot gKids gKids_inj A v 6
  · exact install_slot gKids gKids_inj A v 7
  · exact install_slot gKids gKids_inj A v 8
  · exact install_slot gKids gKids_inj A v 9
  · exact install_slot gKids gKids_inj A v 10
  · exact install_slot gKids gKids_inj A v 11
  · exact install_slot gKids gKids_inj A v 12
  · exact install_slot gKids gKids_inj A v 13
  · exact install_slot gKids gKids_inj A v 14
  · exact install_slot gKids gKids_inj A v 15
  · exact install_slot gKids gKids_inj A v 16
  · exact install_slot gKids gKids_inj A v 17
  · exact install_other gKids A v 18 (by decide)

theorem dockH_gKids (H : Fin 19 → ℕ) (v : Fin 18 → ℕ) :
    dockH gKids H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, H 18] := by
  funext i
  fin_cases i
  · exact dockH_slot gKids gKids_inj H v 0
  · exact dockH_slot gKids gKids_inj H v 1
  · exact dockH_slot gKids gKids_inj H v 2
  · exact dockH_slot gKids gKids_inj H v 3
  · exact dockH_slot gKids gKids_inj H v 4
  · exact dockH_slot gKids gKids_inj H v 5
  · exact dockH_slot gKids gKids_inj H v 6
  · exact dockH_slot gKids gKids_inj H v 7
  · exact dockH_slot gKids gKids_inj H v 8
  · exact dockH_slot gKids gKids_inj H v 9
  · exact dockH_slot gKids gKids_inj H v 10
  · exact dockH_slot gKids gKids_inj H v 11
  · exact dockH_slot gKids gKids_inj H v 12
  · exact dockH_slot gKids gKids_inj H v 13
  · exact dockH_slot gKids gKids_inj H v 14
  · exact dockH_slot gKids gKids_inj H v 15
  · exact dockH_slot gKids gKids_inj H v 16
  · exact dockH_slot gKids gKids_inj H v 17
  · exact dockH_other gKids H v 18 (by decide)

/-- One flip pattern: load it into the flip register, step over its frame, run the child loop. -/
noncomputable def flipBody := Composition.machine (RecoveryFocus.machine gLoadF loadM)
  (Composition.machine (RecoveryFocus.machine gMvF moveM) (RecoveryFocus.machine gKids kidsR))
/-- The flips loop over the flip stream (tape 18). -/
noncomputable def flipsM := StreamController.machine flipBody 18

/-- The flips loop's state: the child loop's state and the flip register. -/
structure FSt where
  ps : PSt
  fr : List Bool

def fnext (h : ℕ) {n : ℕ} (gs : List (ExactThresholdGate n)) (side : List Bool) (width : ℕ) (st : FSt)
    (f : List Bool) : FSt := ⟨gs.foldl (pnext h side f width) st.ps, overlay (frame f) st.fr⟩

def gH (o q : ℕ) : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, q]

def gA (NM SD ZH ZL ZR BWO FL : List Bool) (cap cap2 cap3 cap4 : ℕ) (st : FSt) : Fin 19 → List Bool :=
  ![NM, SD, st.fr, st.ps.rp, st.ps.rn, st.ps.ol, st.ps.or, st.ps.pa, st.ps.na, st.ps.tm, List.replicate cap false,
    List.replicate cap2 false, ZH, ZL, ZR, overlay (st.ps.E.flatMap frame) BWO, List.replicate cap3 false,
    List.replicate cap4 false, FL]

def kidsCost (h n width kl kr B : ℕ) : ℕ := B * (childPassCost h n width kl kr + 2) + 1

theorem pnext_E' (h : ℕ) {n : ℕ} (gs : List (ExactThresholdGate n)) (side f : List Bool) (width : ℕ) (st : PSt) :
    (gs.foldl (pnext h side f width) st).E = st.E ++ gs.flatMap (denseRecs h side f width) := pnext_E h side f width gs st

/-- **One flip pattern**: its dense children appended to the pool stream, the children cursor back at `0`. -/
theorem flip_step (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (hn : 1 ≤ n) (gs : List (ExactThresholdGate n)) (side f : List Bool)
    (width : ℕ) (hs : side.length = n) (hf : f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postN tS tZ sZL sZR BWO preF postF : List Bool) (st : FSt) (cap cap2 cap3 cap4 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcapF : 2 * n + 1 ≤ cap) (hcap2 : cloopCost h n ≤ cap2)
    (hcap3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ cap3)
    (hcap4 : kidsCost h n width (nLeft side n) (nRight side n) gs.length ≤ cap4) :
    Step flipBody (2 * (2 * n + 1) + 2 + 1 + (1 + 1 + (2 * kidsCost h n width (nLeft side n) (nRight side n) gs.length + 2)))
      (gH (st.ps.E.flatMap frame).length preF.length)
      (gA (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO (preF ++ frame f ++ postF) cap cap2 cap3 cap4 st)
      (gH ((fnext h gs side width st f).ps.E.flatMap frame).length (preF ++ frame f).length)
      (gA (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO (preF ++ frame f ++ postF) cap cap2 cap3 cap4 (fnext h gs side width st f)) := by
  set NM := gs.flatMap (origRec h) ++ false :: postN
  set SD := frame side ++ tS
  set ZH := frame (binary h 0) ++ tZ
  set ZL := streamTape (zeroRecs h (width - nLeft side n)) sZL
  set ZR := streamTape (zeroRecs h (width - nRight side n)) sZR
  set FL := preF ++ frame f ++ postF
  have c1 := loadStep preF f postF st.fr cap (by omega)
  have e1 := dockRun c1 gLoadF gLoadF_inj (gH (st.ps.E.flatMap frame).length preF.length)
    (gA NM SD ZH ZL ZR BWO FL cap cap2 cap3 cap4 st) (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_gLoadF, dockH_gLoadF] at e1
  have e2 := dockRun (moveStep FL (preF.length + 2 * f.length)) gMvF gMvF_inj
    (gH (st.ps.E.flatMap frame).length (preF.length + 2 * f.length))
    (gA NM SD ZH ZL ZR BWO FL cap cap2 cap3 cap4 ⟨st.ps, overlay (frame f) st.fr⟩)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_gMvF, dockH_gMvF] at e2
  have k0 := kids_run h h1 hn gs side f width hs hf hL hR postN tS (st.fr.drop (frame f).length) tZ sZL sZR BWO st.ps
    cap cap2 cap3 hcap hcap2 hcap3
  have km := k0.mask (fun i => decide (i = 0)) (by intro i hi; simp at hi; subst hi; rfl) hcap4
  have k1 : Step kidsR (2 * kidsCost h n width (nLeft side n) (nRight side n) gs.length + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (st.ps.E.flatMap frame).length, 0, 0]
      ![NM, SD, overlay (frame f) st.fr, st.ps.rp, st.ps.rn, st.ps.ol, st.ps.or, st.ps.pa, st.ps.na, st.ps.tm,
        List.replicate cap false, List.replicate cap2 false, ZH, ZL, ZR, overlay (st.ps.E.flatMap frame) BWO,
        List.replicate cap3 false, List.replicate cap4 false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ((gs.foldl (pnext h side f width) st.ps).E.flatMap frame).length, 0, 0]
      ![NM, SD, overlay (frame f) st.fr, (gs.foldl (pnext h side f width) st.ps).rp,
        (gs.foldl (pnext h side f width) st.ps).rn, (gs.foldl (pnext h side f width) st.ps).ol,
        (gs.foldl (pnext h side f width) st.ps).or, (gs.foldl (pnext h side f width) st.ps).pa,
        (gs.foldl (pnext h side f width) st.ps).na, (gs.foldl (pnext h side f width) st.ps).tm,
        List.replicate cap false, List.replicate cap2 false, ZH, ZL, ZR,
        overlay ((gs.foldl (pnext h side f width) st.ps).E.flatMap frame) BWO, List.replicate cap3 false,
        List.replicate cap4 false] := by
    refine (km.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      (try fin_cases j) <;> rfl
  have e3 := dockRun k1 gKids gKids_inj (gH (st.ps.E.flatMap frame).length (preF.length + 2 * f.length + 1))
    (gA NM SD ZH ZL ZR BWO FL cap cap2 cap3 cap4 ⟨st.ps, overlay (frame f) st.fr⟩)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_gKids, dockH_gKids] at e3
  have j := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      (e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)))
  have hq : preF.length + 2 * f.length + 1 = (preF ++ frame f).length := by simp; omega
  rw [hq] at j
  refine (j.congr ?_ ?_).enlarge (le_of_eq (by rw [hf]))
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def flipCost (h n width kl kr B : ℕ) : ℕ := 2 * (2 * n + 1) + 2 + 1 + (1 + 1 + (2 * kidsCost h n width kl kr B + 2))

theorem fnext_E (h : ℕ) {n : ℕ} (gs : List (ExactThresholdGate n)) (side : List Bool) (width : ℕ) :
    ∀ (flips : List (List Bool)) (st : FSt), (flips.foldl (fnext h gs side width) st).ps.E =
      st.ps.E ++ flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))
  | [], st => by simp
  | f :: fs, st => by
    rw [List.foldl_cons, fnext_E h gs side width fs, List.flatMap_cons]
    simp [fnext, pnext_E, List.append_assoc]

theorem flips_run (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (hn : 1 ≤ n) (gs : List (ExactThresholdGate n)) (side : List Bool)
    (width : ℕ) (flips : List (List Bool)) (hs : side.length = n) (hfl : ∀ f ∈ flips, f.length = n)
    (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postN tS tZ sZL sZR BWO staleF : List Bool) (st0 : FSt) (cap cap2 cap3 cap4 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcapF : 2 * n + 1 ≤ cap) (hcap2 : cloopCost h n ≤ cap2)
    (hcap3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ cap3)
    (hcap4 : kidsCost h n width (nLeft side n) (nRight side n) gs.length ≤ cap4) :
    Step flipsM (flips.length * (flipCost h n width (nLeft side n) (nRight side n) gs.length + 2) + 1)
      (gH (st0.ps.E.flatMap frame).length 0)
      (gA (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO (streamTape flips staleF) cap cap2 cap3 cap4 st0)
      (gH ((st0.ps.E ++ flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))).flatMap frame).length
        (flips.flatMap frame).length)
      (gA (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO (streamTape flips staleF) cap cap2 cap3 cap4 (flips.foldl (fnext h gs side width) st0)) := by
  have hne : ∀ r ∈ flips, r ≠ [] := by
    intro r hr hr0; have := hfl r hr; rw [hr0] at this; simp at this; omega
  have hr := streamRun flipBody 18 flips staleF hne (fnext h gs side width) st0
    (fun st p => gH (st.ps.E.flatMap frame).length p)
    (fun st => gA (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame (binary h 0) ++ tZ)
      (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
      BWO (streamTape flips staleF) cap cap2 cap3 cap4 st)
    (fun st => rfl) (fun st p => rfl) (flipCost h n width (nLeft side n) (nRight side n) gs.length) (by
      intro j hj
      have hS := streamTape_split flips staleF j hj
      have c := flip_step h h1 hn gs side flips[j] width hs (hfl _ (List.getElem_mem hj)) hL hR postN tS tZ sZL sZR BWO
        ((flips.take j).flatMap frame) ((flips.drop (j + 1)).flatMap frame ++ false :: staleF)
        ((flips.take j).foldl (fnext h gs side width) st0) cap cap2 cap3 cap4 hcap hcapF hcap2 hcap3 hcap4
      have hFL : (flips.take j).flatMap frame ++ frame flips[j] ++ ((flips.drop (j + 1)).flatMap frame ++ false :: staleF) =
          streamTape flips staleF := by
        rw [hS]
      rw [hFL] at c
      have ht : flips.take (j + 1) = flips.take j ++ [flips[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (flips.take (j + 1)).foldl (fnext h gs side width) st0 =
          fnext h gs side width ((flips.take j).foldl (fnext h gs side width) st0) flips[j] := by
        rw [ht, List.foldl_append]; rfl
      have ho : off flips (j + 1) = ((flips.take j).flatMap frame ++ frame flips[j]).length := by
        rw [off_succ flips j hj]; simp [off]
      rw [hst, ho]
      exact c)
  rw [fnext_E h gs side width flips st0] at hr
  exact hr

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
