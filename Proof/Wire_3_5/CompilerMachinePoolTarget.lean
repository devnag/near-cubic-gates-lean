import Proof.Wire_3_5.CompilerMachinePoolLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def bZipPT : Fin 4 → Fin 11 := ![7, 3, 9, 10]
def bZipNT : Fin 4 → Fin 11 := ![8, 4, 9, 10]
def bPutL : Fin 1 → Fin 11 := ![5]
def bPutR : Fin 1 → Fin 11 := ![6]

theorem bZipPT_inj : Function.Injective bZipPT := by decide

theorem install_bZipPT (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install bZipPT A v = ![A 0, A 1, A 2, v 1, A 4, A 5, A 6, v 0, A 8, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other bZipPT A v 0 (by decide)
  · exact install_other bZipPT A v 1 (by decide)
  · exact install_other bZipPT A v 2 (by decide)
  · exact install_slot bZipPT bZipPT_inj A v 1
  · exact install_other bZipPT A v 4 (by decide)
  · exact install_other bZipPT A v 5 (by decide)
  · exact install_other bZipPT A v 6 (by decide)
  · exact install_slot bZipPT bZipPT_inj A v 0
  · exact install_other bZipPT A v 8 (by decide)
  · exact install_slot bZipPT bZipPT_inj A v 2
  · exact install_slot bZipPT bZipPT_inj A v 3

theorem dockH_bZipPT (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH bZipPT H v = ![H 0, H 1, H 2, v 1, H 4, H 5, H 6, v 0, H 8, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other bZipPT H v 0 (by decide)
  · exact dockH_other bZipPT H v 1 (by decide)
  · exact dockH_other bZipPT H v 2 (by decide)
  · exact dockH_slot bZipPT bZipPT_inj H v 1
  · exact dockH_other bZipPT H v 4 (by decide)
  · exact dockH_other bZipPT H v 5 (by decide)
  · exact dockH_other bZipPT H v 6 (by decide)
  · exact dockH_slot bZipPT bZipPT_inj H v 0
  · exact dockH_other bZipPT H v 8 (by decide)
  · exact dockH_slot bZipPT bZipPT_inj H v 2
  · exact dockH_slot bZipPT bZipPT_inj H v 3

theorem bZipNT_inj : Function.Injective bZipNT := by decide

theorem install_bZipNT (A : Fin 11 → List Bool) (v : Fin 4 → List Bool) :
    install bZipNT A v = ![A 0, A 1, A 2, A 3, v 1, A 5, A 6, A 7, v 0, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other bZipNT A v 0 (by decide)
  · exact install_other bZipNT A v 1 (by decide)
  · exact install_other bZipNT A v 2 (by decide)
  · exact install_other bZipNT A v 3 (by decide)
  · exact install_slot bZipNT bZipNT_inj A v 1
  · exact install_other bZipNT A v 5 (by decide)
  · exact install_other bZipNT A v 6 (by decide)
  · exact install_other bZipNT A v 7 (by decide)
  · exact install_slot bZipNT bZipNT_inj A v 0
  · exact install_slot bZipNT bZipNT_inj A v 2
  · exact install_slot bZipNT bZipNT_inj A v 3

theorem dockH_bZipNT (H : Fin 11 → ℕ) (v : Fin 4 → ℕ) :
    dockH bZipNT H v = ![H 0, H 1, H 2, H 3, v 1, H 5, H 6, H 7, v 0, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other bZipNT H v 0 (by decide)
  · exact dockH_other bZipNT H v 1 (by decide)
  · exact dockH_other bZipNT H v 2 (by decide)
  · exact dockH_other bZipNT H v 3 (by decide)
  · exact dockH_slot bZipNT bZipNT_inj H v 1
  · exact dockH_other bZipNT H v 5 (by decide)
  · exact dockH_other bZipNT H v 6 (by decide)
  · exact dockH_other bZipNT H v 7 (by decide)
  · exact dockH_slot bZipNT bZipNT_inj H v 0
  · exact dockH_slot bZipNT bZipNT_inj H v 2
  · exact dockH_slot bZipNT bZipNT_inj H v 3

theorem bPutL_inj : Function.Injective bPutL := by decide

theorem install_bPutL (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install bPutL A v = ![A 0, A 1, A 2, A 3, A 4, v 0, A 6, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other bPutL A v 0 (by decide)
  · exact install_other bPutL A v 1 (by decide)
  · exact install_other bPutL A v 2 (by decide)
  · exact install_other bPutL A v 3 (by decide)
  · exact install_other bPutL A v 4 (by decide)
  · exact install_slot bPutL bPutL_inj A v 0
  · exact install_other bPutL A v 6 (by decide)
  · exact install_other bPutL A v 7 (by decide)
  · exact install_other bPutL A v 8 (by decide)
  · exact install_other bPutL A v 9 (by decide)
  · exact install_other bPutL A v 10 (by decide)

theorem dockH_bPutL (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH bPutL H v = ![H 0, H 1, H 2, H 3, H 4, v 0, H 6, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other bPutL H v 0 (by decide)
  · exact dockH_other bPutL H v 1 (by decide)
  · exact dockH_other bPutL H v 2 (by decide)
  · exact dockH_other bPutL H v 3 (by decide)
  · exact dockH_other bPutL H v 4 (by decide)
  · exact dockH_slot bPutL bPutL_inj H v 0
  · exact dockH_other bPutL H v 6 (by decide)
  · exact dockH_other bPutL H v 7 (by decide)
  · exact dockH_other bPutL H v 8 (by decide)
  · exact dockH_other bPutL H v 9 (by decide)
  · exact dockH_other bPutL H v 10 (by decide)

theorem bPutR_inj : Function.Injective bPutR := by decide

theorem install_bPutR (A : Fin 11 → List Bool) (v : Fin 1 → List Bool) :
    install bPutR A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8, A 9, A 10] := by
  funext i
  fin_cases i
  · exact install_other bPutR A v 0 (by decide)
  · exact install_other bPutR A v 1 (by decide)
  · exact install_other bPutR A v 2 (by decide)
  · exact install_other bPutR A v 3 (by decide)
  · exact install_other bPutR A v 4 (by decide)
  · exact install_other bPutR A v 5 (by decide)
  · exact install_slot bPutR bPutR_inj A v 0
  · exact install_other bPutR A v 7 (by decide)
  · exact install_other bPutR A v 8 (by decide)
  · exact install_other bPutR A v 9 (by decide)
  · exact install_other bPutR A v 10 (by decide)

theorem dockH_bPutR (H : Fin 11 → ℕ) (v : Fin 1 → ℕ) :
    dockH bPutR H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8, H 9, H 10] := by
  funext i
  fin_cases i
  · exact dockH_other bPutR H v 0 (by decide)
  · exact dockH_other bPutR H v 1 (by decide)
  · exact dockH_other bPutR H v 2 (by decide)
  · exact dockH_other bPutR H v 3 (by decide)
  · exact dockH_other bPutR H v 4 (by decide)
  · exact dockH_other bPutR H v 5 (by decide)
  · exact dockH_slot bPutR bPutR_inj H v 0
  · exact dockH_other bPutR H v 7 (by decide)
  · exact dockH_other bPutR H v 8 (by decide)
  · exact dockH_other bPutR H v 9 (by decide)
  · exact dockH_other bPutR H v 10 (by decide)

section TPrims
variable (NM SD FR OL OR : List Bool) (a sd fr oL oR cap : ℕ)

theorem ps_zipPT (u tu v tv RN NA TM : List Bool) (hl : u.length = v.length) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bZipPT (zipM addOut addNxt false)) (2 * (2 * u.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR (frame v ++ tv) RN OL OR (frame u ++ tu) NA TM (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR (frame v ++ tv) RN OL OR (frame u ++ tu) NA
        (overlay (frame (ZipMap.map addOut addNxt u v false)) TM) (List.replicate cap false)) := by
  have e := dockRun (zipT addOut addNxt false u v tu tv TM hl cap hcap) bZipPT bZipPT_inj (pH a sd fr oL oR)
    (pA NM SD FR (frame v ++ tv) RN OL OR (frame u ++ tu) NA TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bZipPT, dockH_bZipPT] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

theorem ps_zipNT (u tu v tv RP PA TM : List Bool) (hl : u.length = v.length) (hcap : 2 * u.length + 1 ≤ cap) :
    Step (RecoveryFocus.machine bZipNT (zipM addOut addNxt false)) (2 * (2 * u.length + 1) + 2) (pH a sd fr oL oR)
      (pA NM SD FR RP (frame v ++ tv) OL OR PA (frame u ++ tu) TM (List.replicate cap false)) (pH a sd fr oL oR)
      (pA NM SD FR RP (frame v ++ tv) OL OR PA (frame u ++ tu)
        (overlay (frame (ZipMap.map addOut addNxt u v false)) TM) (List.replicate cap false)) := by
  have e := dockRun (zipT addOut addNxt false u v tu tv TM hl cap hcap) bZipNT bZipNT_inj (pH a sd fr oL oR)
    (pA NM SD FR RP (frame v ++ tv) OL OR PA (frame u ++ tu) TM (List.replicate cap false))
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_bZipNT, dockH_bZipNT] at e
  exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

end TPrims

theorem ps_putL (NM SD FR RP RN OR PA NA TM LG X B : List Bool) (a sd fr oR : ℕ) :
    Step (RecoveryFocus.machine bPutL (putM false)) 1 (pH a sd fr X.length oR)
      (pA NM SD FR RP RN (overlay X B) OR PA NA TM LG) (pH a sd fr (X ++ [false]).length oR)
      (pA NM SD FR RP RN (overlay (X ++ [false]) B) OR PA NA TM LG) := by
  have p0 := putStep false (overlay X B) X.length
  rw [overlay_write] at p0
  have e := dockRun p0 bPutL bPutL_inj (pH a sd fr X.length oR) (pA NM SD FR RP RN (overlay X B) OR PA NA TM LG)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_bPutL, dockH_bPutL] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

theorem ps_putR (NM SD FR RP RN OL PA NA TM LG X B : List Bool) (a sd fr oL : ℕ) :
    Step (RecoveryFocus.machine bPutR (putM false)) 1 (pH a sd fr oL X.length)
      (pA NM SD FR RP RN OL (overlay X B) PA NA TM LG) (pH a sd fr oL (X ++ [false]).length)
      (pA NM SD FR RP RN OL (overlay (X ++ [false]) B) PA NA TM LG) := by
  have p0 := putStep false (overlay X B) X.length
  rw [overlay_write] at p0
  have e := dockRun p0 bPutR bPutR_inj (pH a sd fr oL X.length) (pA NM SD FR RP RN OL (overlay X B) PA NA TM LG)
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_bPutR, dockH_bPutR] at e
  refine e.congr ?_ (by funext i; fin_cases i <;> rfl)
  funext i; fin_cases i <;> simp [pH]

/-- The coordinate loop, then the two buffers closed by `false`. -/
noncomputable def cloopInner := Composition.machine (StreamController.machine coordBody 1)
  (Composition.machine (RecoveryFocus.machine bPutL (putM false)) (RecoveryFocus.machine bPutR (putM false)))
/-- The coordinate phase with the side, flip and buffer heads returned to `0` (log on tape 11). -/
noncomputable def cloopR := MaskedReset.machine cloopInner (fun i => decide (i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6))

def cloopCost (h n : ℕ) : ℕ := (n * (coordCost h + 2) + 1) + 1 + (1 + 1 + 1)

def qH (a : ℕ) : Fin 12 → ℕ := ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def qA (NM SD FR RP RN OL OR PA NA TM LG LG2 : List Bool) : Fin 12 → List Bool :=
  ![NM, SD, FR, RP, RN, OL, OR, PA, NA, TM, LG, LG2]

/-- **The coordinate phase of one child**: the left and right parts are written and closed, the accumulators hold
the crossed flip sums, and every loop head is back at `0`. -/
theorem cloop_run (h : ℕ) (cs : List Coord) (pre post tS tF BL BR PA0 NA0 RP0 RN0 T0 : List Bool) (P0 N0 cap cap2 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcap2 : cloopCost h cs.length ≤ cap2) :
    Step cloopR (2 * cloopCost h cs.length + 2) (qH pre.length)
      (qA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        RP0 RN0 BL BR (overlay (frame (binary h P0)) PA0) (overlay (frame (binary h N0)) NA0) T0
        (List.replicate cap false) (List.replicate cap2 false))
      (qH (pre.length + (pairsOf h cs).length))
      (qA (pre ++ pairsOf h cs ++ post) (frame (cs.map fun c => c.1) ++ tS) (frame (cs.map fun c => c.2.1) ++ tF)
        (cs.foldl (cstep h) ⟨[], [], P0, N0, RP0, RN0, T0⟩).rp (cs.foldl (cstep h) ⟨[], [], P0, N0, RP0, RN0, T0⟩).rn
        (overlay (leftPart h cs ++ [false]) BL) (overlay (rightPart h cs ++ [false]) BR)
        (overlay (frame (binary h (cs.foldl (cstep h) ⟨[], [], P0, N0, RP0, RN0, T0⟩).P)) PA0)
        (overlay (frame (binary h (cs.foldl (cstep h) ⟨[], [], P0, N0, RP0, RN0, T0⟩).N)) NA0)
        (cs.foldl (cstep h) ⟨[], [], P0, N0, RP0, RN0, T0⟩).tmp (List.replicate cap false)
        (List.replicate cap2 false)) := by
  set st0 : CoordSt := ⟨[], [], P0, N0, RP0, RN0, T0⟩
  set st := cs.foldl (cstep h) st0
  set NM := pre ++ pairsOf h cs ++ post
  set SD := frame (cs.map fun c => c.1) ++ tS
  set FR := frame (cs.map fun c => c.2.1) ++ tF
  have hL : st.L = leftPart h cs := by rw [cfold_L]; rfl
  have hR : st.R = rightPart h cs := by rw [cfold_R]; rfl
  have c1 := coords_run h cs pre post tS tF BL BR PA0 NA0 st0 cap hcap
  have hBL : overlay st0.L BL = BL := by simp [st0, overlay]
  have hBR : overlay st0.R BR = BR := by simp [st0, overlay]
  unfold loopA at c1
  rw [hBL, hBR] at c1
  have c2 := ps_putL NM SD FR st.rp st.rn (overlay st.R BR) (overlay (frame (binary h st.P)) PA0)
    (overlay (frame (binary h st.N)) NA0) st.tmp (List.replicate cap false) st.L BL
    (pre.length + (pairsOf h cs).length) (2 * cs.length) (2 * cs.length) st.R.length
  have c3 := ps_putR NM SD FR st.rp st.rn (overlay (st.L ++ [false]) BL) (overlay (frame (binary h st.P)) PA0)
    (overlay (frame (binary h st.N)) NA0) st.tmp (List.replicate cap false) st.R BR
    (pre.length + (pairsOf h cs).length) (2 * cs.length) (2 * cs.length) (st.L ++ [false]).length
  have j := c1.seq (c2.seq c3)
  have hm := j.mask (fun i => decide (i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6))
    (by intro i hi; fin_cases i <;> simp_all [pH, st0]) hcap2
  rw [hL, hR] at hm
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- Step over the separator, load the target's pair, add it into the accumulators. -/
noncomputable def tgtM := Composition.machine mvN (Composition.machine ldP (Composition.machine mvN
  (Composition.machine ldN (Composition.machine mvN (Composition.machine (RecoveryFocus.machine bZipPT (zipM addOut addNxt false))
    (Composition.machine (RecoveryFocus.machine bCpP regCopyM) (Composition.machine
      (RecoveryFocus.machine bZipNT (zipM addOut addNxt false)) (RecoveryFocus.machine bCpN regCopyM))))))))

def tgtCost (h : ℕ) : ℕ := 1 + 1 + (regCost h + 1 + (1 + 1 + (regCost h + 1 + (1 + 1 + (regCost h + 1 + (regCost h + 1 +
  (regCost h + 1 + regCost h)))))))

theorem tgt_step (h Pt Nt P N : ℕ) (pre post SD FR RPx RNx OL OR PA0 NA0 Tx : List Bool) (sd fr oL oR cap : ℕ)
    (hcap : 2 * h + 1 ≤ cap) :
    Step tgtM (tgtCost h) (pH pre.length sd fr oL oR)
      (pA (pre ++ false :: (pairEnc h (Pt, Nt) ++ post)) SD FR RPx RNx OL OR (overlay (frame (binary h P)) PA0)
        (overlay (frame (binary h N)) NA0) Tx (List.replicate cap false))
      (pH (pre ++ false :: pairEnc h (Pt, Nt)).length sd fr oL oR)
      (pA (pre ++ false :: (pairEnc h (Pt, Nt) ++ post)) SD FR (overlay (frame (binary h Pt)) RPx)
        (overlay (frame (binary h Nt)) RNx) OL OR (overlay (frame (binary h (P + Pt))) PA0)
        (overlay (frame (binary h (N + Nt))) NA0)
        (overlay (frame (binary h (N + Nt))) (overlay (frame (binary h (P + Pt))) Tx)) (List.replicate cap false)) := by
  have hrc : ∀ x, 2 * (2 * (binary h x).length + 1) + 2 = regCost h := by intro x; simp [regCost]
  have hbl : ∀ x, 2 * (binary h x).length + 1 ≤ cap := by intro x; simp; omega
  set NM := pre ++ false :: (pairEnc h (Pt, Nt) ++ post)
  set lg := List.replicate cap false
  set PAi := overlay (frame (binary h P)) PA0
  set NAi := overlay (frame (binary h N)) NA0
  set RP1 := overlay (frame (binary h Pt)) RPx
  set RN1 := overlay (frame (binary h Nt)) RNx
  set PA1 := overlay (frame (binary h (P + Pt))) PA0
  set NA1 := overlay (frame (binary h (N + Nt))) NA0
  set T1 := overlay (frame (binary h (P + Pt))) Tx
  set T2 := overlay (frame (binary h (N + Nt))) T1
  have hN1 : NM = (pre ++ [false]) ++ frame (binary h Pt) ++ (frame (binary h Nt) ++ post) := by
    simp [NM, pairEnc, List.append_assoc]
  have hN2 : NM = (pre ++ [false] ++ frame (binary h Pt)) ++ frame (binary h Nt) ++ post := by
    simp [NM, pairEnc, List.append_assoc]
  have s1 := ps_mvN NM SD FR RPx RNx OL OR PAi NAi Tx pre.length sd fr oL oR lg
  have s2 : Step ldP (regCost h) (pH (pre.length + 1) sd fr oL oR) (pA NM SD FR RPx RNx OL OR PAi NAi Tx lg)
      (pH ((pre ++ [false]).length + 2 * h) sd fr oL oR) (pA NM SD FR RP1 RNx OL OR PAi NAi Tx lg) := by
    have e := ps_loadP SD FR RPx RNx OL OR PAi NAi Tx sd fr oL oR cap (pre ++ [false]) (binary h Pt)
      (frame (binary h Nt) ++ post) (hbl Pt)
    rw [← hN1, binary_length, show (pre ++ [false]).length = pre.length + 1 by simp] at e
    rw [show (pre ++ [false]).length = pre.length + 1 by simp]
    exact e.enlarge (le_of_eq (by simp [regCost]))
  have s3 := ps_mvN NM SD FR RP1 RNx OL OR PAi NAi Tx ((pre ++ [false]).length + 2 * h) sd fr oL oR lg
  have s4 : Step ldN (regCost h) (pH ((pre ++ [false]).length + 2 * h + 1) sd fr oL oR)
      (pA NM SD FR RP1 RNx OL OR PAi NAi Tx lg)
      (pH ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PAi NAi Tx lg) := by
    have e := ps_loadN SD FR RP1 RNx OL OR PAi NAi Tx sd fr oL oR cap (pre ++ [false] ++ frame (binary h Pt))
      (binary h Nt) post (hbl Nt)
    rw [← hN2, binary_length] at e
    have hl : (pre ++ [false] ++ frame (binary h Pt)).length = (pre ++ [false]).length + 2 * h + 1 := by simp; omega
    rw [hl] at e
    rw [hl]
    exact e.enlarge (le_of_eq (by simp [regCost]))
  have s5 := ps_mvN NM SD FR RP1 RN1 OL OR PAi NAi Tx ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h) sd fr
    oL oR lg
  have s6 : Step (RecoveryFocus.machine bZipPT (zipM addOut addNxt false)) (regCost h) (pH ((pre ++ [false] ++ frame
      (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PAi NAi Tx lg)
      (pH ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PAi NAi T1 lg) := by
    have z := ps_zipPT NM SD FR OL OR ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR cap
      (binary h P) (PA0.drop (frame (binary h P)).length) (binary h Pt) (RPx.drop (frame (binary h Pt)).length) RN1 NAi Tx
      (by simp) (hbl P)
    rw [map_add] at z
    exact z.enlarge (le_of_eq (hrc P))
  have s7 : Step (RecoveryFocus.machine bCpP regCopyM) (regCost h) (pH ((pre ++ [false] ++ frame
      (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PAi NAi T1 lg)
      (pH ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PA1 NAi T1 lg) := by
    have c := ps_cpP NM SD FR OL OR ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR cap
      (binary h (P + Pt)) (Tx.drop (frame (binary h (P + Pt))).length) RP1 RN1 PAi NAi (hbl (P + Pt))
    have e : overlay (frame (binary h (P + Pt))) PAi = PA1 := overlay_collapse _ _ _ (by simp)
    rw [e] at c
    exact c.enlarge (le_of_eq (hrc (P + Pt)))
  have s8 : Step (RecoveryFocus.machine bZipNT (zipM addOut addNxt false)) (regCost h) (pH ((pre ++ [false] ++ frame
      (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PA1 NAi T1 lg)
      (pH ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PA1 NAi T2 lg) := by
    have z := ps_zipNT NM SD FR OL OR ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR cap
      (binary h N) (NA0.drop (frame (binary h N)).length) (binary h Nt) (RNx.drop (frame (binary h Nt)).length) RP1 PA1 T1
      (by simp) (hbl N)
    rw [map_add] at z
    exact z.enlarge (le_of_eq (hrc N))
  have s9 : Step (RecoveryFocus.machine bCpN regCopyM) (regCost h) (pH ((pre ++ [false] ++ frame
      (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PA1 NAi T2 lg)
      (pH ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR) (pA NM SD FR RP1 RN1 OL OR PA1 NA1 T2 lg) := by
    have c := ps_cpN NM SD FR OL OR ((pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1) sd fr oL oR cap
      (binary h (N + Nt)) (T1.drop (frame (binary h (N + Nt))).length) RP1 RN1 PA1 NAi (hbl (N + Nt))
    have e : overlay (frame (binary h (N + Nt))) NAi = NA1 := overlay_collapse _ _ _ (by simp)
    rw [e] at c
    exact c.enlarge (le_of_eq (hrc (N + Nt)))
  have j := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq s9)))))))
  have hend : (pre ++ [false] ++ frame (binary h Pt)).length + 2 * h + 1 = (pre ++ false :: pairEnc h (Pt, Nt)).length := by
    simp [pairEnc]; omega
  rw [hend] at j
  exact j

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
