import Proof.Wire_3_5.CompilerMachinePoolChild

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The child loop's state: the stale registers and buffers, and the pool records written so far. -/
structure PSt where
  rp : List Bool
  rn : List Bool
  ol : List Bool
  or : List Bool
  pa : List Bool
  na : List Bool
  tm : List Bool
  E : List (List Bool)

/-- One child's effect (`child_pass`). -/
def pnext (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (st : PSt) (e : ExactThresholdGate n) : PSt where
  rp := overlay (frame (binary h (pn e.target).1)) st.rp
  rn := overlay (frame (binary h (pn e.target).2)) st.rn
  ol := overlay (leftPart h (coords side f e) ++ [false]) st.ol
  or := overlay (rightPart h (coords side f e) ++ [false]) st.or
  pa := overlay (frame (binary h (targetP (coords side f e) e.target))) st.pa
  na := overlay (frame (binary h (targetN (coords side f e) e.target))) st.na
  tm := overlay (frame (binary h (targetN (coords side f e) e.target))) st.tm
  E := st.E ++ denseRecs h side f width e

theorem pnext_E (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) :
    ∀ (gs : List (ExactThresholdGate n)) (st : PSt),
      (gs.foldl (pnext h side f width) st).E = st.E ++ gs.flatMap (denseRecs h side f width)
  | [], st => by simp
  | e :: gs, st => by
    rw [List.foldl_cons, pnext_E h side f width gs, List.flatMap_cons]
    simp [pnext, List.append_assoc]

/-- The child loop over the normalized children (tape 0). -/
noncomputable def kidsM := StreamController.machine childPass 0

/-- The child pass's bank from a state. -/
def kBank (NM SD FR ZH ZL ZR BWO : List Bool) (cap cap2 cap3 : ℕ) (st : PSt) : Fin 17 → List Bool :=
  kA NM SD FR st.rp st.rn st.ol st.or st.pa st.na st.tm (List.replicate cap false) (List.replicate cap2 false) ZH ZL ZR
    (overlay (st.E.flatMap frame) BWO) (List.replicate cap3 false)

theorem origRec_head (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (hn : 1 ≤ n) (e : ExactThresholdGate n) :
    ∃ l, origRec h e = true :: l := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp [origRec, List.ofFn_succ, pairEnc, binary, frame]

theorem kids_run (h : ℕ) (h1 : 1 ≤ h) {n : ℕ} (hn : 1 ≤ n) (gs : List (ExactThresholdGate n)) (side f : List Bool)
    (width : ℕ) (hs : side.length = n) (hf : f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postN tS tF tZ sZL sZR BWO : List Bool) (st0 : PSt) (cap cap2 cap3 : ℕ)
    (hcap : 2 * h + 1 ≤ cap) (hcap2 : cloopCost h n ≤ cap2)
    (hcap3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ cap3) :
    Step kidsM (gs.length * (childPassCost h n width (nLeft side n) (nRight side n) + 2) + 1)
      (kH 0 (st0.E.flatMap frame).length)
      (kBank (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame f ++ tF) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO cap cap2 cap3 st0)
      (kH (gs.flatMap (origRec h)).length ((gs.foldl (pnext h side f width) st0).E.flatMap frame).length)
      (kBank (gs.flatMap (origRec h) ++ false :: postN) (frame side ++ tS) (frame f ++ tF) (frame (binary h 0) ++ tZ)
        (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
        BWO cap cap2 cap3 (gs.foldl (pnext h side f width) st0)) := by
  set NM := gs.flatMap (origRec h) ++ false :: postN
  have hr := encRun (origRec h) (fun e => origRec_head h h1 hn e) childPass 0 [] gs postN (pnext h side f width) st0
    (fun st p => kH p (st.E.flatMap frame).length)
    (fun st => kBank NM (frame side ++ tS) (frame f ++ tF) (frame (binary h 0) ++ tZ)
      (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
      BWO cap cap2 cap3 st)
    (fun st => by simp [kBank, kA, NM]) (fun st p => rfl) (childPassCost h n width (nLeft side n) (nRight side n)) (by
      intro j hj
      set st := (gs.take j).foldl (pnext h side f width) st0
      have hS : NM = ((gs.take j).flatMap (origRec h)) ++ origRec h gs[j] ++
          ((gs.drop (j + 1)).flatMap (origRec h) ++ false :: postN) := by
        simp only [NM]
        rw [enc_split (origRec h) gs j hj]
        simp [List.append_assoc]
      have c := child_pass h h1 side f width gs[j] hs hf hL hR ((gs.take j).flatMap (origRec h))
        ((gs.drop (j + 1)).flatMap (origRec h) ++ false :: postN) tS tF st.rp st.rn st.tm st.pa st.na st.ol st.or tZ
        sZL sZR BWO st.E cap cap2 cap3 hcap hcap2 hcap3
      rw [← hS] at c
      have ht : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have hst : (gs.take (j + 1)).foldl (pnext h side f width) st0 = pnext h side f width st gs[j] := by
        rw [ht, List.foldl_append]; rfl
      have hpos : ([] : List Bool).length + ((gs.take (j + 1)).flatMap (origRec h)).length =
          ((gs.take j).flatMap (origRec h) ++ origRec h gs[j]).length := by
        rw [ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_nil,
          Nat.zero_add]
      rw [hst, hpos]
      refine c.congr_in ?_ rfl
      simp)
  simp only [List.length_nil, Nat.zero_add] at hr
  exact hr

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
