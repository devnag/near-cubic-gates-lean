import Proof.Wire_3_5.CompilerMachineEmitArms

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

theorem selAt_length_le {α : Type} (PC : List α) (U j : ℕ) : (selAt PC U j).length ≤ j := by
  unfold selAt
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem trueCost_mono (R0 L1 L2 h : ℕ) (hL : L1 ≤ L2) : trueCost R0 L1 h ≤ trueCost R0 L2 h := by
  unfold trueCost mergeAllCost mergeCost copyCost appendCost
  gcongr

theorem falseCost_mono (R0 L1 L2 h : ℕ) (hL : L1 ≤ L2) : falseCost R0 L1 h ≤ falseCost R0 L2 h := by
  unfold falseCost skipCost
  gcongr

/-- A uniform bound for both arms at stack width at most `Lm`. -/
def armBound (R0 Lm h : ℕ) : ℕ := trueCost R0 Lm h + falseCost R0 Lm h

/-- The cost of one label. -/
def labelCost (R0 Lm h : ℕ) : ℕ := 1 + 1 + ((armBound R0 Lm h + 2) + 1 + 1)

def lRE : Fin 1 → Fin 6 := ![0]
def lTrue : Fin 5 → Fin 6 := ![2, 1, 3, 4, 5]
def lFalse : Fin 3 → Fin 6 := ![2, 1, 4]

theorem lRE_inj : Function.Injective lRE := by decide

theorem install_lRE (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    install lRE A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i
  fin_cases i
  · exact install_slot lRE lRE_inj A v 0
  · exact install_other lRE A v 1 (by decide)
  · exact install_other lRE A v 2 (by decide)
  · exact install_other lRE A v 3 (by decide)
  · exact install_other lRE A v 4 (by decide)
  · exact install_other lRE A v 5 (by decide)

theorem dockH_lRE (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH lRE H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i
  fin_cases i
  · exact dockH_slot lRE lRE_inj H v 0
  · exact dockH_other lRE H v 1 (by decide)
  · exact dockH_other lRE H v 2 (by decide)
  · exact dockH_other lRE H v 3 (by decide)
  · exact dockH_other lRE H v 4 (by decide)
  · exact dockH_other lRE H v 5 (by decide)

theorem lTrue_inj : Function.Injective lTrue := by decide

theorem install_lTrue (A : Fin 6 → List Bool) (v : Fin 5 → List Bool) :
    install lTrue A v = ![A 0, v 1, v 0, v 2, v 3, v 4] := by
  funext i
  fin_cases i
  · exact install_other lTrue A v 0 (by decide)
  · exact install_slot lTrue lTrue_inj A v 1
  · exact install_slot lTrue lTrue_inj A v 0
  · exact install_slot lTrue lTrue_inj A v 2
  · exact install_slot lTrue lTrue_inj A v 3
  · exact install_slot lTrue lTrue_inj A v 4

theorem dockH_lTrue (H : Fin 6 → ℕ) (v : Fin 5 → ℕ) :
    dockH lTrue H v = ![H 0, v 1, v 0, v 2, v 3, v 4] := by
  funext i
  fin_cases i
  · exact dockH_other lTrue H v 0 (by decide)
  · exact dockH_slot lTrue lTrue_inj H v 1
  · exact dockH_slot lTrue lTrue_inj H v 0
  · exact dockH_slot lTrue lTrue_inj H v 2
  · exact dockH_slot lTrue lTrue_inj H v 3
  · exact dockH_slot lTrue lTrue_inj H v 4

theorem lFalse_inj : Function.Injective lFalse := by decide

theorem install_lFalse (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    install lFalse A v = ![A 0, v 1, v 0, A 3, v 2, A 5] := by
  funext i
  fin_cases i
  · exact install_other lFalse A v 0 (by decide)
  · exact install_slot lFalse lFalse_inj A v 1
  · exact install_slot lFalse lFalse_inj A v 0
  · exact install_other lFalse A v 3 (by decide)
  · exact install_slot lFalse lFalse_inj A v 2
  · exact install_other lFalse A v 5 (by decide)

theorem dockH_lFalse (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH lFalse H v = ![H 0, v 1, v 0, H 3, v 2, H 5] := by
  funext i
  fin_cases i
  · exact dockH_other lFalse H v 0 (by decide)
  · exact dockH_slot lFalse lFalse_inj H v 1
  · exact dockH_slot lFalse lFalse_inj H v 0
  · exact dockH_other lFalse H v 3 (by decide)
  · exact dockH_slot lFalse lFalse_inj H v 2
  · exact dockH_other lFalse H v 5 (by decide)

noncomputable def lMoveD := RecoveryFocus.machine lRE moveM
noncomputable def lTrueD := RecoveryFocus.machine lTrue trueArmM
noncomputable def lFalseD := RecoveryFocus.machine lFalse falseArmM
/-- **One label**: step onto the mask bit, merge or skip, step onto the next mark. -/
noncomputable def labelBodyM := Composition.machine lMoveD (Composition.machine (branchM 0 lTrueD lFalseD) lMoveD)

theorem read_mask_bit (Pre l tl : List Bool) (j : ℕ) (hj : j < l.length) :
    readTapeBit (Pre ++ (frame l ++ tl)) (Pre.length + 2 * j + 1) = l[j] := by
  rw [show Pre.length + 2 * j + 1 = Pre.length + (2 * j + 1) by omega, read_suffix]
  exact read_frame_bit' l tl j hj

theorem mergeAllCost_mono (R0 L1 L2 h : ℕ) (hL : L1 ≤ L2) : mergeAllCost R0 L1 h ≤ mergeAllCost R0 L2 h := by
  unfold mergeAllCost mergeCost
  gcongr

theorem skipCost_mono (R0 L1 L2 h : ℕ) (hL : L1 ≤ L2) : skipCost R0 L1 h ≤ skipCost R0 L2 h := by
  unfold skipCost
  gcongr

theorem appendCost_mono (R0 W1 W2 : ℕ) (hW : W1 ≤ W2) : appendCost 0 R0 W1 ≤ appendCost 0 R0 W2 := by
  unfold appendCost
  gcongr

/-- A merged label: the stack stream of the next labels, collapsed over the old one. -/
theorem stack_next (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (fe : List Bool × ExactThresholdGate n) (X : List Bool) :
    overlay (streamTape (List.zipWith (· ++ ·) (stackRecs h side width L) (labRecs h side width fe)) [])
        (overlay (stackStream h side width L) X) = overlay (stackStream h side width (L ++ [fe])) X := by
  rw [zip_stack]
  apply overlay_collapse'
  unfold stackStream
  rw [stream_len _ _ (stackRecs_width h side width (L ++ [fe])), stream_len _ _ (stackRecs_width h side width L),
    stackRecs_length, stackRecs_length, List.length_append, List.length_singleton]
  gcongr
  nlinarith

/-- **The label loop**: after the whole pool, the stack and the scratch hold the stack stream of the mask's labels. -/
theorem labels_loop (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (PC : List (List Bool × ExactThresholdGate n))
    (U : ℕ) (Pre tlRE tlPL S1₀ S2₀ : List Bool) (capA capC : ℕ)
    (hA1 : mergeAllCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hA2 : skipCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hC : appendCost 0 (2 * (width + width + 1)) (1 + PC.length * h + h) ≤ capC) :
    Step (StreamController.machine labelBodyM 0)
      (PC.length * (labelCost (2 * (width + width + 1)) (1 + PC.length * h) h + 2) + 1)
      ![Pre.length, 0, 0, 0, 0, 0]
      ![Pre ++ (frame (binary PC.length U) ++ tlRE), (PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL,
        overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀,
        overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀,
        List.replicate capA false, List.replicate capC false]
      ![Pre.length + 2 * PC.length, ((PC.flatMap (labRecs h side width)).flatMap frame).length, 0, 0, 0, 0]
      ![Pre ++ (frame (binary PC.length U) ++ tlRE), (PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL,
        overlay (stackStream h side width (selAt PC U PC.length)) S1₀,
        overlay (stackStream h side width (selAt PC U PC.length)) S2₀,
        List.replicate capA false, List.replicate capC false] := by
  set R0 := 2 * (width + width + 1)
  set Lm := 1 + PC.length * h
  set LR := labRecs h side width
  set RE := Pre ++ (frame (binary PC.length U) ++ tlRE)
  set PL := (PC.flatMap LR).flatMap frame ++ tlPL
  let bH : ℕ → Fin 6 → ℕ := fun j => ![Pre.length + 2 * j, (((PC.take j).flatMap LR).flatMap frame).length, 0, 0, 0, 0]
  let bA : ℕ → Fin 6 → List Bool := fun j => ![RE, PL, overlay (stackStream h side width (selAt PC U j)) S1₀,
    overlay (stackStream h side width (selAt PC U j)) S2₀, List.replicate capA false, List.replicate capC false]
  have hl := frameRunAt labelBodyM 0 Pre (binary PC.length U) tlRE bH bA (fun _ => rfl) (fun _ => rfl)
    (labelCost R0 Lm h) (by
      intro j hj
      rw [binary_length] at hj
      set sel := selAt PC U j
      set rs := stackRecs h side width sel
      set lr := LR PC[j]
      set pre0 := ((PC.take j).flatMap LR).flatMap frame
      set rest := ((PC.drop (j + 1)).flatMap LR).flatMap frame ++ tlPL
      set L1 := 1 + sel.length * h
      have hPL : PL = pre0 ++ (lr.flatMap frame ++ rest) := pool_split LR PC j hj tlPL
      have hL1 : L1 ≤ Lm := by
        have h0 : sel.length ≤ j := selAt_length_le PC U j
        have : sel.length * h ≤ PC.length * h := Nat.mul_le_mul_right h (by omega)
        omega
      have hrs := stackRecs_width h side width sel
      have hlr := labRecs_width h side width PC[j]
      have hr : rs.length = R0 := stackRecs_length h side width _
      have hlr' : lr.length = R0 := labRecs_length h side width _
      have hj1 : (((PC.take (j + 1)).flatMap LR).flatMap frame).length = pre0.length + (lr.flatMap frame).length := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append,
          List.flatMap_append]
        simp [pre0, lr]
      -- the step onto the bit and the step onto the next mark
      have m1 := dockRun (moveStep RE (Pre.length + 2 * j)) lRE lRE_inj (bH j) (bA j)
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_lRE, dockH_lRE] at m1
      have m1' : Step lMoveD 1 (bH j) (bA j)
          ![Pre.length + 2 * j + 1, pre0.length, 0, 0, 0, 0] (bA j) :=
        m1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
      have m2 := dockRun (moveStep RE (Pre.length + 2 * j + 1)) lRE lRE_inj
        ![Pre.length + 2 * j + 1, pre0.length + (lr.flatMap frame).length, 0, 0, 0, 0] (bA (j + 1))
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_lRE, dockH_lRE] at m2
      have m2' : Step lMoveD 1 ![Pre.length + 2 * j + 1, pre0.length + (lr.flatMap frame).length, 0, 0, 0, 0]
          (bA (j + 1)) (bH (j + 1)) (bA (j + 1)) := by
        refine m2.congr ?_ (by funext i; fin_cases i <;> rfl)
        funext i; fin_cases i
        · show Pre.length + 2 * j + 1 + 1 = Pre.length + 2 * (j + 1); omega
        · exact hj1.symm
        · rfl
        · rfl
        · rfl
        · rfl
      have hbit : readTapeBit ((bA j) 0) (Pre.length + 2 * j + 1) = U.testBit j := by
        show readTapeBit RE (Pre.length + 2 * j + 1) = _
        rw [read_mask_bit Pre (binary PC.length U) tlRE j (by simpa using hj)]
        rw [← MatrixScorePhi.binary_getD PC.length U j hj, List.getD_eq_getElem _ _ (by simpa using hj)]
      have hbound1 : trueCost R0 L1 h ≤ armBound R0 Lm h :=
        (trueCost_mono R0 L1 Lm h hL1).trans (Nat.le_add_right _ _)
      have hbound2 : falseCost R0 L1 h ≤ armBound R0 Lm h :=
        (falseCost_mono R0 L1 Lm h hL1).trans (Nat.le_add_left _ _)
      by_cases hb : U.testBit j = true
      · have hsel : selAt PC U (j + 1) = sel ++ [PC[j]] := by
          rw [selAt_succ PC U j hj, if_pos hb]
        have t := true_arm rs lr R0 L1 h hr hlr' hrs hlr (by omega) S1₀ pre0 rest
          (overlay (stackStream h side width sel) S2₀) capA capC
          ((mergeAllCost_mono R0 L1 Lm h hL1).trans hA1)
          ((appendCost_mono R0 (L1 + h) (Lm + h) (by omega)).trans hC)
        rw [stack_next h side width sel PC[j] S2₀] at t
        have ts : streamTape (List.zipWith (· ++ ·) rs lr) [] = stackStream h side width (sel ++ [PC[j]]) := by
          unfold stackStream; rw [zip_stack]
        rw [ts] at t
        have hcol : overlay (stackStream h side width (sel ++ [PC[j]])) (overlay (streamTape rs []) S1₀) =
            overlay (stackStream h side width (sel ++ [PC[j]])) S1₀ := by
          have sn := stack_next h side width sel PC[j] S1₀
          rw [ts] at sn
          exact sn
        rw [hcol] at t
        have d := dockRun t lTrue lTrue_inj ![Pre.length + 2 * j + 1, pre0.length, 0, 0, 0, 0] (bA j)
          (by intro k; fin_cases k <;> rfl) (by
            intro k; fin_cases k
            · rfl
            · exact hPL
            · rfl
            · rfl
            · rfl)
        rw [install_lTrue, dockH_lTrue] at d
        have d' : Step lTrueD (armBound R0 Lm h) ![Pre.length + 2 * j + 1, pre0.length, 0, 0, 0, 0] (bA j)
            ![Pre.length + 2 * j + 1, pre0.length + (lr.flatMap frame).length, 0, 0, 0, 0] (bA (j + 1)) := by
          refine (d.congr ?_ ?_).enlarge hbound1
          · funext i; fin_cases i <;> rfl
          · funext i; fin_cases i
            · rfl
            · exact hPL.symm
            · show _ = overlay (stackStream h side width (selAt PC U (j + 1))) S1₀
              rw [hsel]; rfl
            · show _ = overlay (stackStream h side width (selAt PC U (j + 1))) S2₀
              rw [hsel]; rfl
            · rfl
            · rfl
        have br := branch_true (0 : Fin 6) lFalseD d' (by
          show readTapeBit ((bA j) 0) (Pre.length + 2 * j + 1) = true; rw [hbit, hb])
        have j3 := m1'.seq (br.seq m2')
        unfold labelCost
        exact j3
      · have hb' : U.testBit j = false := by simpa using hb
        have hsel : selAt PC U (j + 1) = sel := by
          rw [selAt_succ PC U j hj, if_neg hb, List.append_nil]
        have t := false_arm rs lr R0 L1 h hr hlr' hrs hlr (by omega) S1₀ pre0 rest capA
          ((skipCost_mono R0 L1 Lm h hL1).trans hA2)
        have d := dockRun t lFalse lFalse_inj ![Pre.length + 2 * j + 1, pre0.length, 0, 0, 0, 0] (bA j)
          (by intro k; fin_cases k <;> rfl) (by
            intro k; fin_cases k
            · rfl
            · exact hPL
            · rfl)
        rw [install_lFalse, dockH_lFalse] at d
        have d' : Step lFalseD (armBound R0 Lm h) ![Pre.length + 2 * j + 1, pre0.length, 0, 0, 0, 0] (bA j)
            ![Pre.length + 2 * j + 1, pre0.length + (lr.flatMap frame).length, 0, 0, 0, 0] (bA (j + 1)) := by
          refine (d.congr ?_ ?_).enlarge hbound2
          · funext i; fin_cases i <;> rfl
          · funext i; fin_cases i
            · rfl
            · exact hPL.symm
            · show _ = overlay (stackStream h side width (selAt PC U (j + 1))) S1₀
              rw [hsel]; rfl
            · show _ = overlay (stackStream h side width (selAt PC U (j + 1))) S2₀
              rw [hsel]; rfl
            · rfl
            · rfl
        have br := branch_false (0 : Fin 6) lTrueD d' (by
          show readTapeBit ((bA j) 0) (Pre.length + 2 * j + 1) = false; rw [hbit, hb'])
        have j3 := m1'.seq (br.seq m2')
        unfold labelCost
        exact j3)
  simp only [binary_length] at hl
  refine hl.congr ?_ ?_
  · funext i; fin_cases i
    · rfl
    · show (((PC.take PC.length).flatMap LR).flatMap frame).length = _
      rw [List.take_length]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · funext i; fin_cases i <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
