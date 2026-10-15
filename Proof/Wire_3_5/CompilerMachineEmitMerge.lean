import Proof.Wire_3_5.CompilerMachineEmitNorm

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

theorem overlay_collapse' (a b M : List Bool) (h : b.length ≤ a.length) :
    overlay a (overlay b M) = overlay a M := by
  unfold overlay
  congr 1
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append, List.drop_drop]
  congr 1
  omega

theorem overlay_prefix (a c M : List Bool) : overlay a (overlay (a ++ c) M) = overlay (a ++ c) M := by
  unfold overlay
  rw [List.append_assoc a c, List.drop_append_length]

theorem frame_fpre (w : List Bool) : frame w = fpre w ++ [false] := by
  have h := frame_append' w []
  rw [List.append_nil] at h
  exact h

theorem split_at (pre0 rest : List Bool) (lr : List (List Bool)) (j : ℕ) (hj : j < lr.length) :
    pre0 ++ (lr.flatMap frame ++ rest) =
      (pre0 ++ (lr.take j).flatMap frame) ++ frame lr[j] ++ ((lr.drop (j + 1)).flatMap frame ++ rest) := by
  have e : lr = lr.take j ++ lr[j] :: lr.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  conv_lhs => rw [e]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

def mCp1 : Fin 2 → Fin 3 := ![0, 2]
def mLeft : Fin 1 → Fin 3 := ![2]
def mCp2 : Fin 2 → Fin 3 := ![1, 2]
def mNx1 : Fin 1 → Fin 3 := ![0]
def mNx2 : Fin 1 → Fin 3 := ![1]

theorem mCp1_inj : Function.Injective mCp1 := by decide

theorem install_mCp1 (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    install mCp1 A v = ![v 0, A 1, v 1] := by
  funext i
  fin_cases i
  · exact install_slot mCp1 mCp1_inj A v 0
  · exact install_other mCp1 A v 1 (by decide)
  · exact install_slot mCp1 mCp1_inj A v 1

theorem dockH_mCp1 (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH mCp1 H v = ![v 0, H 1, v 1] := by
  funext i
  fin_cases i
  · exact dockH_slot mCp1 mCp1_inj H v 0
  · exact dockH_other mCp1 H v 1 (by decide)
  · exact dockH_slot mCp1 mCp1_inj H v 1

theorem mLeft_inj : Function.Injective mLeft := by decide

theorem install_mLeft (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install mLeft A v = ![A 0, A 1, v 0] := by
  funext i
  fin_cases i
  · exact install_other mLeft A v 0 (by decide)
  · exact install_other mLeft A v 1 (by decide)
  · exact install_slot mLeft mLeft_inj A v 0

theorem dockH_mLeft (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH mLeft H v = ![H 0, H 1, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other mLeft H v 0 (by decide)
  · exact dockH_other mLeft H v 1 (by decide)
  · exact dockH_slot mLeft mLeft_inj H v 0

theorem mCp2_inj : Function.Injective mCp2 := by decide

theorem install_mCp2 (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    install mCp2 A v = ![A 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact install_other mCp2 A v 0 (by decide)
  · exact install_slot mCp2 mCp2_inj A v 0
  · exact install_slot mCp2 mCp2_inj A v 1

theorem dockH_mCp2 (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH mCp2 H v = ![H 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other mCp2 H v 0 (by decide)
  · exact dockH_slot mCp2 mCp2_inj H v 0
  · exact dockH_slot mCp2 mCp2_inj H v 1

theorem mNx1_inj : Function.Injective mNx1 := by decide

theorem install_mNx1 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install mNx1 A v = ![v 0, A 1, A 2] := by
  funext i
  fin_cases i
  · exact install_slot mNx1 mNx1_inj A v 0
  · exact install_other mNx1 A v 1 (by decide)
  · exact install_other mNx1 A v 2 (by decide)

theorem dockH_mNx1 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH mNx1 H v = ![v 0, H 1, H 2] := by
  funext i
  fin_cases i
  · exact dockH_slot mNx1 mNx1_inj H v 0
  · exact dockH_other mNx1 H v 1 (by decide)
  · exact dockH_other mNx1 H v 2 (by decide)

theorem mNx2_inj : Function.Injective mNx2 := by decide

theorem install_mNx2 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install mNx2 A v = ![A 0, v 0, A 2] := by
  funext i
  fin_cases i
  · exact install_other mNx2 A v 0 (by decide)
  · exact install_slot mNx2 mNx2_inj A v 0
  · exact install_other mNx2 A v 2 (by decide)

theorem dockH_mNx2 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH mNx2 H v = ![H 0, v 0, H 2] := by
  funext i
  fin_cases i
  · exact dockH_other mNx2 H v 0 (by decide)
  · exact dockH_slot mNx2 mNx2_inj H v 0
  · exact dockH_other mNx2 H v 2 (by decide)

noncomputable def mCp1D := RecoveryFocus.machine mCp1 CopyO.machine
noncomputable def mLeftD := RecoveryFocus.machine mLeft moveLM
noncomputable def mCp2D := RecoveryFocus.machine mCp2 CopyO.machine
noncomputable def mNx1D := RecoveryFocus.machine mNx1 moveM
noncomputable def mNx2D := RecoveryFocus.machine mNx2 moveM
/-- One stack record merged with one label record (tapes: 0 stack, 1 pool, 2 scratch). -/
noncomputable def mergeBodyM :=
  Composition.machine mCp1D (Composition.machine mLeftD (Composition.machine mCp2D (Composition.machine mNx1D mNx2D)))

/-- The cost of one merged record. -/
def mergeCost (a b : ℕ) : ℕ := (2 * a + 1) + 1 + (1 + 1 + ((2 * b + 1) + 1 + (1 + 1 + 1)))

/-- **One merged record**: the scratch stream gets `frame (w ++ v)`; both sources step past their records. -/
theorem merge_body (preS w tailS preP v tailP acc BW : List Bool) :
    Step mergeBodyM (mergeCost w.length v.length) ![preS.length, preP.length, acc.length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay acc BW]
      ![preS.length + (2 * w.length + 1), preP.length + (2 * v.length + 1), (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW] := by
  have c1 := dockRun (copyStep preS w tailS acc BW) mCp1 mCp1_inj ![preS.length, preP.length, acc.length]
    ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay acc BW]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_mCp1, dockH_mCp1] at c1
  have c1' : Step mCp1D (2 * w.length + 1) ![preS.length, preP.length, acc.length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay acc BW]
      ![preS.length + 2 * w.length, preP.length, (acc.length + 2 * w.length) + 1]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW] :=
    c1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have l := dockRun (moveLStep (overlay (acc ++ frame w) BW) (acc.length + 2 * w.length)) mLeft mLeft_inj
    ![preS.length + 2 * w.length, preP.length, (acc.length + 2 * w.length) + 1]
    ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_mLeft, dockH_mLeft] at l
  have hov : overlay (acc ++ fpre w) (overlay (acc ++ frame w) BW) = overlay (acc ++ frame w) BW := by
    have : acc ++ frame w = (acc ++ fpre w) ++ [false] := by rw [List.append_assoc, frame_fpre]
    rw [this, overlay_prefix]
  have hfl : (acc ++ fpre w).length = acc.length + 2 * w.length := by simp [fpre_length]
  have l' : Step mLeftD 1 ![preS.length + 2 * w.length, preP.length, (acc.length + 2 * w.length) + 1]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW]
      ![preS.length + 2 * w.length, preP.length, (acc ++ fpre w).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW] :=
    l.congr (by funext i; fin_cases i <;> first | rfl | exact hfl.symm) (by funext i; fin_cases i <;> rfl)
  have c2 := dockRun (copyStep preP v tailP (acc ++ fpre w) (overlay (acc ++ frame w) BW)) mCp2 mCp2_inj
    ![preS.length + 2 * w.length, preP.length, (acc ++ fpre w).length]
    ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> first | rfl | exact hov.symm)
  rw [install_mCp2, dockH_mCp2] at c2
  have hw : overlay (acc ++ fpre w ++ frame v) (overlay (acc ++ frame w) BW) = overlay (acc ++ frame (w ++ v)) BW := by
    rw [overlay_collapse' _ _ _ (by simp [fpre_length]), List.append_assoc, ← frame_append']
  have hlen2 : (acc ++ fpre w).length + (2 * v.length + 1) = (acc ++ frame (w ++ v)).length := by
    simp [fpre_length, frame_append']; omega
  have c2' : Step mCp2D (2 * v.length + 1) ![preS.length + 2 * w.length, preP.length, (acc ++ fpre w).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame w) BW]
      ![preS.length + 2 * w.length, preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW] := by
    refine c2.congr ?_ ?_
    · funext i; fin_cases i
      · rfl
      · rfl
      · exact hlen2
    · funext i; fin_cases i
      · rfl
      · rfl
      · exact hw
  have n1 := dockRun (moveStep (preS ++ frame w ++ tailS) (preS.length + 2 * w.length)) mNx1 mNx1_inj
    ![preS.length + 2 * w.length, preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
    ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_mNx1, dockH_mNx1] at n1
  have n1' : Step mNx1D 1 ![preS.length + 2 * w.length, preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW]
      ![preS.length + (2 * w.length + 1), preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW] :=
    n1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have n2 := dockRun (moveStep (preP ++ frame v ++ tailP) (preP.length + 2 * v.length)) mNx2 mNx2_inj
    ![preS.length + (2 * w.length + 1), preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
    ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_mNx2, dockH_mNx2] at n2
  have n2' : Step mNx2D 1
      ![preS.length + (2 * w.length + 1), preP.length + 2 * v.length, (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW]
      ![preS.length + (2 * w.length + 1), preP.length + (2 * v.length + 1), (acc ++ frame (w ++ v)).length]
      ![preS ++ frame w ++ tailS, preP ++ frame v ++ tailP, overlay (acc ++ frame (w ++ v)) BW] :=
    n2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact c1'.seq (l'.seq (c2'.seq (n1'.seq n2')))

/-- The merge fold: the next stack record joined with the label record of the same index. -/
def mergeF (lr : List (List Bool)) (acc : List (List Bool)) (r : List Bool) : List (List Bool) :=
  acc ++ [r ++ lr.getD acc.length []]

theorem foldl_mergeF (rs lr : List (List Bool)) (hlen : rs.length = lr.length) :
    ∀ j, j ≤ rs.length → (rs.take j).foldl (mergeF lr) [] = (List.zipWith (· ++ ·) rs lr).take j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, List.foldl_append,
      foldl_mergeF rs lr hlen j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, mergeF]
    have hl : ((List.zipWith (· ++ ·) rs lr).take j).length = j := by simp; omega
    rw [hl, List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.getElem_zipWith,
      List.getD_eq_getElem _ _ (by omega)]

/-- **All stack records merged with the label's records**: the scratch stream gets the merged records. -/
theorem merge_loop (rs lr : List (List Bool)) (hlen : rs.length = lr.length) (L1 L2 : ℕ)
    (hrs : ∀ r ∈ rs, r.length = L1) (hlr : ∀ r ∈ lr, r.length = L2) (hL1 : 1 ≤ L1)
    (stale1 pre0 rest BW : List Bool) :
    Step (StreamController.machine mergeBodyM 0) (rs.length * (mergeCost L1 L2 + 2) + 1)
      ![0, pre0.length, 0] ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest), BW]
      ![(rs.flatMap frame).length, pre0.length + (lr.flatMap frame).length,
        ((List.zipWith (· ++ ·) rs lr).flatMap frame).length]
      ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest),
        overlay ((List.zipWith (· ++ ·) rs lr).flatMap frame) BW] := by
  have h := streamRun mergeBodyM 0 rs stale1 (fun r hr h0 => by have := hrs r hr; rw [h0] at this; simp at this; omega)
    (mergeF lr) [] (fun acc p => ![p, pre0.length + off lr acc.length, (acc.flatMap frame).length])
    (fun acc => ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest), overlay (acc.flatMap frame) BW])
    (fun _ => rfl) (fun _ _ => rfl) (mergeCost L1 L2) (by
      intro j hj
      have hj' : j < lr.length := by omega
      have e0 := foldl_mergeF rs lr hlen j (by omega)
      have e1 := foldl_mergeF rs lr hlen (j + 1) (by omega)
      have hl0 : ((List.zipWith (· ++ ·) rs lr).take j).length = j := by simp; omega
      have hl1 : ((List.zipWith (· ++ ·) rs lr).take (j + 1)).length = j + 1 := by simp; omega
      have hb := merge_body ((rs.take j).flatMap frame) rs[j] ((rs.drop (j + 1)).flatMap frame ++ false :: stale1)
        (pre0 ++ (lr.take j).flatMap frame) lr[j] ((lr.drop (j + 1)).flatMap frame ++ rest)
        (((List.zipWith (· ++ ·) rs lr).take j).flatMap frame) BW
      rw [← streamTape_split rs stale1 j hj, ← split_at pre0 rest lr j hj', hrs _ (List.getElem_mem hj),
        hlr _ (List.getElem_mem hj')] at hb
      have hacc : ((List.zipWith (· ++ ·) rs lr).take j).flatMap frame ++ frame (rs[j] ++ lr[j]) =
          ((List.zipWith (· ++ ·) rs lr).take (j + 1)).flatMap frame := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
          List.getElem_zipWith]
        simp
      rw [hacc] at hb
      have ho1 := off_succ rs j hj
      have ho2 := off_succ lr j hj'
      rw [hrs _ (List.getElem_mem hj)] at ho1
      rw [hlr _ (List.getElem_mem hj')] at ho2
      rw [e0, e1, hl0, hl1]
      refine (hb.congr_in ?_ rfl).congr ?_ rfl
      · funext i; fin_cases i
        · rfl
        · show (pre0 ++ (lr.take j).flatMap frame).length = pre0.length + off lr j
          simp [off]
        · rfl
      · funext i; fin_cases i
        · show off rs j + (2 * L1 + 1) = off rs (j + 1)
          rw [ho1]
        · show (pre0 ++ (lr.take j).flatMap frame).length + (2 * L2 + 1) = pre0.length + off lr (j + 1)
          rw [ho2]; simp [off]; omega
        · rfl)
  have ef : rs.foldl (mergeF lr) [] = List.zipWith (· ++ ·) rs lr := by
    have := foldl_mergeF rs lr hlen rs.length le_rfl
    rw [List.take_length] at this
    rw [this, List.take_of_length_le (by simp)]
  rw [ef] at h
  have hz : (List.zipWith (· ++ ·) rs lr).length = lr.length := by simp; omega
  rw [hz, off_length] at h
  exact h

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
