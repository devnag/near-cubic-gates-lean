import Proof.Wire_3_5.CompilerMachineEmitMerge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def aPut : Fin 1 → Fin 3 := ![2]
def cDst : Fin 1 → Fin 3 := ![0]
def kS1 : Fin 1 → Fin 2 := ![0]
def kPL : Fin 1 → Fin 2 := ![1]

theorem aPut_inj : Function.Injective aPut := by decide

theorem install_aPut (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install aPut A v = ![A 0, A 1, v 0] := by
  funext i
  fin_cases i
  · exact install_other aPut A v 0 (by decide)
  · exact install_other aPut A v 1 (by decide)
  · exact install_slot aPut aPut_inj A v 0

theorem dockH_aPut (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH aPut H v = ![H 0, H 1, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other aPut H v 0 (by decide)
  · exact dockH_other aPut H v 1 (by decide)
  · exact dockH_slot aPut aPut_inj H v 0

theorem cDst_inj : Function.Injective cDst := by decide

theorem install_cDst (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install cDst A v = ![v 0, A 1, A 2] := by
  funext i
  fin_cases i
  · exact install_slot cDst cDst_inj A v 0
  · exact install_other cDst A v 1 (by decide)
  · exact install_other cDst A v 2 (by decide)

theorem dockH_cDst (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH cDst H v = ![v 0, H 1, H 2] := by
  funext i
  fin_cases i
  · exact dockH_slot cDst cDst_inj H v 0
  · exact dockH_other cDst H v 1 (by decide)
  · exact dockH_other cDst H v 2 (by decide)

theorem kS1_inj : Function.Injective kS1 := by decide

theorem install_kS1 (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install kS1 A v = ![v 0, A 1] := by
  funext i
  fin_cases i
  · exact install_slot kS1 kS1_inj A v 0
  · exact install_other kS1 A v 1 (by decide)

theorem dockH_kS1 (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH kS1 H v = ![v 0, H 1] := by
  funext i
  fin_cases i
  · exact dockH_slot kS1 kS1_inj H v 0
  · exact dockH_other kS1 H v 1 (by decide)

theorem kPL_inj : Function.Injective kPL := by decide

theorem install_kPL (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install kPL A v = ![A 0, v 0] := by
  funext i
  fin_cases i
  · exact install_other kPL A v 0 (by decide)
  · exact install_slot kPL kPL_inj A v 0

theorem dockH_kPL (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH kPL H v = ![H 0, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other kPL H v 0 (by decide)
  · exact dockH_slot kPL kPL_inj H v 0

noncomputable def aPutD := RecoveryFocus.machine aPut (putM false)
/-- The merge loop and the scratch stream's terminator (tapes: 0 stack, 1 pool, 2 scratch). -/
noncomputable def mergeAllM := Composition.machine (StreamController.machine mergeBodyM 0) aPutD

/-- **One label merged into the stack**: the scratch stream holds the merged records. -/
theorem mergeAll_step (rs lr : List (List Bool)) (hlen : rs.length = lr.length) (L1 L2 : ℕ)
    (hrs : ∀ r ∈ rs, r.length = L1) (hlr : ∀ r ∈ lr, r.length = L2) (hL1 : 1 ≤ L1)
    (stale1 pre0 rest BW : List Bool) :
    Step mergeAllM (rs.length * (mergeCost L1 L2 + 2) + 1 + 1 + 1)
      ![0, pre0.length, 0] ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest), BW]
      ![(rs.flatMap frame).length, pre0.length + (lr.flatMap frame).length,
        ((List.zipWith (· ++ ·) rs lr).flatMap frame).length + 1]
      ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest),
        overlay (streamTape (List.zipWith (· ++ ·) rs lr) []) BW] := by
  have m := merge_loop rs lr hlen L1 L2 hrs hlr hL1 stale1 pre0 rest BW
  set M := List.zipWith (· ++ ·) rs lr
  have p := dockRun (putStep false (overlay (M.flatMap frame) BW) (M.flatMap frame).length) aPut aPut_inj
    ![(rs.flatMap frame).length, pre0.length + (lr.flatMap frame).length, (M.flatMap frame).length]
    ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest), overlay (M.flatMap frame) BW]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_aPut, dockH_aPut, overlay_write] at p
  have p' := p.congr (hout' := ![(rs.flatMap frame).length, pre0.length + (lr.flatMap frame).length,
      (M.flatMap frame).length + 1])
    (tout' := ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest), overlay (streamTape M []) BW])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact m.seq p'

theorem write_zero (D : List Bool) : writeTapeBit D 0 false = false :: D.tail := by
  cases D <;> rfl

def cPut : Fin 1 → Fin 3 := ![0]

noncomputable def cPutD := RecoveryFocus.machine cDst (putM false)
noncomputable def cLeftD := RecoveryFocus.machine cDst moveLM
/-- **Copy a stream over a destination** (tapes: 0 destination, 1 source, 2 log). -/
noncomputable def copyS := Composition.machine cPutD (Composition.machine cLeftD appendResetM)

/-- **The stream copy**: the destination becomes `overlay (streamTape N []) D`; all heads back at cell `0`. -/
theorem copyS_step (N : List (List Bool)) (staleO D : List Bool) (W cap : ℕ) (hN : ∀ r ∈ N, r.length = W)
    (hW : 1 ≤ W) (hcap : appendCost 0 N.length W ≤ cap) :
    Step copyS (1 + 1 + (1 + 1 + (2 * appendCost 0 N.length W + 2))) ![0, 0, 0]
      ![D, streamTape N staleO, List.replicate cap false] ![0, 0, 0]
      ![overlay (streamTape N []) D, streamTape N staleO, List.replicate cap false] := by
  have p := dockRun (putStep false D 0) cDst cDst_inj ![0, 0, 0] ![D, streamTape N staleO, List.replicate cap false]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_cDst, dockH_cDst, write_zero] at p
  have l := dockRun (moveLStep (false :: D.tail) 0) cDst cDst_inj ![1, 0, 0]
    ![false :: D.tail, streamTape N staleO, List.replicate cap false] (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [install_cDst, dockH_cDst] at l
  have a := appendRun [] N D.tail staleO W cap (by simp) hN hW hcap
  simp only [List.nil_append] at a
  have hS : streamTape [] D.tail = false :: D.tail := rfl
  rw [hS] at a
  have hD : streamTape N ((false :: D.tail).drop ((N.flatMap frame).length + 1)) = overlay (streamTape N []) D := by
    rw [List.drop_succ_cons]
    cases D with
    | nil => simp [overlay, streamTape]
    | cons b D' => simp [overlay, streamTape, List.append_assoc]
  rw [hD] at a
  have p' := p.congr (hout' := ![1, 0, 0]) (tout' := ![false :: D.tail, streamTape N staleO, List.replicate cap false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have l' := l.congr (hout' := ![0, 0, 0]) (tout' := ![false :: D.tail, streamTape N staleO, List.replicate cap false])
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have a' : Step appendResetM (2 * appendCost 0 N.length W + 2) ![0, 0, 0]
      ![false :: D.tail, streamTape N staleO, List.replicate cap false] ![0, 0, 0]
      ![overlay (streamTape N []) D, streamTape N staleO, List.replicate cap false] :=
    (a.congr_in (by funext i; fin_cases i <;> rfl) rfl).congr (by funext i; fin_cases i <;> rfl) rfl
  exact p'.seq (l'.seq a')

noncomputable def kS1D := RecoveryFocus.machine kS1 skipM
noncomputable def kPLD := RecoveryFocus.machine kPL skipM
/-- One stack record and one label record skipped (tapes: 0 stack, 1 pool). -/
noncomputable def skipBodyM := Composition.machine kS1D kPLD

/-- **A label outside the mask**: its records and the stack's records skipped in lockstep. -/
theorem skip_loop2 (rs lr : List (List Bool)) (hlen : rs.length = lr.length) (L1 L2 : ℕ)
    (hrs : ∀ r ∈ rs, r.length = L1) (hlr : ∀ r ∈ lr, r.length = L2) (hL1 : 1 ≤ L1)
    (stale1 pre0 rest : List Bool) :
    Step (StreamController.machine skipBodyM 0) (rs.length * ((2 * L1 + 1) + 1 + (2 * L2 + 1) + 2) + 1)
      ![0, pre0.length] ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)]
      ![(rs.flatMap frame).length, pre0.length + (lr.flatMap frame).length]
      ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)] := by
  have h := streamRun skipBodyM 0 rs stale1 (fun r hr h0 => by have := hrs r hr; rw [h0] at this; simp at this; omega)
    (fun (n : ℕ) _ => n + 1) 0 (fun n p => ![p, pre0.length + off lr n])
    (fun _ => ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)])
    (fun _ => rfl) (fun _ _ => rfl) ((2 * L1 + 1) + 1 + (2 * L2 + 1)) (by
      intro j hj
      have hj' : j < lr.length := by omega
      have hcount : ∀ i, i ≤ rs.length → (rs.take i).foldl (fun (n : ℕ) _ => n + 1) 0 = i := by
        intro i hi
        rw [List.foldl_const]
        simp; omega
      rw [hcount j (by omega), hcount (j + 1) (by omega)]
      have s1 := skipStep ((rs.take j).flatMap frame) rs[j] ((rs.drop (j + 1)).flatMap frame ++ false :: stale1)
      rw [← streamTape_split rs stale1 j hj, hrs _ (List.getElem_mem hj)] at s1
      have d1 := dockRun s1 kS1 kS1_inj ![off rs j, pre0.length + off lr j]
        ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)] (by intro k; fin_cases k; rfl)
        (by intro k; fin_cases k; rfl)
      rw [install_kS1, dockH_kS1] at d1
      have s2 := skipStep (pre0 ++ (lr.take j).flatMap frame) lr[j] ((lr.drop (j + 1)).flatMap frame ++ rest)
      rw [← split_at pre0 rest lr j hj', hlr _ (List.getElem_mem hj')] at s2
      have d2 := dockRun s2 kPL kPL_inj ![off rs (j + 1), pre0.length + off lr j]
        ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)] (by intro k; fin_cases k; simp [kPL, off])
        (by intro k; fin_cases k; rfl)
      rw [install_kPL, dockH_kPL] at d2
      have ho1 := off_succ rs j hj
      have ho2 := off_succ lr j hj'
      rw [hrs _ (List.getElem_mem hj)] at ho1
      rw [hlr _ (List.getElem_mem hj')] at ho2
      have d1' := d1.congr (hout' := ![off rs (j + 1), pre0.length + off lr j])
        (tout' := ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)])
        (by funext i; fin_cases i
            · show ((rs.take j).flatMap frame).length + 2 * L1 + 1 = off rs (j + 1)
              rw [ho1]; rfl
            · rfl)
        (by funext i; fin_cases i <;> rfl)
      have d2' := d2.congr (hout' := ![off rs (j + 1), pre0.length + off lr (j + 1)])
        (tout' := ![streamTape rs stale1, pre0 ++ (lr.flatMap frame ++ rest)])
        (by funext i; fin_cases i
            · rfl
            · show (pre0 ++ (lr.take j).flatMap frame).length + 2 * L2 + 1 = pre0.length + off lr (j + 1)
              rw [ho2]; simp [off]; omega)
        (by funext i; fin_cases i <;> rfl)
      exact d1'.seq d2')
  have hcount : rs.foldl (fun (n : ℕ) _ => n + 1) 0 = lr.length := by rw [List.foldl_const]; simp; omega
  rw [hcount, off_length] at h
  exact h

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
