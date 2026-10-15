import Proof.Wire_3_5.CompilerMachineMasksLookup
import Proof.Wire_3_5.CompilerMachineUnionsWord

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **One atom's expansion on words**: every running word joined with every child word. -/
def expandW (L Ea : List (List Bool)) : List (List Bool) := L.flatMap fun U => Ea.map (orW U)

def xLoadE : Fin 3 → Fin 7 := ![2, 4, 6]
def xNudgeE : Fin 1 → Fin 7 := ![2]
def xOr : Fin 4 → Fin 7 := ![3, 4, 5, 6]
def xEmit : Fin 3 → Fin 7 := ![5, 1, 6]
def xLoadL : Fin 3 → Fin 8 := ![0, 3, 6]
def xNudgeL : Fin 1 → Fin 8 := ![0]
def xPutB : Fin 1 → Fin 8 := ![1]

noncomputable def xLoadED := RecoveryFocus.machine xLoadE loadM
noncomputable def xNudgeED := RecoveryFocus.machine xNudgeE nudgeM
noncomputable def xOrD := RecoveryFocus.machine xOr (zipM orOut keep false)
noncomputable def xEmitD := RecoveryFocus.machine xEmit emitM
/-- Inner body: load the child, step past it, join it with `U`, write the union out. -/
noncomputable def xInnerBodyM :=
  Composition.machine (Composition.machine (Composition.machine xLoadED xNudgeED) xOrD) xEmitD
noncomputable def xInnerLoopM := StreamController.machine xInnerBodyM 2
def xSelE : Fin 7 → Bool := ![false, false, true, false, false, false, false]
/-- The inner loop with `Ea`'s head returned to cell 0 (log on tape 7). -/
noncomputable def xInnerM := MaskedReset.machine xInnerLoopM xSelE

noncomputable def xLoadLD := RecoveryFocus.machine xLoadL loadM
noncomputable def xNudgeLD := RecoveryFocus.machine xNudgeL nudgeM
noncomputable def xPutBD := RecoveryFocus.machine xPutB (putM false)
/-- Outer body: load `U`, step past it, run the inner loop. -/
noncomputable def xOuterBodyM := Composition.machine (Composition.machine xLoadLD xNudgeLD) xInnerM
noncomputable def xOuterLoopM := StreamController.machine xOuterBodyM 0
noncomputable def xLoopM := Composition.machine xOuterLoopM xPutBD
def xSelLB : Fin 8 → Bool := ![true, true, false, false, false, false, false, false]
/-- **The expansion machine**: the outer loop, the terminator, both lists' heads back at cell 0 (log on tape 8). -/
noncomputable def expandM := MaskedReset.machine xLoopM xSelLB

theorem xLoadE_inj : Function.Injective xLoadE := by decide

theorem install_xLoadE (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install xLoadE A v = ![A 0, A 1, v 0, A 3, v 1, A 5, v 2] := by
  funext i
  fin_cases i
  · exact install_other xLoadE A v 0 (by decide)
  · exact install_other xLoadE A v 1 (by decide)
  · exact install_slot xLoadE xLoadE_inj A v 0
  · exact install_other xLoadE A v 3 (by decide)
  · exact install_slot xLoadE xLoadE_inj A v 1
  · exact install_other xLoadE A v 5 (by decide)
  · exact install_slot xLoadE xLoadE_inj A v 2

theorem dockH_xLoadE (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH xLoadE H v = ![H 0, H 1, v 0, H 3, v 1, H 5, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other xLoadE H v 0 (by decide)
  · exact dockH_other xLoadE H v 1 (by decide)
  · exact dockH_slot xLoadE xLoadE_inj H v 0
  · exact dockH_other xLoadE H v 3 (by decide)
  · exact dockH_slot xLoadE xLoadE_inj H v 1
  · exact dockH_other xLoadE H v 5 (by decide)
  · exact dockH_slot xLoadE xLoadE_inj H v 2

theorem xNudgeE_inj : Function.Injective xNudgeE := by decide

theorem install_xNudgeE (A : Fin 7 → List Bool) (v : Fin 1 → List Bool) :
    install xNudgeE A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6] := by
  funext i
  fin_cases i
  · exact install_other xNudgeE A v 0 (by decide)
  · exact install_other xNudgeE A v 1 (by decide)
  · exact install_slot xNudgeE xNudgeE_inj A v 0
  · exact install_other xNudgeE A v 3 (by decide)
  · exact install_other xNudgeE A v 4 (by decide)
  · exact install_other xNudgeE A v 5 (by decide)
  · exact install_other xNudgeE A v 6 (by decide)

theorem dockH_xNudgeE (H : Fin 7 → ℕ) (v : Fin 1 → ℕ) :
    dockH xNudgeE H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6] := by
  funext i
  fin_cases i
  · exact dockH_other xNudgeE H v 0 (by decide)
  · exact dockH_other xNudgeE H v 1 (by decide)
  · exact dockH_slot xNudgeE xNudgeE_inj H v 0
  · exact dockH_other xNudgeE H v 3 (by decide)
  · exact dockH_other xNudgeE H v 4 (by decide)
  · exact dockH_other xNudgeE H v 5 (by decide)
  · exact dockH_other xNudgeE H v 6 (by decide)

theorem xOr_inj : Function.Injective xOr := by decide

theorem install_xOr (A : Fin 7 → List Bool) (v : Fin 4 → List Bool) :
    install xOr A v = ![A 0, A 1, A 2, v 0, v 1, v 2, v 3] := by
  funext i
  fin_cases i
  · exact install_other xOr A v 0 (by decide)
  · exact install_other xOr A v 1 (by decide)
  · exact install_other xOr A v 2 (by decide)
  · exact install_slot xOr xOr_inj A v 0
  · exact install_slot xOr xOr_inj A v 1
  · exact install_slot xOr xOr_inj A v 2
  · exact install_slot xOr xOr_inj A v 3

theorem dockH_xOr (H : Fin 7 → ℕ) (v : Fin 4 → ℕ) :
    dockH xOr H v = ![H 0, H 1, H 2, v 0, v 1, v 2, v 3] := by
  funext i
  fin_cases i
  · exact dockH_other xOr H v 0 (by decide)
  · exact dockH_other xOr H v 1 (by decide)
  · exact dockH_other xOr H v 2 (by decide)
  · exact dockH_slot xOr xOr_inj H v 0
  · exact dockH_slot xOr xOr_inj H v 1
  · exact dockH_slot xOr xOr_inj H v 2
  · exact dockH_slot xOr xOr_inj H v 3

theorem xEmit_inj : Function.Injective xEmit := by decide

theorem install_xEmit (A : Fin 7 → List Bool) (v : Fin 3 → List Bool) :
    install xEmit A v = ![A 0, v 1, A 2, A 3, A 4, v 0, v 2] := by
  funext i
  fin_cases i
  · exact install_other xEmit A v 0 (by decide)
  · exact install_slot xEmit xEmit_inj A v 1
  · exact install_other xEmit A v 2 (by decide)
  · exact install_other xEmit A v 3 (by decide)
  · exact install_other xEmit A v 4 (by decide)
  · exact install_slot xEmit xEmit_inj A v 0
  · exact install_slot xEmit xEmit_inj A v 2

theorem dockH_xEmit (H : Fin 7 → ℕ) (v : Fin 3 → ℕ) :
    dockH xEmit H v = ![H 0, v 1, H 2, H 3, H 4, v 0, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other xEmit H v 0 (by decide)
  · exact dockH_slot xEmit xEmit_inj H v 1
  · exact dockH_other xEmit H v 2 (by decide)
  · exact dockH_other xEmit H v 3 (by decide)
  · exact dockH_other xEmit H v 4 (by decide)
  · exact dockH_slot xEmit xEmit_inj H v 0
  · exact dockH_slot xEmit xEmit_inj H v 2

theorem xLoadL_inj : Function.Injective xLoadL := by decide

theorem install_xLoadL (A : Fin 8 → List Bool) (v : Fin 3 → List Bool) :
    install xLoadL A v = ![v 0, A 1, A 2, v 1, A 4, A 5, v 2, A 7] := by
  funext i
  fin_cases i
  · exact install_slot xLoadL xLoadL_inj A v 0
  · exact install_other xLoadL A v 1 (by decide)
  · exact install_other xLoadL A v 2 (by decide)
  · exact install_slot xLoadL xLoadL_inj A v 1
  · exact install_other xLoadL A v 4 (by decide)
  · exact install_other xLoadL A v 5 (by decide)
  · exact install_slot xLoadL xLoadL_inj A v 2
  · exact install_other xLoadL A v 7 (by decide)

theorem dockH_xLoadL (H : Fin 8 → ℕ) (v : Fin 3 → ℕ) :
    dockH xLoadL H v = ![v 0, H 1, H 2, v 1, H 4, H 5, v 2, H 7] := by
  funext i
  fin_cases i
  · exact dockH_slot xLoadL xLoadL_inj H v 0
  · exact dockH_other xLoadL H v 1 (by decide)
  · exact dockH_other xLoadL H v 2 (by decide)
  · exact dockH_slot xLoadL xLoadL_inj H v 1
  · exact dockH_other xLoadL H v 4 (by decide)
  · exact dockH_other xLoadL H v 5 (by decide)
  · exact dockH_slot xLoadL xLoadL_inj H v 2
  · exact dockH_other xLoadL H v 7 (by decide)

theorem xNudgeL_inj : Function.Injective xNudgeL := by decide

theorem install_xNudgeL (A : Fin 8 → List Bool) (v : Fin 1 → List Bool) :
    install xNudgeL A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7] := by
  funext i
  fin_cases i
  · exact install_slot xNudgeL xNudgeL_inj A v 0
  · exact install_other xNudgeL A v 1 (by decide)
  · exact install_other xNudgeL A v 2 (by decide)
  · exact install_other xNudgeL A v 3 (by decide)
  · exact install_other xNudgeL A v 4 (by decide)
  · exact install_other xNudgeL A v 5 (by decide)
  · exact install_other xNudgeL A v 6 (by decide)
  · exact install_other xNudgeL A v 7 (by decide)

theorem dockH_xNudgeL (H : Fin 8 → ℕ) (v : Fin 1 → ℕ) :
    dockH xNudgeL H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7] := by
  funext i
  fin_cases i
  · exact dockH_slot xNudgeL xNudgeL_inj H v 0
  · exact dockH_other xNudgeL H v 1 (by decide)
  · exact dockH_other xNudgeL H v 2 (by decide)
  · exact dockH_other xNudgeL H v 3 (by decide)
  · exact dockH_other xNudgeL H v 4 (by decide)
  · exact dockH_other xNudgeL H v 5 (by decide)
  · exact dockH_other xNudgeL H v 6 (by decide)
  · exact dockH_other xNudgeL H v 7 (by decide)

theorem xPutB_inj : Function.Injective xPutB := by decide

theorem install_xPutB (A : Fin 8 → List Bool) (v : Fin 1 → List Bool) :
    install xPutB A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7] := by
  funext i
  fin_cases i
  · exact install_other xPutB A v 0 (by decide)
  · exact install_slot xPutB xPutB_inj A v 0
  · exact install_other xPutB A v 2 (by decide)
  · exact install_other xPutB A v 3 (by decide)
  · exact install_other xPutB A v 4 (by decide)
  · exact install_other xPutB A v 5 (by decide)
  · exact install_other xPutB A v 6 (by decide)
  · exact install_other xPutB A v 7 (by decide)

theorem dockH_xPutB (H : Fin 8 → ℕ) (v : Fin 1 → ℕ) :
    dockH xPutB H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7] := by
  funext i
  fin_cases i
  · exact dockH_other xPutB H v 0 (by decide)
  · exact dockH_slot xPutB xPutB_inj H v 0
  · exact dockH_other xPutB H v 2 (by decide)
  · exact dockH_other xPutB H v 3 (by decide)
  · exact dockH_other xPutB H v 4 (by decide)
  · exact dockH_other xPutB H v 5 (by decide)
  · exact dockH_other xPutB H v 6 (by decide)
  · exact dockH_other xPutB H v 7 (by decide)

theorem zeroHeads4' : (![0, 0, 0, 0] : Fin 4 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

/-! ## The inner loop -/

def innerStep (U : List Bool) (st : List (List Bool) × List Bool × List Bool) (e : List Bool) :
    List (List Bool) × List Bool × List Bool :=
  (st.1 ++ [orW U e], e, orW U e)

theorem foldl_innerStep_outs (U : List Bool) : ∀ (Ea : List (List Bool)) (st : List (List Bool) × List Bool × List Bool),
    (Ea.foldl (innerStep U) st).1 = st.1 ++ Ea.map (orW U)
  | [], st => by simp
  | e :: Ea, st => by
    rw [List.foldl_cons, foldl_innerStep_outs U Ea]
    simp [innerStep]

theorem foldl_innerStep_regs (U : List Bool) (L : ℕ) (hU : U.length = L) : ∀ (Ea : List (List Bool))
    (st : List (List Bool) × List Bool × List Bool), (∀ e ∈ Ea, e.length = L) → st.2.1.length = L →
      st.2.2.length = L → (Ea.foldl (innerStep U) st).2.1.length = L ∧ (Ea.foldl (innerStep U) st).2.2.length = L
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | e :: Ea, st, hE, _, _ => by
    rw [List.foldl_cons]
    have he := hE e List.mem_cons_self
    refine foldl_innerStep_regs U L hU Ea _ (fun e' h' => hE e' (List.mem_cons_of_mem e h')) he ?_
    show (orW U e).length = L
    unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hU, he]), hU]

/-- The inner banks. -/
def iH (p q : ℕ) (outs : List (List Bool)) : Fin 7 → ℕ := ![p, (outs.flatMap frame).length, q, 0, 0, 0, 0]

def iA (LAt BW Et U : List Bool) (cap : ℕ) (st : List (List Bool) × List Bool × List Bool) : Fin 7 → List Bool :=
  ![LAt, overlay (st.1.flatMap frame) BW, Et, frame U, frame st.2.1, frame st.2.2, List.replicate cap false]

/-- The uniform cost of one child of the inner loop, at width `L`. -/
def innerCost (L : ℕ) : ℕ := 12 * L + 16

theorem inner_body (LAt BW pre e post U : List Bool) (cap L p : ℕ) (st : List (List Bool) × List Bool × List Bool)
    (he : e.length = L) (hU : U.length = L) (h2 : st.2.1.length = L) (h3 : st.2.2.length = L) (hcap : 2 * L + 1 ≤ cap) :
    Step xInnerBodyM (innerCost L) (iH p pre.length st.1) (iA LAt BW (pre ++ frame e ++ post) U cap st)
      (iH p (pre.length + (2 * e.length + 1)) (innerStep U st e).1)
      (iA LAt BW (pre ++ frame e ++ post) U cap (innerStep U st e)) := by
  obtain ⟨outs, r2, r3⟩ := st
  simp only at h2 h3
  have hor : (orW U e).length = L := by unfold orW; rw [ZipMap.map_length _ _ _ _ _ (by rw [hU, he]), hU]

  have e0 := loadStep pre e post (frame r2) cap (by omega)
  rw [overlay_exact _ _ (by simp [frame_length, h2, he])] at e0
  have s1 := dockRun e0 xLoadE xLoadE_inj (iH p pre.length outs)
    (iA LAt BW (pre ++ frame e ++ post) U cap (outs, r2, r3)) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [install_xLoadE, dockH_xLoadE] at s1
  -- step past it
  have s2 := dockRun (nudge_run (pre ++ frame e ++ post) (pre.length + 2 * e.length)) xNudgeE xNudgeE_inj
    ![p, (outs.flatMap frame).length, pre.length + 2 * e.length, 0, 0, 0, 0]
    ![LAt, overlay (outs.flatMap frame) BW, pre ++ frame e ++ post, frame U, frame e, frame r3, List.replicate cap false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_xNudgeE, dockH_xNudgeE] at s2
  -- join
  have e3 := zipStep orOut keep false U e (frame r3) (by rw [hU, he]) cap (by omega)
  rw [overlay_exact _ _ (by simp [frame_length, ZipMap.map_length orOut keep U e false (by rw [hU, he]), h3, hU]),
    zeroHeads4'] at e3
  have s3 := dockKeep e3 xOr xOr_inj ![p, (outs.flatMap frame).length, pre.length + 2 * e.length + 1, 0, 0, 0, 0]
    ![LAt, overlay (outs.flatMap frame) BW, pre ++ frame e ++ post, frame U, frame e, frame r3, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_xOr] at s3
  -- write the union out
  have s4 := dockRun (emitStep (orW U e) (outs.flatMap frame) BW cap (by rw [hor]; exact hcap)) xEmit xEmit_inj
    ![p, (outs.flatMap frame).length, pre.length + 2 * e.length + 1, 0, 0, 0, 0]
    ![LAt, overlay (outs.flatMap frame) BW, pre ++ frame e ++ post, frame U, frame e, frame (orW U e),
      List.replicate cap false] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_xEmit, dockH_xEmit] at s4
  have hall := ((s1.seq s2).seq s3).seq s4
  refine (hall.enlarge (by unfold innerCost; rw [hor, he]; omega)).congr ?_ ?_
  · funext i; fin_cases i <;> simp [iH, innerStep, frame_length]
    all_goals omega
  · funext i; fin_cases i <;> simp [iA, innerStep, orW]

theorem inner_loop (LAt BW : List Bool) (Ea : List (List Bool)) (staleE U : List Bool) (cap L p : ℕ)
    (st0 : List (List Bool) × List Bool × List Bool) (hE : ∀ e ∈ Ea, e.length = L) (hL : 1 ≤ L) (hU : U.length = L)
    (h2 : st0.2.1.length = L) (h3 : st0.2.2.length = L) (hcap : 2 * L + 1 ≤ cap) :
    Step xInnerLoopM (Ea.length * (innerCost L + 2) + 1) (iH p 0 st0.1)
      (iA LAt BW (streamTape Ea staleE) U cap st0) (iH p (Ea.flatMap frame).length (Ea.foldl (innerStep U) st0).1)
      (iA LAt BW (streamTape Ea staleE) U cap (Ea.foldl (innerStep U) st0)) := by
  refine streamRun xInnerBodyM 2 Ea staleE (fun r hr h => by have := hE r hr; rw [h] at this; simp at this; omega)
    (innerStep U) st0 (fun st q => iH p q st.1) (fun st => iA LAt BW (streamTape Ea staleE) U cap st)
    (fun _ => rfl) (fun _ _ => rfl) (innerCost L) ?_
  intro j hj
  have hlen := hE _ (List.getElem_mem hj)
  have hst : (Ea.take (j + 1)).foldl (innerStep U) st0 = innerStep U ((Ea.take j).foldl (innerStep U) st0) Ea[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  obtain ⟨r2, r3⟩ := foldl_innerStep_regs U L hU (Ea.take j) st0 (fun e he => hE e (List.mem_of_mem_take he)) h2 h3
  have hb := inner_body LAt BW ((Ea.take j).flatMap frame) Ea[j] ((Ea.drop (j + 1)).flatMap frame ++ false :: staleE) U
    cap L p ((Ea.take j).foldl (innerStep U) st0) hlen hU r2 r3 hcap
  rw [← streamTape_split Ea staleE j hj] at hb
  rw [hst, off_succ Ea j hj]
  exact hb

/-- The inner loop with its reset, as an 8-tape step. -/
theorem inner_run (LAt BW : List Bool) (Ea : List (List Bool)) (staleE U : List Bool) (cap cap2 L p : ℕ)
    (st0 : List (List Bool) × List Bool × List Bool) (hE : ∀ e ∈ Ea, e.length = L) (hL : 1 ≤ L) (hU : U.length = L)
    (h2 : st0.2.1.length = L) (h3 : st0.2.2.length = L) (hcap : 2 * L + 1 ≤ cap)
    (hcap2 : Ea.length * (innerCost L + 2) + 1 ≤ cap2) :
    Step xInnerM (2 * (Ea.length * (innerCost L + 2) + 1) + 2) ![p, (st0.1.flatMap frame).length, 0, 0, 0, 0, 0, 0]
      ![LAt, overlay (st0.1.flatMap frame) BW, streamTape Ea staleE, frame U, frame st0.2.1, frame st0.2.2,
        List.replicate cap false, List.replicate cap2 false]
      ![p, ((Ea.foldl (innerStep U) st0).1.flatMap frame).length, 0, 0, 0, 0, 0, 0]
      ![LAt, overlay ((Ea.foldl (innerStep U) st0).1.flatMap frame) BW, streamTape Ea staleE, frame U,
        frame (Ea.foldl (innerStep U) st0).2.1, frame (Ea.foldl (innerStep U) st0).2.2, List.replicate cap false,
        List.replicate cap2 false] := by
  have h := inner_loop LAt BW Ea staleE U cap L p st0 hE hL hU h2 h3 hcap
  have hm := h.mask (cap := cap2) xSelE (by intro i hi; fin_cases i <;> simp_all [xSelE, iH]) hcap2
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-! ## The outer loop -/

def outerStep (Ea : List (List Bool)) (st : List (List Bool) × List Bool × List Bool × List Bool) (U : List Bool) :
    List (List Bool) × List Bool × List Bool × List Bool :=
  ((Ea.foldl (innerStep U) (st.1, st.2.2.1, st.2.2.2)).1, U, (Ea.foldl (innerStep U) (st.1, st.2.2.1, st.2.2.2)).2.1,
    (Ea.foldl (innerStep U) (st.1, st.2.2.1, st.2.2.2)).2.2)

theorem foldl_outerStep_outs (Ea : List (List Bool)) : ∀ (Lw : List (List Bool))
    (st : List (List Bool) × List Bool × List Bool × List Bool),
    (Lw.foldl (outerStep Ea) st).1 = st.1 ++ expandW Lw Ea
  | [], st => by simp [expandW]
  | U :: Lw, st => by
    rw [List.foldl_cons, foldl_outerStep_outs Ea Lw]
    simp [outerStep, foldl_innerStep_outs, expandW]

theorem foldl_outerStep_regs (Ea : List (List Bool)) (L : ℕ) (hE : ∀ e ∈ Ea, e.length = L) :
    ∀ (Lw : List (List Bool)) (st : List (List Bool) × List Bool × List Bool × List Bool),
      (∀ U ∈ Lw, U.length = L) → st.2.1.length = L → st.2.2.1.length = L → st.2.2.2.length = L →
      (Lw.foldl (outerStep Ea) st).2.1.length = L ∧ (Lw.foldl (outerStep Ea) st).2.2.1.length = L ∧
        (Lw.foldl (outerStep Ea) st).2.2.2.length = L
  | [], _, _, h1, h2, h3 => ⟨h1, h2, h3⟩
  | U :: Lw, st, hL, _, h2, h3 => by
    rw [List.foldl_cons]
    have hU := hL U List.mem_cons_self
    obtain ⟨g2, g3⟩ := foldl_innerStep_regs U L hU Ea (st.1, st.2.2.1, st.2.2.2) hE h2 h3
    exact foldl_outerStep_regs Ea L hE Lw _ (fun U' h' => hL U' (List.mem_cons_of_mem U h')) hU g2 g3

def oH (q : ℕ) (outs : List (List Bool)) : Fin 8 → ℕ := ![q, (outs.flatMap frame).length, 0, 0, 0, 0, 0, 0]

def oA (LAt BW Et : List Bool) (cap cap2 : ℕ) (st : List (List Bool) × List Bool × List Bool × List Bool) :
    Fin 8 → List Bool :=
  ![LAt, overlay (st.1.flatMap frame) BW, Et, frame st.2.1, frame st.2.2.1, frame st.2.2.2, List.replicate cap false,
    List.replicate cap2 false]

/-- The uniform cost of one running word of the outer loop, for at most `K` children of width `L`. -/
def outerCost (K L : ℕ) : ℕ := 2 * (2 * L + 1) + 2 + 1 + 1 + 1 + (2 * (K * (innerCost L + 2) + 1) + 2)

theorem outer_body (pre U post BW : List Bool) (Ea : List (List Bool)) (staleE : List Bool) (cap cap2 K L : ℕ)
    (st : List (List Bool) × List Bool × List Bool × List Bool) (hE : ∀ e ∈ Ea, e.length = L) (hK : Ea.length ≤ K)
    (hL : 1 ≤ L) (hU : U.length = L) (h1 : st.2.1.length = L) (h2 : st.2.2.1.length = L) (h3 : st.2.2.2.length = L)
    (hcap : 2 * L + 1 ≤ cap) (hcap2 : K * (innerCost L + 2) + 1 ≤ cap2) :
    Step xOuterBodyM (outerCost K L) (oH pre.length st.1) (oA (pre ++ frame U ++ post) BW (streamTape Ea staleE) cap cap2 st)
      (oH (pre.length + (2 * U.length + 1)) (outerStep Ea st U).1)
      (oA (pre ++ frame U ++ post) BW (streamTape Ea staleE) cap cap2 (outerStep Ea st U)) := by
  obtain ⟨outs, R, R2, R3⟩ := st
  simp only at h1 h2 h3
  have e0 := loadStep pre U post (frame R) cap (by omega)
  rw [overlay_exact _ _ (by simp [frame_length, h1, hU])] at e0
  have s1 := dockRun e0 xLoadL xLoadL_inj (oH pre.length outs)
    (oA (pre ++ frame U ++ post) BW (streamTape Ea staleE) cap cap2 (outs, R, R2, R3))
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_xLoadL, dockH_xLoadL] at s1
  have s2 := dockRun (nudge_run (pre ++ frame U ++ post) (pre.length + 2 * U.length)) xNudgeL xNudgeL_inj
    ![pre.length + 2 * U.length, (outs.flatMap frame).length, 0, 0, 0, 0, 0, 0]
    ![pre ++ frame U ++ post, overlay (outs.flatMap frame) BW, streamTape Ea staleE, frame U, frame R2, frame R3,
      List.replicate cap false, List.replicate cap2 false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_xNudgeL, dockH_xNudgeL] at s2
  have s3 := inner_run (pre ++ frame U ++ post) BW Ea staleE U cap cap2 L (pre.length + 2 * U.length + 1) (outs, R2, R3)
    hE hL hU h2 h3 hcap ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hK) 1).trans hcap2)
  have hall := (s1.seq s2).seq s3
  have hc := Nat.mul_le_mul_right (innerCost L + 2) hK
  refine (hall.enlarge (by unfold outerCost; rw [hU]; omega)).congr ?_ ?_
  · funext i; fin_cases i <;> simp [oH, outerStep]
    all_goals omega
  · funext i; fin_cases i <;> simp [oA, outerStep]

theorem outer_loop (Lw : List (List Bool)) (staleA BW : List Bool) (Ea : List (List Bool)) (staleE : List Bool)
    (cap cap2 K L : ℕ) (st0 : List (List Bool) × List Bool × List Bool × List Bool) (hLw : ∀ U ∈ Lw, U.length = L)
    (hE : ∀ e ∈ Ea, e.length = L) (hK : Ea.length ≤ K) (hL : 1 ≤ L) (h1 : st0.2.1.length = L)
    (h2 : st0.2.2.1.length = L) (h3 : st0.2.2.2.length = L) (hcap : 2 * L + 1 ≤ cap)
    (hcap2 : K * (innerCost L + 2) + 1 ≤ cap2) :
    Step xOuterLoopM (Lw.length * (outerCost K L + 2) + 1) (oH 0 st0.1)
      (oA (streamTape Lw staleA) BW (streamTape Ea staleE) cap cap2 st0)
      (oH (Lw.flatMap frame).length (Lw.foldl (outerStep Ea) st0).1)
      (oA (streamTape Lw staleA) BW (streamTape Ea staleE) cap cap2 (Lw.foldl (outerStep Ea) st0)) := by
  refine streamRun xOuterBodyM 0 Lw staleA (fun r hr h => by have := hLw r hr; rw [h] at this; simp at this; omega)
    (outerStep Ea) st0 (fun st q => oH q st.1) (fun st => oA (streamTape Lw staleA) BW (streamTape Ea staleE) cap cap2 st)
    (fun _ => rfl) (fun _ _ => rfl) (outerCost K L) ?_
  intro j hj
  have hlen := hLw _ (List.getElem_mem hj)
  have hst : (Lw.take (j + 1)).foldl (outerStep Ea) st0 = outerStep Ea ((Lw.take j).foldl (outerStep Ea) st0) Lw[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  obtain ⟨g1, g2, g3⟩ := foldl_outerStep_regs Ea L hE (Lw.take j) st0 (fun U hU => hLw U (List.mem_of_mem_take hU)) h1 h2 h3
  have hb := outer_body ((Lw.take j).flatMap frame) Lw[j] ((Lw.drop (j + 1)).flatMap frame ++ false :: staleA) BW Ea
    staleE cap cap2 K L ((Lw.take j).foldl (outerStep Ea) st0) hE hK hL hlen g1 g2 g3 hcap hcap2
  rw [← streamTape_split Lw staleA j hj] at hb
  rw [hst, off_succ Lw j hj]
  exact hb

/-- The cost of the expansion before its reset, `m` running words, at most `K` children of width `L`. -/
def expandLoopCost (m K L : ℕ) : ℕ := m * (outerCost K L + 2) + 1 + 1 + 1

theorem expand_run (Lw : List (List Bool)) (staleA BW : List Bool) (Ea : List (List Bool)) (staleE R R2 R3 : List Bool)
    (cap cap2 cap3 K L : ℕ) (hLw : ∀ U ∈ Lw, U.length = L) (hE : ∀ e ∈ Ea, e.length = L) (hK : Ea.length ≤ K)
    (hL : 1 ≤ L) (h1 : R.length = L) (h2 : R2.length = L) (h3 : R3.length = L) (hcap : 2 * L + 1 ≤ cap)
    (hcap2 : K * (innerCost L + 2) + 1 ≤ cap2) (hcap3 : expandLoopCost Lw.length K L ≤ cap3) :
    Step expandM (2 * expandLoopCost Lw.length K L + 2) (fun _ => 0)
      ![streamTape Lw staleA, BW, streamTape Ea staleE, frame R, frame R2, frame R3, List.replicate cap false,
        List.replicate cap2 false, List.replicate cap3 false]
      (fun _ => 0)
      ![streamTape Lw staleA, streamTape (expandW Lw Ea) (BW.drop (((expandW Lw Ea).flatMap frame).length + 1)),
        streamTape Ea staleE, frame (Lw.foldl (outerStep Ea) ([], R, R2, R3)).2.1,
        frame (Lw.foldl (outerStep Ea) ([], R, R2, R3)).2.2.1, frame (Lw.foldl (outerStep Ea) ([], R, R2, R3)).2.2.2,
        List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false] := by
  have hL1 := outer_loop Lw staleA BW Ea staleE cap cap2 K L ([], R, R2, R3) hLw hE hK hL h1 h2 h3 hcap hcap2
  have hout : (Lw.foldl (outerStep Ea) ([], R, R2, R3)).1 = expandW Lw Ea := by
    rw [foldl_outerStep_outs]; rfl
  set fin := Lw.foldl (outerStep Ea) ([], R, R2, R3)
  have hL1' := hL1.congr (hout' := oH (Lw.flatMap frame).length (expandW Lw Ea))
    (tout' := ![streamTape Lw staleA, overlay ((expandW Lw Ea).flatMap frame) BW, streamTape Ea staleE, frame fin.2.1,
      frame fin.2.2.1, frame fin.2.2.2, List.replicate cap false, List.replicate cap2 false])
    (by rw [hout]) (by funext i; fin_cases i <;> simp [oA, hout])
  have s2 := dockRun (putStep false (overlay ((expandW Lw Ea).flatMap frame) BW) ((expandW Lw Ea).flatMap frame).length)
    xPutB xPutB_inj (oH (Lw.flatMap frame).length (expandW Lw Ea))
    ![streamTape Lw staleA, overlay ((expandW Lw Ea).flatMap frame) BW, streamTape Ea staleE, frame fin.2.1,
      frame fin.2.2.1, frame fin.2.2.2, List.replicate cap false, List.replicate cap2 false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_xPutB, dockH_xPutB, overlay_write, overlay_stream] at s2
  have hall := hL1'.seq s2
  have hm := (hall.enlarge (m := expandLoopCost Lw.length K L) (by unfold expandLoopCost; omega)).mask (cap := cap3)
    xSelLB (by intro i hi; fin_cases i <;> simp_all [xSelLB, oH]) hcap3
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Masks
