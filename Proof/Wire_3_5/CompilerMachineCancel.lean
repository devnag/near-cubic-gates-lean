import Proof.Wire_3_5.CompilerMachineKit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The word-level reference -/

/-- Insert a word by symmetric difference: an equal word already present is removed with it. -/
def symInsertW (G : List (List Bool)) (x : List Bool) : List (List Bool) :=
  if x ∈ G then G.filter (· ≠ x) else G ++ [x]

/-- One record of the filter pass: the kept records, the found flag, the register, the equality cell. -/
def fstep (x : List Bool) (st : List (List Bool) × Bool × List Bool × Bool) (r : List Bool) :
    List (List Bool) × Bool × List Bool × Bool :=
  (if r = x then st.1 else st.1 ++ [r], st.2.1 || decide (r = x), r, decide (r = x))

theorem foldl_fstep (x : List Bool) : ∀ (G : List (List Bool)) (st : List (List Bool) × Bool × List Bool × Bool),
    (G.foldl (fstep x) st).1 = st.1 ++ G.filter (· ≠ x) ∧ (G.foldl (fstep x) st).2.1 = (st.2.1 || decide (x ∈ G)) ∧
      ((G.foldl (fstep x) st).2.2.1 = st.2.2.1 ∨ (G.foldl (fstep x) st).2.2.1 ∈ G)
  | [], st => by simp
  | r :: G, st => by
    obtain ⟨h1, h2, h3⟩ := foldl_fstep x G (fstep x st r)
    rw [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      by_cases hr : r = x
      · simp [fstep, hr]
      · simp [fstep, hr]
    · rw [h2]
      by_cases hr : r = x
      · simp [fstep, hr]
      · have hr' : x ≠ r := fun h => hr h.symm
        simp [fstep, hr, hr']
    · rcases h3 with h | h
      · right; rw [h]; simp [fstep]
      · right; exact List.mem_cons_of_mem r h

/-! ## The layout and the machines -/

def sLoad : Fin 3 → Fin 7 := ![0, 3, 6]
def sNudgeS : Fin 1 → Fin 7 := ![0]
def sEq : Fin 4 → Fin 7 := ![3, 2, 4, 6]
def sSetF : Fin 1 → Fin 7 := ![5]
def sEmitY : Fin 3 → Fin 7 := ![3, 1, 6]
def sEmitX : Fin 3 → Fin 7 := ![2, 1, 6]
def sPutO : Fin 1 → Fin 7 := ![1]
def sCopyOS : Fin 2 → Fin 7 := ![1, 0]
def sNudgeO : Fin 1 → Fin 7 := ![1]
def sPutS : Fin 1 → Fin 7 := ![0]

noncomputable def loadD := RecoveryFocus.machine sLoad loadM
noncomputable def nudgeSD := RecoveryFocus.machine sNudgeS nudgeM
noncomputable def eqD := RecoveryFocus.machine sEq eqM
noncomputable def setFD := RecoveryFocus.machine sSetF (cellM true)
noncomputable def clrFD := RecoveryFocus.machine sSetF (cellM false)
noncomputable def emitYD := RecoveryFocus.machine sEmitY emitM
noncomputable def emitXD := RecoveryFocus.machine sEmitX emitM
noncomputable def putOD := RecoveryFocus.machine sPutO (putM false)
noncomputable def copyOSD := RecoveryFocus.machine sCopyOS CopyO.machine
noncomputable def nudgeOD := RecoveryFocus.machine sNudgeO nudgeM
noncomputable def putSD := RecoveryFocus.machine sPutS (putM false)

/-- The filter pass's record body: load, step past the frame, compare, then drop (set `F`) or copy out. -/
noncomputable def filterBodyM :=
  Composition.machine (Composition.machine (Composition.machine loadD nudgeSD) eqD) (branchM 4 setFD emitYD)

/-- The filter pass: the stream loop, then `X` unless found, the terminator, and `F` cleared. -/
noncomputable def filterLoopM :=
  Composition.machine (Composition.machine (Composition.machine (StreamController.machine filterBodyM 0)
    (branchM 5 (idle 7) emitXD)) putOD) clrFD

/-- The copy-back pass's record body: copy the record from `O` onto `S`, step past its frame. -/
noncomputable def copyBodyM := Composition.machine copyOSD nudgeOD

noncomputable def copyLoopM := Composition.machine (StreamController.machine copyBodyM 1) putSD

def selSO : Fin 7 → Bool := ![true, true, false, false, false, false, false]

noncomputable def filterPassM := MaskedReset.machine filterLoopM selSO
noncomputable def copyPassM := MaskedReset.machine copyLoopM selSO

/-- **The insertion machine**: the filter pass, then the copy-back pass. -/
noncomputable def symM := Composition.machine filterPassM copyPassM

/-! ## The docked steps, generic in the untouched tapes -/

section Docked
variable (cap : ℕ) (T0 T1 T2 T3 T4 T5 : List Bool) (h0 h1 : ℕ)

theorem load_step (pre r post y : List Bool) (hl : y.length = r.length) (hcap : 2 * r.length + 1 ≤ cap) :
    Step loadD (2 * (2 * r.length + 1) + 2) ![pre.length, h1, 0, 0, 0, 0, 0]
      ![pre ++ frame r ++ post, T1, T2, frame y, T4, T5, List.replicate cap false]
      ![pre.length + 2 * r.length, h1, 0, 0, 0, 0, 0]
      ![pre ++ frame r ++ post, T1, T2, frame r, T4, T5, List.replicate cap false] := by
  have e0 := loadStep pre r post (frame y) cap hcap
  rw [overlay_exact _ _ (by simp [frame_length, hl])] at e0
  have e1 := dockRun e0 sLoad (by decide) ![pre.length, h1, 0, 0, 0, 0, 0]
    ![pre ++ frame r ++ post, T1, T2, frame y, T4, T5, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem nudgeS_step : Step nudgeSD 1 ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, List.replicate cap false]
    ![h0 + 1, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, List.replicate cap false] := by
  have e1 := dockRun (nudge_run T0 h0) sNudgeS (by decide) ![h0, h1, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, List.replicate cap false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem eq_step (x r : List Bool) (e : Bool) (hl : r.length = x.length) (hcap : 2 * r.length + 1 ≤ cap) :
    Step eqD (2 * (2 * r.length + 1) + 2) ![h0, h1, 0, 0, 0, 0, 0]
      ![T0, T1, frame x, frame r, [e], T5, List.replicate cap false] ![h0, h1, 0, 0, 0, 0, 0]
      ![T0, T1, frame x, frame r, [decide (r = x)], T5, List.replicate cap false] := by
  have e0 := eqStep r x e hl cap hcap
  have e1 := dockRun e0 sEq (by decide) ![h0, h1, 0, 0, 0, 0, 0]
    ![T0, T1, frame x, frame r, [e], T5, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem setF_step (f : Bool) : Step setFD 1 ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, [f], List.replicate cap false]
    ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, [true], List.replicate cap false] := by
  have e1 := dockRun (cellStep true f) sSetF (by decide) ![h0, h1, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, [f], List.replicate cap false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem clrF_step (f : Bool) : Step clrFD 1 ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, [f], List.replicate cap false]
    ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, [false], List.replicate cap false] := by
  have e1 := dockRun (cellStep false f) sSetF (by decide) ![h0, h1, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, [f], List.replicate cap false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem emitY_step (w out BW : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step emitYD (2 * (2 * w.length + 1) + 2) ![h0, out.length, 0, 0, 0, 0, 0]
      ![T0, overlay out BW, T2, frame w, T4, T5, List.replicate cap false]
      ![h0, out.length + (2 * w.length + 1), 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ frame w) BW, T2, frame w, T4, T5, List.replicate cap false] := by
  have e1 := dockRun (emitStep w out BW cap hcap) sEmitY (by decide) ![h0, out.length, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, T2, frame w, T4, T5, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem emitX_step (w out BW : List Bool) (hcap : 2 * w.length + 1 ≤ cap) :
    Step emitXD (2 * (2 * w.length + 1) + 2) ![h0, out.length, 0, 0, 0, 0, 0]
      ![T0, overlay out BW, frame w, T3, T4, T5, List.replicate cap false]
      ![h0, out.length + (2 * w.length + 1), 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ frame w) BW, frame w, T3, T4, T5, List.replicate cap false] := by
  have e1 := dockRun (emitStep w out BW cap hcap) sEmitX (by decide) ![h0, out.length, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, frame w, T3, T4, T5, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem putO_step (out BW : List Bool) :
    Step putOD 1 ![h0, out.length, 0, 0, 0, 0, 0] ![T0, overlay out BW, T2, T3, T4, T5, List.replicate cap false]
      ![h0, out.length + 1, 0, 0, 0, 0, 0]
      ![T0, overlay (out ++ [false]) BW, T2, T3, T4, T5, List.replicate cap false] := by
  have e0 := putStep false (overlay out BW) out.length
  rw [overlay_write] at e0
  have e1 := dockRun e0 sPutO (by decide) ![h0, out.length, 0, 0, 0, 0, 0]
    ![T0, overlay out BW, T2, T3, T4, T5, List.replicate cap false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem copyOS_step (pre w post out BW : List Bool) :
    Step copyOSD (2 * w.length + 1) ![out.length, pre.length, 0, 0, 0, 0, 0]
      ![overlay out BW, pre ++ frame w ++ post, T2, T3, T4, T5, List.replicate cap false]
      ![out.length + (2 * w.length + 1), pre.length + 2 * w.length, 0, 0, 0, 0, 0]
      ![overlay (out ++ frame w) BW, pre ++ frame w ++ post, T2, T3, T4, T5, List.replicate cap false] := by
  have e1 := dockRun (copyStep pre w post out BW) sCopyOS (by decide) ![out.length, pre.length, 0, 0, 0, 0, 0]
    ![overlay out BW, pre ++ frame w ++ post, T2, T3, T4, T5, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem nudgeO_step : Step nudgeOD 1 ![h0, h1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, List.replicate cap false]
    ![h0, h1 + 1, 0, 0, 0, 0, 0] ![T0, T1, T2, T3, T4, T5, List.replicate cap false] := by
  have e1 := dockRun (nudge_run T1 h1) sNudgeO (by decide) ![h0, h1, 0, 0, 0, 0, 0]
    ![T0, T1, T2, T3, T4, T5, List.replicate cap false] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

theorem putS_step (out BW : List Bool) :
    Step putSD 1 ![out.length, h1, 0, 0, 0, 0, 0] ![overlay out BW, T1, T2, T3, T4, T5, List.replicate cap false]
      ![out.length + 1, h1, 0, 0, 0, 0, 0]
      ![overlay (out ++ [false]) BW, T1, T2, T3, T4, T5, List.replicate cap false] := by
  have e0 := putStep false (overlay out BW) out.length
  rw [overlay_write] at e0
  have e1 := dockRun e0 sPutS (by decide) ![out.length, h1, 0, 0, 0, 0, 0]
    ![overlay out BW, T1, T2, T3, T4, T5, List.replicate cap false] (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  refine e1.congr ?_ ?_ <;> funext i <;> fin_cases i <;> slot_eval

end Docked

end NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
