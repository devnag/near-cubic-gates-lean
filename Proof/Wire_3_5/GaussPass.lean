import Proof.Wire_3_5.GaussRef
import Proof.Wire_3_5.BlockCopy
import Proof.Wire_3_5.BlockBranch
import Proof.Wire_3_5.BlockWhile
import Proof.Wire_3_5.BlockPorts

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Gauss
open NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The pass, row by row -/

/-- One row of the pass. The state is the pivot's tail once found, then the emitted rows. -/
def rowStep (st : Option (List Bool) × List (List Bool)) (r : List Bool) : Option (List Bool) × List (List Bool) :=
  match st.1 with
  | none => if r.headD false then (some r.tail, st.2) else (none, st.2 ++ [r.tail])
  | some p => (some p, st.2 ++ [if r.headD false then List.zipWith xor r.tail p else r.tail])

/-- The pass state after the first `j` rows. -/
def prefixState (reps : List (List Bool)) (j : ℕ) : Option (List Bool) × List (List Bool) :=
  (reps.take j).foldl rowStep (none, [])

theorem prefixState_succ (reps : List (List Bool)) (j : ℕ) (hj : j < reps.length) :
    prefixState reps (j + 1) = rowStep (prefixState reps j) reps[j] := by
  unfold prefixState
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

theorem fold_rowStep (reps : List (List Bool)) (st : Option (List Bool) × List (List Bool)) :
    (reps.foldl rowStep st).2 = st.2 ++ pass st.1 reps ∧ ((reps.foldl rowStep st).1.isSome = (st.1.isSome || found reps)) := by
  induction reps generalizing st with
  | nil =>
    rcases st with ⟨s, out⟩
    cases s <;> simp [pass, found]
  | cons r rs ih =>
    rw [List.foldl_cons]
    rcases st with ⟨s, out⟩
    cases s with
    | none =>
      cases hb : r.headD false
      · have e : rowStep (none, out) r = (none, out ++ [r.tail]) := by
          simp only [rowStep, hb, Bool.false_eq_true, ↓reduceIte]
        rw [e]
        obtain ⟨h1, h2⟩ := ih (none, out ++ [r.tail])
        refine ⟨?_, ?_⟩
        · rw [h1]; simp only [pass, hb, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.singleton_append]
        · rw [h2]; simp only [found, List.any_cons, hb, Option.isSome_none, Bool.false_or]
      · have e : rowStep (none, out) r = (some r.tail, out) := by
          simp only [rowStep, hb, ↓reduceIte]
        rw [e]
        obtain ⟨h1, h2⟩ := ih (some r.tail, out)
        refine ⟨?_, ?_⟩
        · rw [h1]; simp only [pass, hb, ↓reduceIte]
        · rw [h2]; simp only [found, List.any_cons, hb, Option.isSome_some, Option.isSome_none, Bool.true_or,
            Bool.false_or]
    | some p =>
      have e : rowStep (some p, out) r =
          (some p, out ++ [if r.headD false then List.zipWith xor r.tail p else r.tail]) := rfl
      rw [e]
      obtain ⟨h1, h2⟩ := ih _
      refine ⟨?_, ?_⟩
      · rw [h1]; simp only [pass, List.append_assoc, List.singleton_append]
      · rw [h2]; simp only [Option.isSome_some, Bool.true_or]

/-- **The row-by-row pass is `pass`**, and its final state records whether a pivot was found. -/
theorem prefixState_all (reps : List (List Bool)) :
    (prefixState reps reps.length).2 = pass none reps ∧ (prefixState reps reps.length).1.isSome = found reps := by
  unfold prefixState
  rw [List.take_length]
  obtain ⟨h1, h2⟩ := fold_rowStep reps (none, [])
  exact ⟨by simpa using h1, by simpa using h2⟩

/-! ## Small machines: one step right, one written bit -/

/-- Move the head one cell right. -/
def nudge : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem nudge_run (tape : List Bool) (h : ℕ) :
    ∃ r, runFrom nudge 1 ⟨nudge.start, ![h], ![tape]⟩ = some r ∧ r.final.heads = ![h + 1] ∧ r.final.tapes = ![tape] := by
  have hs : step nudge ⟨nudge.start, ![h], ![tape]⟩ = some ⟨1, ![h + 1], ![tape]⟩ := by
    simp [step, nudge]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, _⟩ := (RecoveryExecution.Timed.single (p := nudge) (by rfl) hs).run (by rfl)
  exact ⟨r, hr, by rw [hf], by rw [hf]⟩

noncomputable def nudgeBlock (tape : List Bool) (h : ℕ) : Block 1 :=
  ofRunFrom nudge 1 ![h] ![tape] (by obtain ⟨r, hr, _⟩ := nudge_run tape h; exact ⟨r, hr⟩)

theorem nudgeBlock_spec (tape : List Bool) (h : ℕ) :
    (nudgeBlock tape h).entryH = ![h] ∧ (nudgeBlock tape h).entryA = ![tape] ∧
      (nudgeBlock tape h).exitH = ![h + 1] ∧ (nudgeBlock tape h).exitA = ![tape] ∧ (nudgeBlock tape h).cost = 1 := by
  obtain ⟨r, hr, hh, ht⟩ := nudge_run tape h
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · rw [nudgeBlock, ofRunFrom_exitH _ _ _ _ _ r hr, hh]
  · rw [nudgeBlock, ofRunFrom_exitA _ _ _ _ _ r hr, ht]

/-- Write a fixed bit under the head, without moving. -/
def writeM (b : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some b, fun _ => .stay⟩ else none

theorem write_run (b x : Bool) :
    ∃ r, runFrom (writeM b) 1 ⟨(writeM b).start, ![0], ![[x]]⟩ = some r ∧ r.final.heads = ![0] ∧ r.final.tapes = ![[b]] := by
  have hs : step (writeM b) ⟨(writeM b).start, ![0], ![[x]]⟩ = some ⟨1, ![0], ![[b]]⟩ := by
    simp [step, writeM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, _⟩ := (RecoveryExecution.Timed.single (p := writeM b) (by rfl) hs).run (by rfl)
  exact ⟨r, hr, by rw [hf], by rw [hf]⟩

noncomputable def writeBlock (b x : Bool) : Block 1 :=
  ofRunFrom (writeM b) 1 ![0] ![[x]] (by obtain ⟨r, hr, _⟩ := write_run b x; exact ⟨r, hr⟩)

theorem writeBlock_spec (b x : Bool) :
    (writeBlock b x).entryH = ![0] ∧ (writeBlock b x).entryA = ![[x]] ∧
      (writeBlock b x).exitH = ![0] ∧ (writeBlock b x).exitA = ![[b]] ∧ (writeBlock b x).cost = 1 := by
  obtain ⟨r, hr, hh, ht⟩ := write_run b x
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · rw [writeBlock, ofRunFrom_exitH _ _ _ _ _ r hr, hh]
  · rw [writeBlock, ofRunFrom_exitA _ _ _ _ _ r hr, ht]

/-! ## The row layout: tape 0 rows, 1 output, 2 pivot, 3 flag -/

theorem inst_other {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool) (v : Fin t → List Bool) (i : Fin u)
    (h : ∀ j, slots j ≠ i) : install slots A v i = A i := install_other slots A v i h

/-- Evaluate an install or a head dock at a concrete tape of a concrete layout. -/
macro "port_eval" : tactic => `(tactic| first
  | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1
  | exact install_slot _ (by decide) _ _ 2
  | exact install_other _ _ _ _ (by decide)
  | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1
  | exact dockH_slot _ (by decide) _ _ 2
  | exact dockH_other _ _ _ _ (by decide))

def portR : PortMap 1 4 := PortMap.ofVec ![0] (by decide)
def portRW : PortMap 2 4 := PortMap.ofVec ![0, 1] (by decide)
def portRP : PortMap 2 4 := PortMap.ofVec ![0, 2] (by decide)
def portRPW : PortMap 3 4 := PortMap.ofVec ![0, 2, 1] (by decide)
def portF : PortMap 1 4 := PortMap.ofVec ![3] (by decide)

/-- Step the rows' head one cell right. -/
noncomputable def nudgeR (x0 x1 x2 x3 : List Bool) (r w p : ℕ) : Block 4 :=
  congrExit (dock (nudgeBlock x0 r) portR ![r, w, p, 0] ![x0, x1, x2, x3]
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl))
    (H := ![r + 1, w, p, 0]) (A := ![x0, x1, x2, x3])
    (by
      obtain ⟨_, _, hH, _, _⟩ := nudgeBlock_spec x0 r
      funext i
      change dockH portR.slot ![r, w, p, 0] (nudgeBlock x0 r).exitH i = _
      rw [hH]
      fin_cases i <;> port_eval)
    (by
      obtain ⟨_, _, _, hA, _⟩ := nudgeBlock_spec x0 r
      funext i
      change install portR.slot ![x0, x1, x2, x3] (nudgeBlock x0 r).exitA i = _
      rw [hA]
      fin_cases i <;> port_eval)

/-- Copy the row's framed tail onto the output tape, over its backing. -/
noncomputable def copyW (pre w post outW BW x2 x3 : List Bool) (p : ℕ) : Block 4 :=
  congrExit (dock (copyBlock pre w post outW BW) portRW ![pre.length, outW.length, p, 0]
      ![pre ++ frame w ++ post, overlay outW BW, x2, x3]
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl))
    (H := ![pre.length + 2 * w.length, outW.length + (2 * w.length + 1), p, 0])
    (A := ![pre ++ frame w ++ post, overlay (outW ++ frame w) BW, x2, x3])
    (by
      obtain ⟨_, _, _, hH, _⟩ := copyBlock_spec pre w post outW BW
      funext i
      change dockH portRW.slot _ (copyBlock pre w post outW BW).exitH i = _
      rw [hH]
      fin_cases i <;> port_eval)
    (by
      obtain ⟨_, _, hA, _, _⟩ := copyBlock_spec pre w post outW BW
      funext i
      change install portRW.slot _ (copyBlock pre w post outW BW).exitA i = _
      rw [hA]
      fin_cases i <;> port_eval)

/-- Copy the row's framed tail onto the pivot tape, from cell 0 over its old content. -/
noncomputable def copyP (pre w post x1 pc x3 : List Bool) (q : ℕ) : Block 4 :=
  congrExit (dock (copyBlock pre w post [] pc) portRP ![pre.length, q, 0, 0]
      ![pre ++ frame w ++ post, x1, overlay [] pc, x3]
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl))
    (H := ![pre.length + 2 * w.length, q, 2 * w.length + 1, 0])
    (A := ![pre ++ frame w ++ post, x1, overlay (frame w) pc, x3])
    (by
      obtain ⟨_, _, _, hH, _⟩ := copyBlock_spec pre w post [] pc
      funext i
      change dockH portRP.slot _ (copyBlock pre w post [] pc).exitH i = _
      rw [hH]
      fin_cases i
      · exact dockH_slot _ (by decide) _ _ 0
      · exact dockH_other _ _ _ _ (by decide)
      · exact (dockH_slot _ (by decide) _ _ 1).trans (by simp)
      · exact dockH_other _ _ _ _ (by decide))
    (by
      obtain ⟨_, _, hA, _, _⟩ := copyBlock_spec pre w post [] pc
      funext i
      change install portRP.slot _ (copyBlock pre w post [] pc).exitA i = _
      rw [hA]
      fin_cases i <;> port_eval)

/-- XOR the row's framed tail with the pivot onto the output tape, over its backing. -/
noncomputable def xorW (pre w post piv tp outW BW x3 : List Bool) (hw : w.length = piv.length) : Block 4 :=
  congrExit (dock (mapBlockO xorOut keep false pre [] w piv post tp outW BW hw) portRPW ![pre.length, outW.length, 0, 0]
      ![pre ++ frame w ++ post, overlay outW BW, [] ++ frame piv ++ tp, x3]
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl))
    (H := ![pre.length + 2 * w.length, outW.length + (2 * w.length + 1), 2 * piv.length, 0])
    (A := ![pre ++ frame w ++ post, overlay (outW ++ frame (ZipMap.map xorOut keep w piv false)) BW,
      [] ++ frame piv ++ tp, x3])
    (by
      obtain ⟨_, _, _, hH, _⟩ := mapBlockO_spec xorOut keep false pre [] w piv post tp outW BW hw
      funext i
      change dockH portRPW.slot _ (mapBlockO xorOut keep false pre [] w piv post tp outW BW hw).exitH i = _
      rw [hH]
      fin_cases i
      · exact dockH_slot _ (by decide) _ _ 0
      · exact dockH_slot _ (by decide) _ _ 2
      · exact (dockH_slot _ (by decide) _ _ 1).trans (by simp)
      · exact dockH_other _ _ _ _ (by decide))
    (by
      obtain ⟨_, _, hA, _, _⟩ := mapBlockO_spec xorOut keep false pre [] w piv post tp outW BW hw
      funext i
      change install portRPW.slot _ (mapBlockO xorOut keep false pre [] w piv post tp outW BW hw).exitA i = _
      rw [hA]
      fin_cases i
      · exact install_slot _ (by decide) _ _ 0
      · exact install_slot _ (by decide) _ _ 2
      · exact install_slot _ (by decide) _ _ 1
      · exact install_other _ _ _ _ (by decide))

/-- Set the found flag. -/
noncomputable def writeF (x0 x1 x2 : List Bool) (x : Bool) (r w p : ℕ) : Block 4 :=
  congrExit (dock (writeBlock true x) portF ![r, w, p, 0] ![x0, x1, x2, [x]]
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl))
    (H := ![r, w, p, 0]) (A := ![x0, x1, x2, [true]])
    (by
      obtain ⟨_, _, hH, _, _⟩ := writeBlock_spec true x
      funext i
      change dockH portF.slot _ (writeBlock true x).exitH i = _
      rw [hH]
      fin_cases i <;> port_eval)
    (by
      obtain ⟨_, _, _, hA, _⟩ := writeBlock_spec true x
      funext i
      change install portF.slot _ (writeBlock true x).exitA i = _
      rw [hA]
      fin_cases i <;> port_eval)

/-! ### The banks of the docked stages (definitional) -/

section Banks
variable (x0 x1 x2 x3 pre w post outW BW pc piv tp : List Bool) (x : Bool) (r q p : ℕ)
@[simp] theorem nudgeR_entryH : (nudgeR x0 x1 x2 x3 r q p).entryH = ![r, q, p, 0] := rfl
@[simp] theorem nudgeR_entryA : (nudgeR x0 x1 x2 x3 r q p).entryA = ![x0, x1, x2, x3] := rfl
@[simp] theorem nudgeR_exitH : (nudgeR x0 x1 x2 x3 r q p).exitH = ![r + 1, q, p, 0] := rfl
@[simp] theorem nudgeR_exitA : (nudgeR x0 x1 x2 x3 r q p).exitA = ![x0, x1, x2, x3] := rfl
@[simp] theorem nudgeR_cost : (nudgeR x0 x1 x2 x3 r q p).cost = 1 := rfl
@[simp] theorem copyW_entryH : (copyW pre w post outW BW x2 x3 p).entryH = ![pre.length, outW.length, p, 0] := rfl
@[simp] theorem copyW_entryA : (copyW pre w post outW BW x2 x3 p).entryA =
    ![pre ++ frame w ++ post, overlay outW BW, x2, x3] := rfl
@[simp] theorem copyW_exitH : (copyW pre w post outW BW x2 x3 p).exitH =
    ![pre.length + 2 * w.length, outW.length + (2 * w.length + 1), p, 0] := rfl
@[simp] theorem copyW_exitA : (copyW pre w post outW BW x2 x3 p).exitA =
    ![pre ++ frame w ++ post, overlay (outW ++ frame w) BW, x2, x3] := rfl
@[simp] theorem copyW_cost : (copyW pre w post outW BW x2 x3 p).cost = 2 * w.length + 1 := rfl
@[simp] theorem copyP_entryH : (copyP pre w post x1 pc x3 q).entryH = ![pre.length, q, 0, 0] := rfl
@[simp] theorem copyP_entryA : (copyP pre w post x1 pc x3 q).entryA = ![pre ++ frame w ++ post, x1, overlay [] pc, x3] := rfl
@[simp] theorem copyP_exitH : (copyP pre w post x1 pc x3 q).exitH = ![pre.length + 2 * w.length, q, 2 * w.length + 1, 0] := rfl
@[simp] theorem copyP_exitA : (copyP pre w post x1 pc x3 q).exitA =
    ![pre ++ frame w ++ post, x1, overlay (frame w) pc, x3] := rfl
@[simp] theorem copyP_cost : (copyP pre w post x1 pc x3 q).cost = 2 * w.length + 1 := rfl
@[simp] theorem xorW_entryH (hw : w.length = piv.length) :
    (xorW pre w post piv tp outW BW x3 hw).entryH = ![pre.length, outW.length, 0, 0] := rfl
@[simp] theorem xorW_entryA (hw : w.length = piv.length) :
    (xorW pre w post piv tp outW BW x3 hw).entryA = ![pre ++ frame w ++ post, overlay outW BW, [] ++ frame piv ++ tp, x3] := rfl
@[simp] theorem xorW_exitH (hw : w.length = piv.length) :
    (xorW pre w post piv tp outW BW x3 hw).exitH =
      ![pre.length + 2 * w.length, outW.length + (2 * w.length + 1), 2 * piv.length, 0] := rfl
@[simp] theorem xorW_exitA (hw : w.length = piv.length) :
    (xorW pre w post piv tp outW BW x3 hw).exitA =
      ![pre ++ frame w ++ post, overlay (outW ++ frame (ZipMap.map xorOut keep w piv false)) BW, [] ++ frame piv ++ tp, x3] := rfl
@[simp] theorem xorW_cost (hw : w.length = piv.length) : (xorW pre w post piv tp outW BW x3 hw).cost = 2 * w.length + 1 := rfl
@[simp] theorem writeF_entryH : (writeF x0 x1 x2 x r q p).entryH = ![r, q, p, 0] := rfl
@[simp] theorem writeF_entryA : (writeF x0 x1 x2 x r q p).entryA = ![x0, x1, x2, [x]] := rfl
@[simp] theorem writeF_exitH : (writeF x0 x1 x2 x r q p).exitH = ![r, q, p, 0] := rfl
@[simp] theorem writeF_exitA : (writeF x0 x1 x2 x r q p).exitA = ![x0, x1, x2, [true]] := rfl
@[simp] theorem writeF_cost : (writeF x0 x1 x2 x r q p).cost = 1 := rfl
end Banks

/-! ## The uniform row machine and its four cases -/

noncomputable def nudgeRM := RecoveryFocus.machine portR.slot nudge
noncomputable def copyWM := RecoveryFocus.machine portRW.slot CopyO.machine
noncomputable def copyPM := RecoveryFocus.machine portRP.slot CopyO.machine
noncomputable def xorWM := RecoveryFocus.machine portRPW.slot (ZipMap.machine xorOut keep false)
noncomputable def writeFM := RecoveryFocus.machine portF.slot (writeM true)
noncomputable def copyCaseM := Composition.machine (Composition.machine nudgeRM copyWM) nudgeRM
noncomputable def xorCaseM := Composition.machine (Composition.machine nudgeRM xorWM) nudgeRM
noncomputable def pivotCaseM :=
  Composition.machine (Composition.machine (Composition.machine nudgeRM copyPM) nudgeRM) writeFM
/-- The row body: step onto the first bit, then branch on the flag and on that bit. -/
noncomputable def rowM :=
  Composition.machine nudgeRM (branchM 3 (branchM 0 xorCaseM copyCaseM) (branchM 0 pivotCaseM copyCaseM))
def selP : Fin 4 → Bool := ![false, false, true, false]
/-- The loop body: the row body, then the paid reset of the pivot's head. -/
noncomputable def bodyM := MaskedReset.machine rowM selP

section Cases
variable (pre tail post outW BW pc : List Bool) (b0 f : Bool)

/-- The row's framed source, with the rows' head just past its marker. -/
def rowSrc : List Bool := pre ++ frame (b0 :: tail) ++ post

theorem rowSrc_split : rowSrc pre tail post b0 = (pre ++ [true, b0]) ++ frame tail ++ post := by
  simp [rowSrc, frame, List.append_assoc]

/-- Copy the tail out: `nudge; copy; nudge`. -/
noncomputable def copyCase : Block 4 :=
  seq (seq (nudgeR (rowSrc pre tail post b0) (overlay outW BW) pc [f] (pre.length + 1) outW.length 0)
      (copyW (pre ++ [true, b0]) tail post outW BW pc [f] 0)
      (by funext i; fin_cases i <;> simp)
      (by funext i; fin_cases i <;> simp [rowSrc_split]))
    (nudgeR ((pre ++ [true, b0]) ++ frame tail ++ post) (overlay (outW ++ frame tail) BW) pc [f]
      ((pre ++ [true, b0]).length + 2 * tail.length) (outW.length + (2 * tail.length + 1)) 0)
    rfl rfl

/-- XOR the tail with the pivot: `nudge; xor; nudge`. -/
noncomputable def xorCase (piv tp : List Bool) (hpc : pc = frame piv ++ tp) (hw : tail.length = piv.length) : Block 4 :=
  seq (seq (nudgeR (rowSrc pre tail post b0) (overlay outW BW) pc [f] (pre.length + 1) outW.length 0)
      (xorW (pre ++ [true, b0]) tail post piv tp outW BW [f] hw)
      (by funext i; fin_cases i <;> simp)
      (by funext i; fin_cases i <;> simp [rowSrc_split, hpc]))
    (nudgeR ((pre ++ [true, b0]) ++ frame tail ++ post)
      (overlay (outW ++ frame (ZipMap.map xorOut keep tail piv false)) BW) ([] ++ frame piv ++ tp) [f]
      ((pre ++ [true, b0]).length + 2 * tail.length) (outW.length + (2 * tail.length + 1)) (2 * piv.length))
    rfl rfl

/-- Make the tail the pivot: `nudge; copy onto the pivot tape; nudge; set the flag`. -/
noncomputable def pivotCase : Block 4 :=
  seq (seq (seq (nudgeR (rowSrc pre tail post b0) (overlay outW BW) pc [f] (pre.length + 1) outW.length 0)
      (copyP (pre ++ [true, b0]) tail post (overlay outW BW) pc [f] outW.length)
      (by funext i; fin_cases i <;> simp)
      (by funext i; fin_cases i <;> simp [rowSrc_split, overlay]))
    (nudgeR ((pre ++ [true, b0]) ++ frame tail ++ post) (overlay outW BW) (overlay (frame tail) pc) [f]
      ((pre ++ [true, b0]).length + 2 * tail.length) outW.length (2 * tail.length + 1))
    rfl rfl)
    (writeF ((pre ++ [true, b0]) ++ frame tail ++ post) (overlay outW BW) (overlay (frame tail) pc) f
      ((pre ++ [true, b0]).length + 2 * tail.length + 1) outW.length (2 * tail.length + 1))
    rfl rfl

theorem copyCase_machine : (copyCase pre tail post outW BW pc b0 f).machine = copyCaseM := rfl
theorem xorCase_machine (piv tp : List Bool) (hpc : pc = frame piv ++ tp) (hw : tail.length = piv.length) :
    (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).machine = xorCaseM := rfl
theorem pivotCase_machine : (pivotCase pre tail post outW BW pc b0 f).machine = pivotCaseM := rfl

@[simp] theorem copyCase_entryH : (copyCase pre tail post outW BW pc b0 f).entryH = ![pre.length + 1, outW.length, 0, 0] := rfl
@[simp] theorem copyCase_entryA :
    (copyCase pre tail post outW BW pc b0 f).entryA = ![rowSrc pre tail post b0, overlay outW BW, pc, [f]] := rfl
@[simp] theorem copyCase_exitH : (copyCase pre tail post outW BW pc b0 f).exitH =
    ![(pre ++ [true, b0]).length + 2 * tail.length + 1, outW.length + (2 * tail.length + 1), 0, 0] := rfl
@[simp] theorem copyCase_exitA : (copyCase pre tail post outW BW pc b0 f).exitA =
    ![(pre ++ [true, b0]) ++ frame tail ++ post, overlay (outW ++ frame tail) BW, pc, [f]] := rfl
@[simp] theorem copyCase_cost : (copyCase pre tail post outW BW pc b0 f).cost = 2 * tail.length + 5 := by
  simp [copyCase]; omega

@[simp] theorem pivotCase_entryH : (pivotCase pre tail post outW BW pc b0 f).entryH = ![pre.length + 1, outW.length, 0, 0] := rfl
@[simp] theorem pivotCase_entryA :
    (pivotCase pre tail post outW BW pc b0 f).entryA = ![rowSrc pre tail post b0, overlay outW BW, pc, [f]] := rfl
@[simp] theorem pivotCase_exitH : (pivotCase pre tail post outW BW pc b0 f).exitH =
    ![(pre ++ [true, b0]).length + 2 * tail.length + 1, outW.length, 2 * tail.length + 1, 0] := rfl
@[simp] theorem pivotCase_exitA : (pivotCase pre tail post outW BW pc b0 f).exitA =
    ![(pre ++ [true, b0]) ++ frame tail ++ post, overlay outW BW, overlay (frame tail) pc, [true]] := rfl
@[simp] theorem pivotCase_cost : (pivotCase pre tail post outW BW pc b0 f).cost = 2 * tail.length + 7 := by
  simp [pivotCase]; omega

section
variable (piv tp : List Bool) (hpc : pc = frame piv ++ tp) (hw : tail.length = piv.length)
include hpc hw
@[simp] theorem xorCase_entryH : (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).entryH =
    ![pre.length + 1, outW.length, 0, 0] := rfl
@[simp] theorem xorCase_entryA : (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).entryA =
    ![rowSrc pre tail post b0, overlay outW BW, pc, [f]] := rfl
@[simp] theorem xorCase_exitH : (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).exitH =
    ![(pre ++ [true, b0]).length + 2 * tail.length + 1, outW.length + (2 * tail.length + 1), 2 * piv.length, 0] := rfl
@[simp] theorem xorCase_exitA : (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).exitA =
    ![(pre ++ [true, b0]) ++ frame tail ++ post, overlay (outW ++ frame (ZipMap.map xorOut keep tail piv false)) BW,
      [] ++ frame piv ++ tp, [f]] := rfl
@[simp] theorem xorCase_cost : (xorCase pre tail post outW BW pc b0 f piv tp hpc hw).cost = 2 * tail.length + 5 := by
  simp [xorCase]; omega
end

end Cases

/-! ### Banks through `seq` and the one-sided branches (definitional) -/

@[simp] theorem seq_entryA' {t : ℕ} (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) :
    (seq b c hH hA).entryA = b.entryA := rfl
@[simp] theorem seq_exitH' {t : ℕ} (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) :
    (seq b c hH hA).exitH = c.exitH := rfl
@[simp] theorem branchT_entryH {t : ℕ} (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂) (h : entryBit b.entryH b.entryA i = true) :
    (branchT i b q h).entryH = b.entryH := rfl
@[simp] theorem branchT_entryA {t : ℕ} (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂) (h : entryBit b.entryH b.entryA i = true) :
    (branchT i b q h).entryA = b.entryA := rfl
@[simp] theorem branchT_exitH {t : ℕ} (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂) (h : entryBit b.entryH b.entryA i = true) :
    (branchT i b q h).exitH = b.exitH := rfl
@[simp] theorem branchT_exitA {t : ℕ} (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂) (h : entryBit b.entryH b.entryA i = true) :
    (branchT i b q h).exitA = b.exitA := rfl
@[simp] theorem branchF_entryH {t : ℕ} (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t) (h : entryBit c.entryH c.entryA i = false) :
    (branchF i p c h).entryH = c.entryH := rfl
@[simp] theorem branchF_entryA {t : ℕ} (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t) (h : entryBit c.entryH c.entryA i = false) :
    (branchF i p c h).entryA = c.entryA := rfl
@[simp] theorem branchF_exitH {t : ℕ} (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t) (h : entryBit c.entryH c.entryA i = false) :
    (branchF i p c h).exitH = c.exitH := rfl
@[simp] theorem branchF_exitA {t : ℕ} (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t) (h : entryBit c.entryH c.entryA i = false) :
    (branchF i p c h).exitA = c.exitA := rfl

/-! ## One row of the pass, as one step of the loop body -/

/-- The pivot tape for a pass state: its old content before a pivot is found, then the pivot's frame over it. -/
def pivTape : Option (List Bool) → List Bool → List Bool
  | none, JP => JP
  | some p, JP => overlay (frame p) JP

/-- The pass layout's tapes before a row. -/
def rowTapes (SR : List Bool) (outs : List (List Bool)) (BW : List Bool) (st : Option (List Bool)) (JP : List Bool) :
    Fin 4 → List Bool :=
  ![SR, overlay (outs.flatMap frame) BW, pivTape st JP, [st.isSome]]

/-- The pass layout's heads before a row. -/
def rowHeads (h : ℕ) (outs : List (List Bool)) : Fin 4 → ℕ := ![h, (outs.flatMap frame).length, 0, 0]

/-- The uniform per-row cost bound of the loop body. -/
def rowCost (L : ℕ) : ℕ := 4 * L + 28

theorem readTapeBit_row (pre tail post : List Bool) (b0 : Bool) :
    readTapeBit (pre ++ frame (b0 :: tail) ++ post) (pre.length + 1) = b0 := by
  have := Streaming.read_append (pre ++ [true]) (frame tail ++ post) b0
  simpa [frame, List.append_assoc] using this

theorem readTapeBit_flag (f : Bool) : readTapeBit [f] 0 = f := by cases f <;> rfl

theorem pivTape_some (p JP : List Bool) : pivTape (some p) JP = frame p ++ JP.drop (frame p).length := rfl

/-- Close a bank equation of the row step: split the log tape off, evaluate the four row tapes. -/
macro "bank_eq" : tactic => `(tactic| (
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [masked, Fin.addCases_left, Fin.addCases_right] <;> (try fin_cases j) <;>
    simp [selP, rowHeads, rowTapes, rowStep, pivTape_some, pivTape, rowSrc, frame, List.append_assoc] <;> omega))

/-- **One row.** From the bank before row `b0 :: tail` in pass state `(st, outs)`, the loop body reaches the
bank before the next row in the state `rowStep (st, outs) (b0 :: tail)`. -/
theorem row_step (pre tail post BW JP : List Bool) (outs : List (List Bool)) (b0 : Bool) (st : Option (List Bool))
    (cap : ℕ) (hst : ∀ p, st = some p → p.length = tail.length) (hcap : 2 * tail.length + 13 ≤ cap) :
    Step bodyM (rowCost tail.length)
      (Fin.addCases (rowHeads pre.length outs) (fun _ : Fin 1 => 0))
      (Fin.addCases (rowTapes (pre ++ frame (b0 :: tail) ++ post) outs BW st JP)
        (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (rowHeads (pre.length + (2 * tail.length + 3)) (rowStep (st, outs) (b0 :: tail)).2)
        (fun _ : Fin 1 => 0))
      (Fin.addCases (rowTapes (pre ++ frame (b0 :: tail) ++ post) (rowStep (st, outs) (b0 :: tail)).2 BW
        (rowStep (st, outs) (b0 :: tail)).1 JP) (fun _ : Fin 1 => List.replicate cap false)) := by
  have hbit : ∀ (_pc : List Bool) (f : Bool), readTapeBit (rowSrc pre tail post b0) (pre.length + 1) = b0 ∧
      readTapeBit [f] 0 = f :=
    fun _ f => ⟨readTapeBit_row pre tail post b0, readTapeBit_flag f⟩
  cases st with
  | none =>
    cases b0 with
    | false =>
      have hm := (masked (seq (nudgeR (rowSrc pre tail post false) (overlay (outs.flatMap frame) BW) JP [false]
          pre.length (outs.flatMap frame).length 0)
        (branchF 3 (branchM 0 xorCaseM copyCaseM)
          (branchF 0 pivotCaseM (copyCase pre tail post (outs.flatMap frame) BW JP false false)
            (by simp [entryBit, (hbit JP false).1]))
          (by simp [entryBit, readTapeBit_flag])) rfl rfl) selP cap
        (by intro i hi; fin_cases i <;> simp_all [selP]) (by simp; omega)).run
      refine ((hm.enlarge (by simp [rowCost]; omega)).congr ?_ ?_).congr_in ?_ ?_ <;> bank_eq
    | true =>
      have hm := (masked (seq (nudgeR (rowSrc pre tail post true) (overlay (outs.flatMap frame) BW) JP [false]
          pre.length (outs.flatMap frame).length 0)
        (branchF 3 (branchM 0 xorCaseM copyCaseM)
          (branchT 0 (pivotCase pre tail post (outs.flatMap frame) BW JP true false) copyCaseM
            (by simp [entryBit, (hbit JP false).1]))
          (by simp [entryBit, readTapeBit_flag])) rfl rfl) selP cap
        (by intro i hi; fin_cases i <;> simp_all [selP]) (by simp; omega)).run
      refine ((hm.enlarge (by simp [rowCost]; omega)).congr ?_ ?_).congr_in ?_ ?_ <;> bank_eq
  | some p =>
    have hp : p.length = tail.length := hst p rfl
    cases b0 with
    | false =>
      have hm := (masked (seq (nudgeR (rowSrc pre tail post false) (overlay (outs.flatMap frame) BW)
          (overlay (frame p) JP) [true] pre.length (outs.flatMap frame).length 0)
        (branchT 3 (branchF 0 xorCaseM (copyCase pre tail post (outs.flatMap frame) BW (overlay (frame p) JP) false true)
            (by simp [entryBit, (hbit JP true).1]))
          (branchM 0 pivotCaseM copyCaseM)
          (by simp [entryBit, readTapeBit_flag])) rfl rfl) selP cap
        (by intro i hi; fin_cases i <;> simp_all [selP]) (by simp; omega)).run
      refine ((hm.enlarge (by simp [rowCost]; omega)).congr ?_ ?_).congr_in ?_ ?_ <;> bank_eq
    | true =>
      have hpc : overlay (frame p) JP = frame p ++ JP.drop (frame p).length := rfl
      let C := xorCase pre tail post (outs.flatMap frame) BW (overlay (frame p) JP) true true p
        (JP.drop (frame p).length) hpc hp.symm
      have hC0 : entryBit C.entryH C.entryA 0 = true := (hbit JP true).1
      let I := branchT 0 C copyCaseM hC0
      have hI3 : entryBit I.entryH I.entryA 3 = true := rfl
      let O := branchT 3 I (branchM 0 pivotCaseM copyCaseM) hI3
      let B := seq (nudgeR (rowSrc pre tail post true) (overlay (outs.flatMap frame) BW)
          (overlay (frame p) JP) [true] pre.length (outs.flatMap frame).length 0) O rfl rfl
      have hBc : B.cost = 2 * tail.length + 11 := by
        show 1 + 1 + (C.cost + 2 + 2) = _
        rw [xorCase_cost]; omega
      have hm := (masked B selP cap (by intro i hi; fin_cases i <;> simp_all [selP]; rfl) (by omega)).run
      have hmx := hm.enlarge (m := rowCost tail.length) (by rw [masked_cost, hBc, rowCost]; omega)
      have eH : (masked B selP cap (by intro i hi; fin_cases i <;> simp_all [selP]; rfl) (by omega)).exitH =
          Fin.addCases (rowHeads (pre.length + (2 * tail.length + 3))
            (rowStep (some p, outs) (true :: tail)).2) (fun _ : Fin 1 => 0) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [masked, Fin.addCases_left]
          show (if selP j then 0 else C.exitH j) = _
          rw [xorCase_exitH]
          fin_cases j <;> simp [selP, rowHeads, rowStep] <;> omega
        · simp [masked]
      have eA : (masked B selP cap (by intro i hi; fin_cases i <;> simp_all [selP]; rfl) (by omega)).exitA =
          Fin.addCases (rowTapes (pre ++ frame (true :: tail) ++ post) (rowStep (some p, outs) (true :: tail)).2 BW
            (rowStep (some p, outs) (true :: tail)).1 JP) (fun _ : Fin 1 => List.replicate cap false) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [masked, Fin.addCases_left]
          show C.exitA j = _
          rw [xorCase_exitA, map_xor _ _ hp.symm]
          fin_cases j <;> simp [rowTapes, rowStep, pivTape_some, frame, List.append_assoc]
        · simp [masked]
      refine (hmx.congr eH eA).congr_in ?_ ?_
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [masked, Fin.addCases_left]
          fin_cases j <;> rfl
        · simp [masked]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [masked, Fin.addCases_left]
          fin_cases j <;> rfl
        · simp [masked]

end NearCubicWires.WireExponent3_5.Gauss
