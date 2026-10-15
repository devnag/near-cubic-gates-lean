import Proof.Wire_3_5.ListMachinePrintBank

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.GF2 (write_mid)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (atomCode monoBits recW dockRun maskRun)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Copying one unary code as pairs -/

namespace CopyCode
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Tape 0 the label word (read), tape 1 the output. State `0` reads a label bit and writes the pair's marker, `1`
writes a one, `2` writes a zero (the code's end), `3` halts. -/
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none (some true) .stay .right else act 2 none (some true) .stay .right)
    else if q.val = 1 then some (act 0 none (some true) .right .right)
    else if q.val = 2 then some (act 3 none (some false) .right .right)
    else none

theorem one_steps (A : List Bool) (h : ℕ) (o B : List Bool) (hr : readTapeBit A h = true) :
    Timed machine 2 (cfg 0 A (overlay o B) h o.length) (cfg 0 A (overlay (o ++ [true, true]) B) (h + 1) (o ++ [true, true]).length) := by
  have s1 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 0 1 A (overlay o B) h o.length none (some true)
    .stay .right (by simp [machine, hr])
  have s2 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 1 0 A (overlay (o ++ [true]) B) h
    (o ++ [true]).length none (some true) .right .right (by simp [machine])
  simp only [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, overlay_write] at s1 s2
  have e : (o ++ [true]).length = o.length + 1 := by simp
  rw [← e] at s1
  have := (Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)
  simpa [List.append_assoc] using this

theorem zero_steps (A : List Bool) (h : ℕ) (o B : List Bool) (hr : readTapeBit A h = false) :
    Timed machine 2 (cfg 0 A (overlay o B) h o.length) (cfg 3 A (overlay (o ++ [true, false]) B) (h + 1) (o ++ [true, false]).length) := by
  have s1 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 0 2 A (overlay o B) h o.length none (some true)
    .stay .right (by simp [machine, hr])
  have s2 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 2 3 A (overlay (o ++ [true]) B) h
    (o ++ [true]).length none (some false) .right .right (by simp [machine])
  simp only [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, overlay_write] at s1 s2
  have e : (o ++ [true]).length = o.length + 1 := by simp
  rw [← e] at s1
  have := (Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)
  simpa [List.append_assoc] using this

theorem timed (tail B : List Bool) : ∀ (k : ℕ) (pre o : List Bool),
    Timed machine (2 * (k + 1))
      (cfg 0 (pre ++ (List.replicate k true ++ [false]) ++ tail) (overlay o B) pre.length o.length)
      (cfg 3 (pre ++ (List.replicate k true ++ [false]) ++ tail)
        (overlay (o ++ Streaming.marks (List.replicate k true ++ [false])) B) (pre.length + (k + 1))
        (o ++ Streaming.marks (List.replicate k true ++ [false])).length) := by
  intro k
  induction k with
  | zero =>
    intro pre o
    have hr : readTapeBit (pre ++ (List.replicate 0 true ++ [false]) ++ tail) pre.length = false := by
      simpa [List.append_assoc] using Streaming.read_append pre tail false
    simpa [Streaming.marks] using zero_steps _ pre.length o B hr
  | succ k ih =>
    intro pre o
    have hr : readTapeBit (pre ++ (List.replicate (k + 1) true ++ [false]) ++ tail) pre.length = true := by
      simpa [List.replicate_succ, List.append_assoc] using
        Streaming.read_append pre (List.replicate k true ++ false :: tail) true
    have t1 := one_steps _ pre.length o B hr
    have e0 : pre ++ (List.replicate (k + 1) true ++ [false]) ++ tail =
        (pre ++ [true]) ++ (List.replicate k true ++ [false]) ++ tail := by
      simp [List.replicate_succ, List.append_assoc]
    have t2 := ih (pre ++ [true]) (o ++ [true, true])
    rw [← e0] at t2
    have e1 : (pre ++ [true]).length = pre.length + 1 := by simp
    have e2 : o ++ [true, true] ++ Streaming.marks (List.replicate k true ++ [false]) =
        o ++ Streaming.marks (List.replicate (k + 1) true ++ [false]) := by
      simp [List.replicate_succ, Streaming.marks, List.append_assoc]
    rw [e1, e2, show pre.length + 1 + (k + 1) = pre.length + (k + 1 + 1) by omega] at t2
    have := t1.trans t2
    rwa [show 2 + 2 * (k + 1) = 2 * (k + 1 + 1) by ring] at this

/-- **Copy one code**: `atomCode k` at the label cursor is written as pairs at the output cursor; the label cursor
passes the code. -/
theorem run (pre tail : List Bool) (k : ℕ) (o B : List Bool) :
    Step machine (2 * (k + 1)) ![pre.length, o.length] ![pre ++ atomCode k ++ tail, overlay o B]
      ![pre.length + (k + 1), (o ++ Streaming.marks (atomCode k)).length]
      ![pre ++ atomCode k ++ tail, overlay (o ++ Streaming.marks (atomCode k)) B] := by
  obtain ⟨r, hr, hf, _⟩ := (timed tail B k pre o).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end CopyCode

/-! ## Passing one unary code -/

namespace SkipCode
open One (cfg)

def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc => if q.val = 0 then some (if sc 0 then ⟨0, ![none], ![.right]⟩ else ⟨1, ![none], ![.right]⟩)
    else none

theorem one_step (A : List Bool) (h : ℕ) (hr : readTapeBit A h = true) :
    step machine (cfg 0 A h) = some (cfg 0 A (h + 1)) := by
  have := One.step_cfg machine 0 0 A h none .right (by simp [machine, hr])
  simpa [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] using this

theorem end_step (A : List Bool) (h : ℕ) (hr : readTapeBit A h = false) :
    step machine (cfg 0 A h) = some (cfg 1 A (h + 1)) := by
  have := One.step_cfg machine 0 1 A h none .right (by simp [machine, hr])
  simpa [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] using this

theorem timed (tail : List Bool) : ∀ (k : ℕ) (pre : List Bool),
    Timed machine (k + 1) (cfg 0 (pre ++ (List.replicate k true ++ [false]) ++ tail) pre.length)
      (cfg 1 (pre ++ (List.replicate k true ++ [false]) ++ tail) (pre.length + (k + 1))) := by
  intro k
  induction k with
  | zero =>
    intro pre
    have hr : readTapeBit (pre ++ (List.replicate 0 true ++ [false]) ++ tail) pre.length = false := by
      simpa [List.append_assoc] using Streaming.read_append pre tail false
    simpa using Timed.single (p := machine) rfl (end_step _ _ hr)
  | succ k ih =>
    intro pre
    have hr : readTapeBit (pre ++ (List.replicate (k + 1) true ++ [false]) ++ tail) pre.length = true := by
      simpa [List.replicate_succ, List.append_assoc] using
        Streaming.read_append pre (List.replicate k true ++ false :: tail) true
    have t1 := Timed.single (p := machine) rfl (one_step _ _ hr)
    have e0 : pre ++ (List.replicate (k + 1) true ++ [false]) ++ tail =
        (pre ++ [true]) ++ (List.replicate k true ++ [false]) ++ tail := by
      simp [List.replicate_succ, List.append_assoc]
    have t2 := ih (pre ++ [true])
    rw [← e0, show (pre ++ [true]).length = pre.length + 1 by simp,
      show pre.length + 1 + (k + 1) = pre.length + (k + 1 + 1) by omega] at t2
    have := t1.trans t2
    rwa [show 1 + (k + 1) = k + 1 + 1 by omega] at this

theorem run (pre tail : List Bool) (k : ℕ) :
    Step machine (k + 1) ![pre.length] ![pre ++ atomCode k ++ tail] ![pre.length + (k + 1)]
      ![pre ++ atomCode k ++ tail] := by
  obtain ⟨r, hr, hf, _⟩ := (timed tail k pre).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end SkipCode

/-! ## The positions of the bitmap against the label word (tapes: 0 the bitmap, 1 the label word, 2 the output) -/

def slX3 : Fin 1 → Fin 3 := ![0]
theorem slX3_inj : Function.Injective slX3 := by decide

theorem dockH_X3 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slX3 H v = ![v 0, H 1, H 2] := by
  funext i; fin_cases i
  · exact dockH_slot slX3 slX3_inj H v 0
  · exact dockH_other slX3 H v 1 (by decide)
  · exact dockH_other slX3 H v 2 (by decide)

theorem install_X3 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slX3 A v = ![v 0, A 1, A 2] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slX3 slX3_inj A v 0
  · exact RecoveryRootRound.install_other slX3 A v 1 (by decide)
  · exact RecoveryRootRound.install_other slX3 A v 2 (by decide)

/-- The label of coordinate `p`. -/
def labOf (labs : List ℕ) (p : ℕ) : ℕ := labs.getD p 0

/-- What position `p` contributes: the pairs of its label's code at a one. -/
def pieceL (xs : List Bool) (labs : List ℕ) (p : ℕ) : List Bool :=
  if xs.getD p false then Streaming.marks (atomCode (labOf labs p)) else []

def accL (xs : List Bool) (labs : List ℕ) (i : ℕ) : List Bool := (List.range i).flatMap (pieceL xs labs)

theorem accL_succ (xs : List Bool) (labs : List ℕ) (i : ℕ) : accL xs labs (i + 1) = accL xs labs i ++ pieceL xs labs i := by
  simp [accL, List.range_succ, List.flatMap_append]

theorem flatMap_pieceL (xs : List Bool) (labs : List ℕ) (l : List ℕ) :
    l.flatMap (pieceL xs labs) =
      (l.filter fun i => xs.getD i false).flatMap fun p => Streaming.marks (atomCode (labOf labs p)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : xs.getD p false = true
    · rw [List.filter_cons_of_pos (p := fun i => xs.getD i false) h, List.flatMap_cons, List.flatMap_cons, ih]
      simp only [pieceL, h, if_true]
    · rw [List.filter_cons_of_neg (p := fun i => xs.getD i false) h, List.flatMap_cons, ih]
      simp only [pieceL, h, if_false, Bool.false_eq_true, List.nil_append]

theorem accL_full (xs : List Bool) (labs : List ℕ) :
    accL xs labs xs.length = Streaming.marks (monoBits ((Interp.supp xs).map (labOf labs))) := by
  unfold accL monoBits Interp.supp
  rw [flatMap_pieceL, List.flatMap_map, marks_flatMap]

/-- The label word before position `i`. -/
def labPre (labs : List ℕ) (i : ℕ) : List Bool := (labs.take i).flatMap atomCode

theorem lab_split (labs : List ℕ) (tail : List Bool) (i : ℕ) (hi : i < labs.length) :
    labs.flatMap atomCode ++ tail = labPre labs i ++ atomCode labs[i] ++ ((labs.drop (i + 1)).flatMap atomCode ++ tail) := by
  unfold labPre
  conv_lhs => rw [← List.take_append_drop i labs]
  rw [List.flatMap_append, List.drop_eq_getElem_cons hi, List.flatMap_cons]
  simp [List.append_assoc]

theorem labPre_succ (labs : List ℕ) (i : ℕ) (hi : i < labs.length) :
    labPre labs (i + 1) = labPre labs i ++ atomCode labs[i] := by
  unfold labPre
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.flatMap_append]
  simp

/-- The branch on the bit: copy the label's code at a one, pass it at a zero. -/
noncomputable def brL := NearCubicWires.WireExponent3_5.Block.branchM 0
  (RecoveryFocus.machine slUO CopyCode.machine) (RecoveryFocus.machine slU3 SkipCode.machine)

/-- One position of the labelled record. -/
noncomputable def bodyL := Composition.machine
  (Composition.machine (RecoveryFocus.machine slX3 Rec.Skip.machine) brL) (RecoveryFocus.machine slX3 Rec.Skip.machine)

def bodyLCost (k : ℕ) : ℕ := 1 + 1 + (2 * (k + 1) + 2) + 1 + 1

theorem bodyL_step (xs : List Bool) (labs : List ℕ) (tail o B : List Bool) (i : ℕ) (hi : i < xs.length)
    (hl : i < labs.length) :
    Step bodyL (bodyLCost labs[i])
      ![2 * i, (labPre labs i).length, o.length] ![frame xs, labs.flatMap atomCode ++ tail, overlay o B]
      ![2 * (i + 1), (labPre labs (i + 1)).length, (o ++ pieceL xs labs i).length]
      ![frame xs, labs.flatMap atomCode ++ tail, overlay (o ++ pieceL xs labs i) B] := by
  have hr := frame_read xs i hi
  set Lw := labs.flatMap atomCode ++ tail with hLw
  have hsplit := lab_split labs tail i hl
  set rest := (labs.drop (i + 1)).flatMap atomCode ++ tail with hrest
  have h1 := dockRun (Rec.Skip.run (frame xs) (2 * i)) slX3 slX3_inj ![2 * i, (labPre labs i).length, o.length]
    ![frame xs, Lw, overlay o B] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_X3, install_X3] at h1
  have hp : pieceL xs labs i = if xs[i] then Streaming.marks (atomCode labs[i]) else [] := by
    unfold pieceL labOf; rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hl]
  -- the branch
  have hb : Step brL (2 * (labs[i] + 1) + 2)
      ![2 * i + 1, (labPre labs i).length, o.length] ![frame xs, Lw, overlay o B]
      ![2 * i + 1, (labPre labs (i + 1)).length, (o ++ pieceL xs labs i).length]
      ![frame xs, Lw, overlay (o ++ pieceL xs labs i) B] := by
    cases hx : xs[i]
    · have hA1 : ∀ j, (![frame xs, Lw, overlay o B] : Fin 3 → List Bool) (slU3 j) =
          ![labPre labs i ++ atomCode labs[i] ++ rest] j := by
        intro j; fin_cases j; exact hsplit
      have hs := dockRun (SkipCode.run (labPre labs i) rest labs[i]) slU3 slU3_inj
        ![2 * i + 1, (labPre labs i).length, o.length] ![frame xs, Lw, overlay o B]
        (by intro j; fin_cases j; rfl) hA1
      rw [dockH_U3, install_U3] at hs
      have h := NearCubicWires.WireExponent3_5.Block.branch_false (0 : Fin 3)
        (RecoveryFocus.machine slUO CopyCode.machine) hs (by simpa [hx] using hr.2)
      refine (h.congr ?_ ?_).enlarge (by omega)
      · funext j; fin_cases j
        · rfl
        · show (labPre labs i).length + (labs[i] + 1) = (labPre labs (i + 1)).length
          rw [labPre_succ labs i hl]; simp [atomCode]
        · show o.length = (o ++ pieceL xs labs i).length
          rw [hp, hx]; simp
      · funext j; fin_cases j
        · rfl
        · exact hsplit.symm
        · show overlay o B = overlay (o ++ pieceL xs labs i) B
          rw [hp, hx]; simp
    · have hA2 : ∀ j, (![frame xs, Lw, overlay o B] : Fin 3 → List Bool) (slUO j) =
          ![labPre labs i ++ atomCode labs[i] ++ rest, overlay o B] j := by
        intro j; fin_cases j
        · exact hsplit
        · rfl
      have hc := dockRun (CopyCode.run (labPre labs i) rest labs[i] o B) slUO slUO_inj
        ![2 * i + 1, (labPre labs i).length, o.length] ![frame xs, Lw, overlay o B]
        (by intro j; fin_cases j <;> rfl) hA2
      rw [dockH_UO, install_UO] at hc
      have h := NearCubicWires.WireExponent3_5.Block.branch_true (0 : Fin 3)
        (RecoveryFocus.machine slU3 SkipCode.machine) hc (by simpa [hx] using hr.2)
      refine h.congr ?_ ?_
      · funext j; fin_cases j
        · rfl
        · show (labPre labs i).length + (labs[i] + 1) = (labPre labs (i + 1)).length
          rw [labPre_succ labs i hl]; simp [atomCode]
        · show (o ++ Streaming.marks (atomCode labs[i])).length = (o ++ pieceL xs labs i).length
          rw [hp, hx]; simp
      · funext j; fin_cases j
        · rfl
        · show labPre labs i ++ atomCode labs[i] ++ rest = Lw
          exact hsplit.symm
        · show overlay (o ++ Streaming.marks (atomCode labs[i])) B = overlay (o ++ pieceL xs labs i) B
          rw [hp, hx]; simp
  have h3 := dockRun (Rec.Skip.run (frame xs) (2 * i + 1)) slX3 slX3_inj
    ![2 * i + 1, (labPre labs (i + 1)).length, (o ++ pieceL xs labs i).length]
    ![frame xs, Lw, overlay (o ++ pieceL xs labs i) B] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_X3, install_X3] at h3
  have s1 := Step.seq h1 (hb.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have s2 := Step.seq s1 (h3.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  refine (s2.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext j; fin_cases j
    · show 2 * i + 1 + 1 = 2 * (i + 1); ring
    · rfl
    · rfl
  · funext j; fin_cases j <;> rfl
  · simp [bodyLCost]

/-! ## The labelled record -/

def loopLCost (xs : List Bool) (labs : List ℕ) : ℕ :=
  ((List.range xs.length).map fun i => bodyLCost (labs.getD i 0) + 2).sum + 1

theorem loopL_run (xs : List Bool) (labs : List ℕ) (tail o B : List Bool) (hl : xs.length ≤ labs.length) :
    Step (StreamController.machine bodyL 0) (loopLCost xs labs)
      ![0, 0, o.length] ![frame xs, labs.flatMap atomCode ++ tail, overlay o B]
      ![2 * xs.length, (labPre labs xs.length).length, (o ++ accL xs labs xs.length).length]
      ![frame xs, labs.flatMap atomCode ++ tail, overlay (o ++ accL xs labs xs.length) B] := by
  have hW := NearCubicWires.WireExponent3_5.Block.WhileBody.run ({
    body := bodyL
    tape := 0
    bound := xs.length
    H := fun i => ![2 * i, (labPre labs i).length, (o ++ accL xs labs i).length]
    A := fun i => ![frame xs, labs.flatMap atomCode ++ tail, overlay (o ++ accL xs labs i) B]
    cost := fun i => bodyLCost (labs.getD i 0)
    step := by
      intro i hi
      have hli : i < labs.length := by omega
      have h := bodyL_step xs labs tail (o ++ accL xs labs i) B i hi hli
      rw [List.getD_eq_getElem _ _ hli]
      refine h.congr ?_ ?_
      · funext j; fin_cases j
        · rfl
        · rfl
        · show (o ++ accL xs labs i ++ pieceL xs labs i).length = (o ++ accL xs labs (i + 1)).length
          rw [accL_succ, List.append_assoc]
      · funext j; fin_cases j
        · rfl
        · rfl
        · show overlay (o ++ accL xs labs i ++ pieceL xs labs i) B = overlay (o ++ accL xs labs (i + 1)) B
          rw [accL_succ, List.append_assoc]
    cont := fun i hi => (frame_read xs i hi).1
    halt := frame_read_end xs } : NearCubicWires.WireExponent3_5.Block.WhileBody 3 _)
  refine (hW.congr_in ?_ ?_).congr ?_ ?_ |>.enlarge (le_of_eq ?_)
  · funext j; fin_cases j <;> simp [labPre, accL]
  · funext j; fin_cases j <;> simp [accL]
  · rfl
  · rfl
  · simp [NearCubicWires.WireExponent3_5.Block.WhileBody.rest, loopLCost]

/-- The labelled record before the rewind: the marker, the positions, the monomial's terminator. -/
noncomputable def recInnerL := Composition.machine
  (Composition.machine (RecoveryFocus.machine slO3 (Put.machine true)) (StreamController.machine bodyL 0))
  (RecoveryFocus.machine slO3 (Put.machine false))

def selXL : Fin 3 → Bool := ![true, true, false]
def sl4of5 : Fin 4 → Fin 5 := ![0, 1, 2, 3]
theorem sl4of5_inj : Function.Injective sl4of5 := by decide

/-- **The labelled record printer** (tapes: 0 the bitmap, 1 the label word, 2 the output, 3 the log, 4 unused). -/
noncomputable def recLM := RecoveryFocus.machine sl4of5 (MaskedReset.machine recInnerL selXL)

def recInnerLCost (xs : List Bool) (labs : List ℕ) : ℕ := 1 + 1 + loopLCost xs labs + 1 + 1

/-- **The labelled record printer**: `recW ((supp xs).map (labOf labs))` appended at the output cursor, every other
tape unchanged and every other cursor at `0`. -/
theorem recL_run (xs : List Bool) (labs : List ℕ) (tail o B : List Bool) (cap1 cap2 : ℕ)
    (hl : xs.length ≤ labs.length) (hcap : recInnerLCost xs labs ≤ cap1) :
    Step recLM (2 * recInnerLCost xs labs + 2)
      ![0, 0, o.length, 0, 0]
      ![frame xs, labs.flatMap atomCode ++ tail, overlay o B, List.replicate cap1 false, List.replicate cap2 false]
      ![0, 0, (o ++ recW ((Interp.supp xs).map (labOf labs))).length, 0, 0]
      ![frame xs, labs.flatMap atomCode ++ tail, overlay (o ++ recW ((Interp.supp xs).map (labOf labs))) B,
        List.replicate cap1 false, List.replicate cap2 false] := by
  set Lw := labs.flatMap atomCode ++ tail with hLw
  have s1 := dockRun (Put.run true o B) slO3 slO3_inj ![0, 0, o.length] ![frame xs, Lw, overlay o B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O3, install_O3] at s1
  have s2 := loopL_run xs labs tail (o ++ [true]) B hl
  have s3 := dockRun (Put.run false (o ++ [true] ++ accL xs labs xs.length) B) slO3 slO3_inj
    ![2 * xs.length, (labPre labs xs.length).length, (o ++ [true] ++ accL xs labs xs.length).length]
    ![frame xs, Lw, overlay (o ++ [true] ++ accL xs labs xs.length) B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O3, install_O3] at s3
  have t := Step.seq (Step.seq s1 (s2.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)))
    (s3.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have hm := maskRun t selXL (by intro j hj; fin_cases j <;> simp_all [selXL]) (by simpa [recInnerLCost] using hcap)
  have hd := dockRun hm sl4of5 sl4of5_inj ![0, 0, o.length, 0, 0]
    ![frame xs, Lw, overlay o B, List.replicate cap1 false, List.replicate cap2 false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have eo : o ++ [true] ++ accL xs labs xs.length ++ [false] = o ++ recW ((Interp.supp xs).map (labOf labs)) := by
    rw [accL_full, recW_eq]; simp
  refine (hd.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext j; fin_cases j
    · exact dockH_slot sl4of5 sl4of5_inj _ _ 0
    · exact dockH_slot sl4of5 sl4of5_inj _ _ 1
    · show dockH sl4of5 _ _ (sl4of5 2) = _
      rw [dockH_slot sl4of5 sl4of5_inj]
      show (o ++ [true] ++ accL xs labs xs.length ++ [false]).length = _
      rw [eo]; rfl
    · exact dockH_slot sl4of5 sl4of5_inj _ _ 3
    · exact dockH_other sl4of5 _ _ 4 (by decide)
  · funext j; fin_cases j
    · exact RecoveryRootRound.install_slot sl4of5 sl4of5_inj _ _ 0
    · exact RecoveryRootRound.install_slot sl4of5 sl4of5_inj _ _ 1
    · show RecoveryRootRound.install sl4of5 _ _ (sl4of5 2) = _
      rw [RecoveryRootRound.install_slot sl4of5 sl4of5_inj]
      show overlay (o ++ [true] ++ accL xs labs xs.length ++ [false]) B = _
      rw [eo]; rfl
    · exact RecoveryRootRound.install_slot sl4of5 sl4of5_inj _ _ 3
    · exact RecoveryRootRound.install_other sl4of5 _ _ 4 (by decide)
  · simp [recInnerLCost]

end NearCubicWires.WireExponent3_5.ListMachine.Print
