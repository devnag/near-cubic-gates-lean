import Proof.Wire_3_5.ListMachinePrintCore

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Interp (supp)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (atomCode monoBits recW dockRun maskRun)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Reading a framed word -/

theorem frame_read (xs : List Bool) : ∀ i (hi : i < xs.length),
    readTapeBit (frame xs) (2 * i) = true ∧ readTapeBit (frame xs) (2 * i + 1) = xs[i] := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => simp [readTapeBit, frame]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [readTapeBit, frame, Nat.mul_succ, List.getD_cons_succ] using this

theorem frame_read_end (xs : List Bool) : readTapeBit (frame xs) (2 * xs.length) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [readTapeBit, frame, Nat.mul_succ, List.getD_cons_succ] using ih

/-! ## The output of one position -/

/-- What position `p` of the bitmap `xs` contributes to the monomial's framed word. -/
def piece (xs : List Bool) (p : ℕ) : List Bool := if xs.getD p false then Streaming.marks (atomCode p) else []

/-- The contribution of the first `i` positions. -/
def accW (xs : List Bool) (i : ℕ) : List Bool := (List.range i).flatMap (piece xs)

theorem accW_succ (xs : List Bool) (i : ℕ) : accW xs (i + 1) = accW xs i ++ piece xs i := by
  simp [accW, List.range_succ, List.flatMap_append]

theorem marks_flatMap (S : List ℕ) (f : ℕ → List Bool) :
    Streaming.marks (S.flatMap f) = S.flatMap fun p => Streaming.marks (f p) := by
  induction S with
  | nil => rfl
  | cons a S ih => simp [List.flatMap_cons, Streaming.marks_append, ih]

theorem flatMap_piece (xs : List Bool) (l : List ℕ) :
    l.flatMap (piece xs) = (l.filter fun i => xs.getD i false).flatMap fun p => Streaming.marks (atomCode p) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : xs.getD p false = true
    · rw [List.filter_cons_of_pos (p := fun i => xs.getD i false) h, List.flatMap_cons, List.flatMap_cons, ih]
      simp only [piece, h, if_true]
    · rw [List.filter_cons_of_neg (p := fun i => xs.getD i false) h, List.flatMap_cons, ih]
      simp only [piece, h, if_false, Bool.false_eq_true, List.nil_append]

/-- **The positions of `xs` print the pairs of `monoBits (supp xs)`.** -/
theorem accW_full (xs : List Bool) : accW xs xs.length = Streaming.marks (monoBits (supp xs)) := by
  unfold accW monoBits supp
  rw [marks_flatMap, flatMap_piece]

theorem marks_atomCode (i : ℕ) :
    Streaming.marks (atomCode i) = Streaming.marks (List.replicate i true) ++ [true, false] := by
  simp [atomCode, Streaming.marks]

/-! ## One position: the arms of the branch (tapes: 0 the bitmap, 1 the position word, 2 the output) -/

def slUO : Fin 2 → Fin 3 := ![1, 2]
def slO3 : Fin 1 → Fin 3 := ![2]
def slU3 : Fin 1 → Fin 3 := ![1]

theorem slUO_inj : Function.Injective slUO := by decide
theorem slO3_inj : Function.Injective slO3 := by decide
theorem slU3_inj : Function.Injective slU3 := by decide

theorem dockH_UO (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) : dockH slUO H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  · exact dockH_other slUO H v 0 (by decide)
  · exact dockH_slot slUO slUO_inj H v 0
  · exact dockH_slot slUO slUO_inj H v 1

theorem install_UO (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slUO A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slUO A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slUO slUO_inj A v 0
  · exact RecoveryRootRound.install_slot slUO slUO_inj A v 1

theorem dockH_O3 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slO3 H v = ![H 0, H 1, v 0] := by
  funext i; fin_cases i
  · exact dockH_other slO3 H v 0 (by decide)
  · exact dockH_other slO3 H v 1 (by decide)
  · exact dockH_slot slO3 slO3_inj H v 0

theorem install_O3 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slO3 A v = ![A 0, A 1, v 0] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slO3 A v 0 (by decide)
  · exact RecoveryRootRound.install_other slO3 A v 1 (by decide)
  · exact RecoveryRootRound.install_slot slO3 slO3_inj A v 0

theorem dockH_U3 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slU3 H v = ![H 0, v 0, H 2] := by
  funext i; fin_cases i
  · exact dockH_other slU3 H v 0 (by decide)
  · exact dockH_slot slU3 slU3_inj H v 0
  · exact dockH_other slU3 H v 2 (by decide)

theorem install_U3 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slU3 A v = ![A 0, v 0, A 2] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slU3 A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slU3 slU3_inj A v 0
  · exact RecoveryRootRound.install_other slU3 A v 2 (by decide)

/-- The arm at a one: copy the position's pairs, close the coordinate, extend the position word. -/
noncomputable def armT := Composition.machine
  (Composition.machine (Composition.machine (RecoveryFocus.machine slUO Rec.CopyOpen.machine)
    (RecoveryFocus.machine slO3 (Put.machine true))) (RecoveryFocus.machine slO3 (Put.machine false)))
  (RecoveryFocus.machine slU3 UExtend.machine)

/-- The arm at a zero: extend the position word. -/
noncomputable def armF := Composition.machine (RecoveryFocus.machine slU3 Seek.machine)
  (RecoveryFocus.machine slU3 UExtend.machine)

/-- The cost of the arm at a one (it bounds the other arm). -/
def armCost (i : ℕ) : ℕ := (2 * i + 1) + 1 + 1 + 1 + 1 + 1 + 3

theorem armT_step (Xw : List Bool) (h0 i : ℕ) (U0 o B : List Bool) :
    Step armT (armCost i)
      ![h0, 0, o.length] ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
      ![h0, 2 * i + 2, (o ++ Streaming.marks (atomCode i)).length]
      ![Xw, overlay (frame (List.replicate (i + 1) true)) U0, overlay (o ++ Streaming.marks (atomCode i)) B] := by
  have hc := Rec.CopyOpen.run [] (List.replicate i true) (U0.drop (frame (List.replicate i true)).length) o B
  have h1 := dockRun hc slUO slUO_inj ![h0, 0, o.length] ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_UO, install_UO] at h1
  set o1 := o ++ Streaming.marks (List.replicate i true) with ho1
  have hp1 := dockRun (Put.run true o1 B) slO3 slO3_inj ![h0, 2 * i, o1.length]
    ![Xw, overlay (frame (List.replicate i true)) U0, overlay o1 B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O3, install_O3] at hp1
  have hp2 := dockRun (Put.run false (o1 ++ [true]) B) slO3 slO3_inj ![h0, 2 * i, (o1 ++ [true]).length]
    ![Xw, overlay (frame (List.replicate i true)) U0, overlay (o1 ++ [true]) B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O3, install_O3] at hp2
  have hu := dockRun (UExtend.run i U0) slU3 slU3_inj ![h0, 2 * i, (o1 ++ [true] ++ [false]).length]
    ![Xw, overlay (frame (List.replicate i true)) U0, overlay (o1 ++ [true] ++ [false]) B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_U3, install_U3] at hu
  have s1 := Step.seq h1 (hp1.congr_in (by funext j; fin_cases j <;> simp [ho1])
    (by funext j; fin_cases j <;> rfl))
  have s2 := Step.seq s1 (hp2.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have s3 := Step.seq s2 (hu.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have eo : o1 ++ [true] ++ [false] = o ++ Streaming.marks (atomCode i) := by
    rw [ho1, marks_atomCode]; simp
  refine (s3.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext j; fin_cases j
    · rfl
    · rfl
    · show (o1 ++ [true] ++ [false]).length = (o ++ Streaming.marks (atomCode i)).length
      rw [eo]
  · funext j; fin_cases j
    · rfl
    · rfl
    · show overlay (o1 ++ [true] ++ [false]) B = overlay (o ++ Streaming.marks (atomCode i)) B
      rw [eo]
  · simp [armCost]

theorem armF_step (Xw : List Bool) (h0 i : ℕ) (U0 o B : List Bool) :
    Step armF (2 * i + 1 + 1 + 3)
      ![h0, 0, o.length] ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
      ![h0, 2 * i + 2, o.length]
      ![Xw, overlay (frame (List.replicate (i + 1) true)) U0, overlay o B] := by
  have hs := Seek.run [] (List.replicate i true) (U0.drop (frame (List.replicate i true)).length)
  have h1 := dockRun hs slU3 slU3_inj ![h0, 0, o.length] ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_U3, install_U3] at h1
  have hu := dockRun (UExtend.run i U0) slU3 slU3_inj ![h0, 2 * i, o.length]
    ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_U3, install_U3] at hu
  have s := Step.seq h1 (hu.congr_in (by funext j; fin_cases j <;> simp) (by funext j; fin_cases j <;> rfl))
  refine (s.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).enlarge (le_of_eq ?_)
  simp

/-! ## The branch on the bit, with the position word rewound -/

/-- The branch on the bitmap's bit (tape 0). -/
noncomputable def br := NearCubicWires.WireExponent3_5.Block.branchM 0 armT armF

theorem br_step (Xw : List Bool) (h0 i : ℕ) (U0 o B : List Bool) (b : Bool) (hb : readTapeBit Xw h0 = b) :
    Step br (armCost i + 2)
      ![h0, 0, o.length] ![Xw, overlay (frame (List.replicate i true)) U0, overlay o B]
      ![h0, 2 * i + 2, (o ++ if b then Streaming.marks (atomCode i) else []).length]
      ![Xw, overlay (frame (List.replicate (i + 1) true)) U0,
        overlay (o ++ if b then Streaming.marks (atomCode i) else []) B] := by
  cases b
  · have h := NearCubicWires.WireExponent3_5.Block.branch_false (0 : Fin 3) armT (armF_step Xw h0 i U0 o B)
      (by simpa using hb)
    refine (h.congr ?_ ?_).enlarge (by simp [armCost])
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp
  · have h := NearCubicWires.WireExponent3_5.Block.branch_true (0 : Fin 3) armF (armT_step Xw h0 i U0 o B)
      (by simpa using hb)
    exact h.congr (by funext j; fin_cases j <;> simp) (by funext j; fin_cases j <;> simp)

def selU3 : Fin 3 → Bool := ![false, true, false]

/-! ## The positions of the bitmap (tapes: 0 the bitmap, 1 the position word, 2 the output, 3 the word's log) -/

def sl0 : Fin 1 → Fin 4 := ![0]
theorem sl0_inj : Function.Injective sl0 := by decide

theorem dockH_0 (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) : dockH sl0 H v = ![v 0, H 1, H 2, H 3] := by
  funext i; fin_cases i
  · exact dockH_slot sl0 sl0_inj H v 0
  · exact dockH_other sl0 H v 1 (by decide)
  · exact dockH_other sl0 H v 2 (by decide)
  · exact dockH_other sl0 H v 3 (by decide)

theorem install_0 (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install sl0 A v = ![v 0, A 1, A 2, A 3] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot sl0 sl0_inj A v 0
  · exact RecoveryRootRound.install_other sl0 A v 1 (by decide)
  · exact RecoveryRootRound.install_other sl0 A v 2 (by decide)
  · exact RecoveryRootRound.install_other sl0 A v 3 (by decide)

/-- One position: pass the marker, the masked branch on the bit, pass the bit. -/
noncomputable def body := Composition.machine
  (Composition.machine (RecoveryFocus.machine sl0 Rec.Skip.machine) (MaskedReset.machine br selU3))
  (RecoveryFocus.machine sl0 Rec.Skip.machine)

def bodyCostR (i : ℕ) : ℕ := 1 + 1 + (2 * (armCost i + 2) + 2) + 1 + 1

theorem getD_eq_getElem' (xs : List Bool) (i : ℕ) (hi : i < xs.length) : xs.getD i false = xs[i] :=
  List.getD_eq_getElem _ _ hi

theorem body_step (xs : List Bool) (i : ℕ) (hi : i < xs.length) (U0 o B : List Bool) (capU : ℕ)
    (hcap : armCost i + 2 ≤ capU) :
    Step body (bodyCostR i)
      ![2 * i, 0, o.length, 0]
      ![frame xs, overlay (frame (List.replicate i true)) U0, overlay o B, List.replicate capU false]
      ![2 * (i + 1), 0, (o ++ piece xs i).length, 0]
      ![frame xs, overlay (frame (List.replicate (i + 1) true)) U0, overlay (o ++ piece xs i) B,
        List.replicate capU false] := by
  have hr := frame_read xs i hi
  have h1 := dockRun (Rec.Skip.run (frame xs) (2 * i)) sl0 sl0_inj ![2 * i, 0, o.length, 0]
    ![frame xs, overlay (frame (List.replicate i true)) U0, overlay o B, List.replicate capU false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_0, install_0] at h1
  have hb := br_step (frame xs) (2 * i + 1) i U0 o B xs[i] hr.2
  have hm := maskRun hb selU3 (by intro j hj; fin_cases j <;> simp_all [selU3]) hcap
  have h3 := dockRun (Rec.Skip.run (frame xs) (2 * i + 1)) sl0 sl0_inj
    ![2 * i + 1, 0, (o ++ if xs[i] then Streaming.marks (atomCode i) else []).length, 0]
    ![frame xs, overlay (frame (List.replicate (i + 1) true)) U0,
      overlay (o ++ if xs[i] then Streaming.marks (atomCode i) else []) B, List.replicate capU false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_0, install_0] at h3
  have s1 := Step.seq h1 (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have s2 := Step.seq s1 (h3.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have hp : piece xs i = if xs[i] then Streaming.marks (atomCode i) else [] := by
    unfold piece; rw [getD_eq_getElem' xs i hi]
  refine (s2.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext j; fin_cases j
    · show 2 * i + 1 + 1 = 2 * (i + 1); ring
    · rfl
    · show (o ++ if xs[i] then Streaming.marks (atomCode i) else []).length = (o ++ piece xs i).length
      rw [hp]
    · rfl
  · funext j; fin_cases j
    · rfl
    · rfl
    · show overlay (o ++ if xs[i] then Streaming.marks (atomCode i) else []) B = overlay (o ++ piece xs i) B
      rw [hp]
    · rfl
  · simp [bodyCostR]

/-- The branch's state count. -/
abbrev brS : ℕ := Fintype.card (NearCubicWires.RepairOrdinary.RecoveryCalls.Control
  (NearCubicWires.WireExponent3_5.Block.sizesM (3 + 2 + 2 + 4) (3 + 4)))

/-- The loop over the positions of the bitmap. -/
noncomputable def loop (xs U0 o0 B : List Bool) (capU : ℕ) (hcap : armCost xs.length + 2 ≤ capU) :
    NearCubicWires.WireExponent3_5.Block.WhileBody 4 (2 + (brS + 2) + 2) where
  body := body
  tape := 0
  bound := xs.length
  H := fun i => ![2 * i, 0, (o0 ++ accW xs i).length, 0]
  A := fun i => ![frame xs, overlay (frame (List.replicate i true)) U0, overlay (o0 ++ accW xs i) B,
    List.replicate capU false]
  cost := bodyCostR
  step := by
    intro i hi
    have h := body_step xs i hi U0 (o0 ++ accW xs i) B capU (le_trans (by simp [armCost]; omega) hcap)
    refine h.congr ?_ ?_
    · funext j; fin_cases j
      · rfl
      · rfl
      · show (o0 ++ accW xs i ++ piece xs i).length = (o0 ++ accW xs (i + 1)).length
        rw [accW_succ, List.append_assoc]
      · rfl
    · funext j; fin_cases j
      · rfl
      · rfl
      · show overlay (o0 ++ accW xs i ++ piece xs i) B = overlay (o0 ++ accW xs (i + 1)) B
        rw [accW_succ, List.append_assoc]
      · rfl
  cont := fun i hi => (frame_read xs i hi).1
  halt := frame_read_end xs

/-- The cost of the loop over the positions. -/
def loopCostR (xs : List Bool) : ℕ := ((List.range xs.length).map fun i => bodyCostR i + 2).sum + 1

theorem loop_run (xs U0 o0 B : List Bool) (capU : ℕ) (hcap : armCost xs.length + 2 ≤ capU) :
    Step (StreamController.machine body 0) (loopCostR xs)
      ![0, 0, o0.length, 0] ![frame xs, overlay (frame []) U0, overlay o0 B, List.replicate capU false]
      ![2 * xs.length, 0, (o0 ++ accW xs xs.length).length, 0]
      ![frame xs, overlay (frame (List.replicate xs.length true)) U0, overlay (o0 ++ accW xs xs.length) B,
        List.replicate capU false] := by
  have h := (loop xs U0 o0 B capU hcap).run
  have hc : (loop xs U0 o0 B capU hcap).rest 0 = loopCostR xs := by
    simp [NearCubicWires.WireExponent3_5.Block.WhileBody.rest, loop, loopCostR]
  rw [hc] at h
  simp only [loop, Nat.mul_zero, accW, List.range_zero, List.flatMap_nil, List.append_nil, List.replicate_zero] at h
  exact h

/-! ## The record -/

def slUL : Fin 2 → Fin 4 := ![1, 3]
def slO4 : Fin 1 → Fin 4 := ![2]
theorem slUL_inj : Function.Injective slUL := by decide
theorem slO4_inj : Function.Injective slO4 := by decide

theorem dockH_UL (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) : dockH slUL H v = ![H 0, v 0, H 2, v 1] := by
  funext i; fin_cases i
  · exact dockH_other slUL H v 0 (by decide)
  · exact dockH_slot slUL slUL_inj H v 0
  · exact dockH_other slUL H v 2 (by decide)
  · exact dockH_slot slUL slUL_inj H v 1

theorem install_UL (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slUL A v = ![A 0, v 0, A 2, v 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slUL A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slUL slUL_inj A v 0
  · exact RecoveryRootRound.install_other slUL A v 2 (by decide)
  · exact RecoveryRootRound.install_slot slUL slUL_inj A v 1

theorem dockH_O4 (H : Fin 4 → ℕ) (v : Fin 1 → ℕ) : dockH slO4 H v = ![H 0, H 1, v 0, H 3] := by
  funext i; fin_cases i
  · exact dockH_other slO4 H v 0 (by decide)
  · exact dockH_other slO4 H v 1 (by decide)
  · exact dockH_slot slO4 slO4_inj H v 0
  · exact dockH_other slO4 H v 3 (by decide)

theorem install_O4 (A : Fin 4 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slO4 A v = ![A 0, A 1, v 0, A 3] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slO4 A v 0 (by decide)
  · exact RecoveryRootRound.install_other slO4 A v 1 (by decide)
  · exact RecoveryRootRound.install_slot slO4 slO4_inj A v 0
  · exact RecoveryRootRound.install_other slO4 A v 3 (by decide)

def selOne : Fin 1 → Bool := ![true]
def selX4 : Fin 4 → Bool := ![true, false, false, false]

/-- The record printer before the bitmap's rewind: reset the position word, the marker, the positions, the
monomial's terminator. -/
noncomputable def recInner := Composition.machine
  (Composition.machine (Composition.machine
    (RecoveryFocus.machine slUL (MaskedReset.machine (Put.machine false) selOne))
    (RecoveryFocus.machine slO4 (Put.machine true)))
    (StreamController.machine body 0))
  (RecoveryFocus.machine slO4 (Put.machine false))

/-- **The record printer** (tapes: 0 the bitmap, 1 the position word, 2 the output, 3 and 4 the logs). -/
noncomputable def recM := MaskedReset.machine recInner selX4

def recInnerCost (xs : List Bool) : ℕ := 4 + 1 + 1 + 1 + loopCostR xs + 1 + 1

theorem frame_eq_marks (x : List Bool) : frame x = Streaming.marks x ++ [false] := by
  have := Streaming.frame_append x []
  simpa [frame] using this

theorem recW_eq (S : List ℕ) : recW S = true :: (Streaming.marks (monoBits S) ++ [false]) := by
  rw [recW, frame_eq_marks]

/-- **The record printer**: `recW (supp xs)` appended at the output cursor; the bitmap, the position word (whose
backing carries `frame (1^{|xs|})`) and the logs are unchanged, every other head back at `0`. -/
theorem rec_run (xs Ub o B : List Bool) (capU capX : ℕ)
    (hUb : overlay (frame (List.replicate xs.length true)) Ub = Ub)
    (hcapU : armCost xs.length + 2 ≤ capU) (hcapX : recInnerCost xs ≤ capX) :
    Step recM (2 * recInnerCost xs + 2)
      ![0, 0, o.length, 0, 0]
      ![frame xs, Ub, overlay o B, List.replicate capU false, List.replicate capX false]
      ![0, 0, (o ++ recW (supp xs)).length, 0, 0]
      ![frame xs, Ub, overlay (o ++ recW (supp xs)) B, List.replicate capU false, List.replicate capX false] := by
  have hcap1 : 1 ≤ capU := by simp [armCost] at hcapU; omega
  -- reset the position word's first cell
  have hp := maskRun (Put.run false [] Ub) selOne (by intro j hj; fin_cases j; rfl) hcap1
  have s1 := dockRun hp slUL slUL_inj ![0, 0, o.length, 0]
    ![frame xs, Ub, overlay o B, List.replicate capU false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_UL, install_UL] at s1
  -- the record marker
  have s2 := dockRun (Put.run true o B) slO4 slO4_inj ![0, 0, o.length, 0]
    ![frame xs, overlay [false] Ub, overlay o B, List.replicate capU false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O4, install_O4] at s2
  -- the positions
  have s3 := loop_run xs Ub (o ++ [true]) B capU hcapU
  -- the monomial's terminator
  have s4 := dockRun (Put.run false (o ++ [true] ++ accW xs xs.length) B) slO4 slO4_inj
    ![2 * xs.length, 0, (o ++ [true] ++ accW xs xs.length).length, 0]
    ![frame xs, overlay (frame (List.replicate xs.length true)) Ub,
      overlay (o ++ [true] ++ accW xs xs.length) B, List.replicate capU false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_O4, install_O4] at s4
  have t12 := Step.seq s1 (s2.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have t123 := Step.seq t12 (s3.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have t := Step.seq t123 (s4.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have hm := maskRun t selX4 (by intro j hj; fin_cases j <;> simp_all [selX4]) (by simpa [recInnerCost] using hcapX)
  have eo : o ++ [true] ++ accW xs xs.length ++ [false] = o ++ recW (supp xs) := by
    rw [accW_full, recW_eq]; simp
  refine ((hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr ?_ ?_).enlarge
    (le_of_eq ?_)
  · funext j; fin_cases j
    · rfl
    · rfl
    · show (o ++ [true] ++ accW xs xs.length ++ [false]).length = (o ++ recW (supp xs)).length
      rw [eo]
    · rfl
    · rfl
  · funext j; fin_cases j
    · rfl
    · show overlay (frame (List.replicate xs.length true)) Ub = Ub
      exact hUb
    · show overlay (o ++ [true] ++ accW xs xs.length ++ [false]) B = overlay (o ++ recW (supp xs)) B
      rw [eo]
    · rfl
    · rfl
  · simp [recInnerCost]

end NearCubicWires.WireExponent3_5.ListMachine.Print
