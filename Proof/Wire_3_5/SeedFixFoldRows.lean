import Proof.Wire_3_5.SeedFixExprCopy
import Proof.Wire_3_5.BlockJoin

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

/-- A row record in an entry. -/
def rowRec (V : SExpr) : List Bool := true :: exprWord V

/-- An entry record: a marker, its rows, a terminator. -/
def entryRec (rs : List SExpr) : List Bool := true :: (rs.flatMap rowRec ++ [false])

/-- The accumulator's state: the product so far, the accumulator's backing, the scratch output, the right register and
the product's left-term register. -/
structure FoldSt where
  A : SExpr
  Xb : List Bool
  Y : List Bool
  ROW : List Bool
  AT : List Bool

/-- The accumulator tape. -/
def FoldSt.X (s : FoldSt) : List Bool := overlay (exprWord s.A) s.Xb

/-- One row multiplied in. -/
def FoldSt.step (s : FoldSt) (V : SExpr) : FoldSt :=
  ⟨smul s.A V, s.X, overlay (exprWord (smul s.A V)) s.Y, overlay (exprWord V) s.ROW, mRegAt s.A s.AT s.A.length⟩

/-- The state after the first `r` rows. -/
def foldAt (s0 : FoldSt) (rs : List SExpr) (r : ℕ) : FoldSt := (rs.take r).foldl FoldSt.step s0

theorem foldAt_A (s0 : FoldSt) : ∀ (rs : List SExpr), (foldAt s0 rs rs.length).A = sfold s0.A rs := by
  intro rs
  unfold foldAt
  rw [List.take_length]
  induction rs generalizing s0 with
  | nil => rfl
  | cons V rs ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem foldAt_succ (s0 : FoldSt) (rs : List SExpr) (r : ℕ) (hr : r < rs.length) :
    foldAt s0 rs (r + 1) = (foldAt s0 rs r).step rs[r] := by
  unfold foldAt
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.foldl_append]
  rfl

/-- The product's coefficients stay nonzero under unit rows. -/
theorem foldAt_ne_zero (s0 : FoldSt) (rs : List SExpr) (h0 : ∀ a ∈ s0.A, a.1 ≠ 0)
    (hrs : ∀ V ∈ rs, ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1) : ∀ r, ∀ a ∈ (foldAt s0 rs r).A, a.1 ≠ 0 := by
  intro r
  unfold foldAt
  generalize hL : rs.take r = L
  have hL' : ∀ V ∈ L, ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1 := fun V hV => hrs V (List.mem_of_mem_take (by rw [hL]; exact hV))
  clear hL
  induction L generalizing s0 with
  | nil => exact h0
  | cons V L ih =>
    rw [List.foldl_cons]
    exact ih _ (smul_ne_zero s0.A V h0 (hL' V List.mem_cons_self)) (fun W hW => hL' W (List.mem_cons_of_mem _ hW))

/-! ## The bank (tapes 0 the block, 1 the accumulator, 2 the scratch output, 3 the right register, 4 the left-term
register, 5–7 the product's logs, 8 the copies' log) -/

def bank9 (B : List Bool) (s : FoldSt) (cI cT cA cC : ℕ) : Fin 9 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false]

def hd9 (p : ℕ) : Fin 9 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0]

def f9N : Fin 1 → Fin 9 := ![0]

theorem install_f9N (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install f9N A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f9N (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH f9N H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def f9R : Fin 3 → Fin 9 := ![0, 3, 8]

theorem install_f9R (A : Fin 9 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install f9R A v = ![v 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f9R (H : Fin 9 → ℕ) (v : Fin 3 → ℕ) :
    dockH f9R H v = ![v 0, H 1, H 2, v 1, H 4, H 5, H 6, H 7, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def f9M : Fin 7 → Fin 9 := ![1, 3, 2, 4, 5, 6, 7]

theorem install_f9M (A : Fin 9 → List Bool) (v : Fin 7 → List Bool) :
    RecoveryRootRound.install f9M A v = ![A 0, v 0, v 2, v 1, v 3, v 4, v 5, v 6, A 8] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f9M (H : Fin 9 → ℕ) (v : Fin 7 → ℕ) :
    dockH f9M H v = ![H 0, v 0, v 2, v 1, v 3, v 4, v 5, v 6, H 8] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_other _ _ _ _ (by decide)

def f9B : Fin 3 → Fin 9 := ![2, 1, 8]

theorem install_f9B (A : Fin 9 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install f9B A v = ![A 0, v 1, v 0, A 3, A 4, A 5, A 6, A 7, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f9B (H : Fin 9 → ℕ) (v : Fin 3 → ℕ) :
    dockH f9B H v = ![H 0, v 1, v 0, H 3, H 4, H 5, H 6, H 7, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def selO : Fin 2 → Bool := ![false, true]
def selBoth : Fin 2 → Bool := ![true, true]

/-- One row: past its marker, into the right register, the product, the product back into the accumulator. -/
noncomputable def fRowBody :=
  Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine f9N nudgeM)
    (RecoveryFocus.machine f9R (MaskedReset.machine (ExprCopy.machine true) selO)))
    (RecoveryFocus.machine f9M exprMulM))
    (RecoveryFocus.machine f9B (MaskedReset.machine (ExprCopy.machine true) selBoth))

def fRowCost (s : FoldSt) (V : SExpr) : ℕ :=
  1 + 1 + (2 * (exprWord V).length + 2) + 1 + mulCost s.A V + 1 + (2 * (exprWord (smul s.A V)).length + 2)

/-- The capacities one row needs. -/
def RowCaps (s : FoldSt) (V : SExpr) (cI cT cA cC : ℕ) : Prop :=
  tcBound s.A ≤ cT ∧ ibound s.A V ≤ cT ∧ ilBound s.A V ≤ cI ∧ s.A.length * (mOuterCost s.A V + 2) + 1 + 1 + 1 ≤ cA ∧
    (exprWord V).length ≤ cC ∧ (exprWord (smul s.A V)).length ≤ cC

theorem row_step (s : FoldSt) (V : SExpr) (pre tail : List Bool) (cI cT cA cC : ℕ)
    (hA : ∀ a ∈ s.A, a.1 ≠ 0) (hV : ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1) (hc : RowCaps s V cI cT cA cC) :
    Step fRowBody (fRowCost s V) (hd9 pre.length) (bank9 (pre ++ rowRec V ++ tail) s cI cT cA cC)
      (hd9 (pre.length + (rowRec V).length)) (bank9 (pre ++ rowRec V ++ tail) (s.step V) cI cT cA cC) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  set B := pre ++ rowRec V ++ tail
  set P := smul s.A V
  -- 1: past the row marker
  have s1 := dockRun (nudge_run B pre.length) f9N (by decide) (hd9 pre.length) (bank9 B s cI cT cA cC)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_f9N, install_f9N] at s1
  -- 2: the row into the right register
  have hr := ExprCopy.run true (pre ++ [true]) V tail [] s.ROW
  have eB : pre ++ [true] ++ exprWord V ++ tail = B := by simp [B, rowRec]
  rw [eB] at hr
  simp only [owC, if_true, List.nil_append] at hr
  have hr0 : Step (ExprCopy.machine true) (exprWord V).length ![pre.length + 1, 0] ![B, s.ROW]
      ![pre.length + 1 + (exprWord V).length, (exprWord V).length] ![B, overlay (exprWord V) s.ROW] := by
    refine (hr.congr_in ?_ rfl).congr ?_ rfl
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp
  have hr' := hr0.mask (cap := cC) selO (by intro j hj; fin_cases j <;> first | rfl | simp [selO] at hj) hc5
  have hr'' : Step (MaskedReset.machine (ExprCopy.machine true) selO) (2 * (exprWord V).length + 2)
      ![pre.length + 1, 0, 0] ![B, s.ROW, List.replicate cC false]
      ![pre.length + 1 + (exprWord V).length, 0, 0] ![B, overlay (exprWord V) s.ROW, List.replicate cC false] := by
    refine (hr'.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockRun hr'' f9R (by decide) (hd9 (pre.length + 1)) (bank9 B s cI cT cA cC)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_f9R, install_f9R] at s2
  -- 3: the product
  have hm := exprMul_run s.A V hA hV (s.Xb.drop (exprWord s.A).length) (s.ROW.drop (exprWord V).length) s.Y s.AT
    cI cT cA hc1 hc2 hc3 hc4
  set s2st : FoldSt := ⟨s.A, s.Xb, s.Y, overlay (exprWord V) s.ROW, s.AT⟩
  set s3st : FoldSt := ⟨s.A, s.Xb, overlay (exprWord P) s.Y, overlay (exprWord V) s.ROW, mRegAt s.A s.AT s.A.length⟩
  have s3 := dockKeep hm f9M (by decide) (hd9 (pre.length + 1 + (exprWord V).length)) (bank9 B s2st cI cT cA cC)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_f9M] at s3
  -- 4: the product back into the accumulator
  have hb := ExprCopy.run true [] P (s.Y.drop (exprWord P).length) [] s.X
  simp only [owC, if_true, List.nil_append, List.length_nil] at hb
  have hb' := hb.mask (cap := cC) selBoth (by intro j _; fin_cases j <;> rfl) hc6
  have hb'' : Step (MaskedReset.machine (ExprCopy.machine true) selBoth) (2 * (exprWord P).length + 2)
      (fun _ => 0) ![overlay (exprWord P) s.Y, s.X, List.replicate cC false] (fun _ => 0)
      ![overlay (exprWord P) s.Y, overlay (exprWord P) s.X, List.replicate cC false] := by
    refine (hb'.congr_in ?_ ?_).congr ?_ ?_
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  have s4 := dockKeep hb'' f9B (by decide) (hd9 (pre.length + 1 + (exprWord V).length)) (bank9 B s3st cI cT cA cC)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_f9B] at s4
  have hall := (((s1.congr (hout' := hd9 (pre.length + 1)) (tout' := bank9 B s cI cT cA cC)
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := hd9 (pre.length + 1 + (exprWord V).length)) (tout' := bank9 B s2st cI cT cA cC)
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s3.congr (tout' := bank9 B s3st cI cT cA cC) rfl (by funext j; fin_cases j <;> rfl))).seq
    (s4.congr (tout' := bank9 B (s.step V) cI cT cA cC) rfl (by funext j; fin_cases j <;> rfl))
  have eL : pre.length + 1 + (exprWord V).length = pre.length + (rowRec V).length := by simp [rowRec]; omega
  rw [eL] at hall
  exact hall

/-! ## The rows of one entry -/

/-- The block's head before row `r` of an entry starting after `pre`. -/
def rowPos (pre : List Bool) (rs : List SExpr) (r : ℕ) : ℕ := pre.length + ((rs.take r).flatMap rowRec).length

theorem rows_split (pre tail : List Bool) (rs : List SExpr) (r : ℕ) (hr : r < rs.length) :
    pre ++ rs.flatMap rowRec ++ tail =
      (pre ++ (rs.take r).flatMap rowRec) ++ rowRec rs[r] ++ ((rs.drop (r + 1)).flatMap rowRec ++ tail) := by
  have e : rs = rs.take r ++ rs[r] :: rs.drop (r + 1) := by
    rw [← List.drop_eq_getElem_cons hr, List.take_append_drop]
  calc pre ++ rs.flatMap rowRec ++ tail = pre ++ (rs.take r ++ rs[r] :: rs.drop (r + 1)).flatMap rowRec ++ tail :=
        congrArg (fun l => pre ++ l.flatMap rowRec ++ tail) e
    _ = _ := by simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem rows_read (pre tail : List Bool) (rs : List SExpr) (r : ℕ) (hr : r ≤ rs.length) :
    readTapeBit (pre ++ rs.flatMap rowRec ++ false :: tail) (rowPos pre rs r) = decide (r < rs.length) := by
  unfold rowPos
  by_cases h : r < rs.length
  · rw [rows_split pre (false :: tail) rs r h, decide_eq_true h, List.append_assoc]
    rw [show pre.length + ((rs.take r).flatMap rowRec).length = (pre ++ (rs.take r).flatMap rowRec).length by simp]
    exact Streaming.read_append _ _ _
  · have hr' : r = rs.length := by omega
    subst hr'
    rw [decide_eq_false h, List.take_length]
    rw [show pre.length + (rs.flatMap rowRec).length = (pre ++ rs.flatMap rowRec).length by simp]
    exact Streaming.read_append _ _ _

noncomputable def rowsMulM := StreamController.machine fRowBody 0

/-- The cost of an entry's rows (the loop's `rest 0`). -/
def rowsMulCost (s0 : FoldSt) (rs : List SExpr) : ℕ :=
  ((List.range (rs.length - 0)).map (fun i => fRowCost (foldAt s0 rs (0 + i)) (rs.getD (0 + i) []) + 2)).sum + 1

/-- **An entry's rows multiplied into the accumulator**: the block's head from the first row to the entry's terminator. -/
theorem rowsMul_run (s0 : FoldSt) (rs : List SExpr) (pre tail : List Bool) (cI cT cA cC : ℕ)
    (h0 : ∀ a ∈ s0.A, a.1 ≠ 0) (hrs : ∀ V ∈ rs, ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1)
    (hc : ∀ r (hr : r < rs.length), RowCaps (foldAt s0 rs r) rs[r] cI cT cA cC) :
    Step rowsMulM (rowsMulCost s0 rs) (hd9 (rowPos pre rs 0))
      (bank9 (pre ++ rs.flatMap rowRec ++ false :: tail) s0 cI cT cA cC)
      (hd9 (rowPos pre rs rs.length))
      (bank9 (pre ++ rs.flatMap rowRec ++ false :: tail) (foldAt s0 rs rs.length) cI cT cA cC) := by
  set B := pre ++ rs.flatMap rowRec ++ false :: tail
  let L : WhileBody 9 _ :=
    { body := fRowBody
      tape := 0
      bound := rs.length
      H := fun r => hd9 (rowPos pre rs r)
      A := fun r => bank9 B (foldAt s0 rs r) cI cT cA cC
      cost := fun r => fRowCost (foldAt s0 rs r) (rs.getD r [])
      step := fun r hr => by
        have hs := row_step (foldAt s0 rs r) rs[r] (pre ++ (rs.take r).flatMap rowRec)
          ((rs.drop (r + 1)).flatMap rowRec ++ false :: tail) cI cT cA cC
          (foldAt_ne_zero s0 rs h0 hrs r) (hrs rs[r] (List.getElem_mem hr)) (hc r hr)
        rw [← rows_split pre (false :: tail) rs r hr] at hs
        rw [foldAt_succ s0 rs r hr, show rs.getD r [] = rs[r] by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl]
        have eP : (pre ++ (rs.take r).flatMap rowRec).length + (rowRec rs[r]).length = rowPos pre rs (r + 1) := by
          unfold rowPos
          rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.flatMap_append]; simp; omega
        have eP0 : (pre ++ (rs.take r).flatMap rowRec).length = rowPos pre rs r := by unfold rowPos; simp
        rw [eP, eP0] at hs
        exact hs
      cont := fun r hr => by
        show readTapeBit B (rowPos pre rs r) = true
        rw [rows_read pre tail rs r (by omega)]; simpa using hr
      halt := by
        show readTapeBit B (rowPos pre rs rs.length) = false
        rw [rows_read pre tail rs rs.length (le_refl _)]; simp }
  exact L.run

/-! ## Passing an entry's rows -/

def f9S : Fin 2 → Fin 9 := ![0, 3]

theorem install_f9S (A : Fin 9 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install f9S A v = ![v 0, A 1, A 2, v 1, A 4, A 5, A 6, A 7, A 8] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_f9S (H : Fin 9 → ℕ) (v : Fin 2 → ℕ) :
    dockH f9S H v = ![v 0, H 1, H 2, v 1, H 4, H 5, H 6, H 7, H 8] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

/-- One row passed. -/
noncomputable def skipBody :=
  Composition.machine (RecoveryFocus.machine f9N nudgeM) (RecoveryFocus.machine f9S (ExprCopy.machine false))

noncomputable def rowsSkipM := StreamController.machine skipBody 0

def rowsSkipCost (rs : List SExpr) : ℕ :=
  ((List.range (rs.length - 0)).map (fun i => 1 + 1 + (exprWord (rs.getD (0 + i) [])).length + 2)).sum + 1

theorem skip_step (s : FoldSt) (V : SExpr) (pre tail : List Bool) (cI cT cA cC : ℕ) :
    Step skipBody (1 + 1 + (exprWord V).length) (hd9 pre.length) (bank9 (pre ++ rowRec V ++ tail) s cI cT cA cC)
      (hd9 (pre.length + (rowRec V).length)) (bank9 (pre ++ rowRec V ++ tail) s cI cT cA cC) := by
  set B := pre ++ rowRec V ++ tail
  have s1 := dockRun (nudge_run B pre.length) f9N (by decide) (hd9 pre.length) (bank9 B s cI cT cA cC)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_f9N, install_f9N] at s1
  have hr := ExprCopy.run false (pre ++ [true]) V tail [] s.ROW
  have eB : pre ++ [true] ++ exprWord V ++ tail = B := by simp [B, rowRec]
  rw [eB] at hr
  simp only [owC, Bool.false_eq_true, if_false, List.append_nil, List.length_nil] at hr
  have hr0 : Step (ExprCopy.machine false) (exprWord V).length ![pre.length + 1, 0] ![B, s.ROW]
      ![pre.length + 1 + (exprWord V).length, 0] ![B, s.ROW] := by
    refine (hr.congr_in ?_ ?_).congr ?_ ?_
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp [overlay]
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp [overlay]
  have s2 := dockRun hr0 f9S (by decide) (hd9 (pre.length + 1)) (bank9 B s cI cT cA cC)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_f9S, install_f9S] at s2
  have hall := (s1.congr (hout' := hd9 (pre.length + 1)) (tout' := bank9 B s cI cT cA cC)
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := hd9 (pre.length + 1 + (exprWord V).length)) (tout' := bank9 B s cI cT cA cC)
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have eL : pre.length + 1 + (exprWord V).length = pre.length + (rowRec V).length := by simp [rowRec]; omega
  rw [eL] at hall
  exact hall

/-- **An entry's rows passed**: only the block's head moves. -/
theorem rowsSkip_run (s : FoldSt) (rs : List SExpr) (pre tail : List Bool) (cI cT cA cC : ℕ) :
    Step rowsSkipM (rowsSkipCost rs) (hd9 (rowPos pre rs 0))
      (bank9 (pre ++ rs.flatMap rowRec ++ false :: tail) s cI cT cA cC)
      (hd9 (rowPos pre rs rs.length)) (bank9 (pre ++ rs.flatMap rowRec ++ false :: tail) s cI cT cA cC) := by
  set B := pre ++ rs.flatMap rowRec ++ false :: tail
  let L : WhileBody 9 _ :=
    { body := skipBody
      tape := 0
      bound := rs.length
      H := fun r => hd9 (rowPos pre rs r)
      A := fun _ => bank9 B s cI cT cA cC
      cost := fun r => 1 + 1 + (exprWord (rs.getD r [])).length
      step := fun r hr => by
        have hs := skip_step s rs[r] (pre ++ (rs.take r).flatMap rowRec)
          ((rs.drop (r + 1)).flatMap rowRec ++ false :: tail) cI cT cA cC
        rw [← rows_split pre (false :: tail) rs r hr] at hs
        rw [show rs.getD r [] = rs[r] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl]
        have eP : (pre ++ (rs.take r).flatMap rowRec).length + (rowRec rs[r]).length = rowPos pre rs (r + 1) := by
          unfold rowPos
          rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.flatMap_append]; simp; omega
        have eP0 : (pre ++ (rs.take r).flatMap rowRec).length = rowPos pre rs r := by unfold rowPos; simp
        rw [eP, eP0] at hs
        exact hs
      cont := fun r hr => by
        show readTapeBit B (rowPos pre rs r) = true
        rw [rows_read pre tail rs r (by omega)]; simpa using hr
      halt := by
        show readTapeBit B (rowPos pre rs rs.length) = false
        rw [rows_read pre tail rs rs.length (le_refl _)]; simp }
  exact L.run

end NearCubicWires.WireExponent3_5.SeedFix
