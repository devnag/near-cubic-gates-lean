import SourceAdapters.ShortPCP.Branch
import SourceAdapters.Code.Composition
import Proof.Wire_3_5.SelectionMachineSortRound

/-!
# Two word functions behind one tag bit (a two-way callee)

Paper context: `thm:short-pcp-ours` and `cor:short-pcp-clock`. Their constructions use explicit clock
integers and ordinary polynomial-time subroutines. The instance generator is one program of L's cell
language (`Close.Cells`), which calls one ordinary word function (`Cells.Callee`) any number of times and
keeps intermediate data in its variables and stores. This file packs two word functions into one,
selected by a leading tag bit:

* `dropWF` — the actual program `b :: w ↦ frame w` (skip the first framed pair, copy the rest, close the frame);
* `dropFirst W` — `W` behind a dropped leading bit (`composeFramed dropWF W`);
* `sumWF WA WB` — one word function on `RA ⊕ RB`: input `true :: inA a` or `false :: inB b`, output `outA a` or
  `outB b`, by `Branch.branch` on the tag cell (cell `1` of the framed input).

Generic: no request type or encoding of the short PCP appears here.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Machine.ComposeCarry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Adapters.ShortPCP
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Dropping the first bit -/

/-- `fwd, fwd` over the first framed pair, copy the remaining pairs to stream `1`, then the closing `false`. -/
def dropP : WMX 1 2 :=
  .wm (.seq (WM.fwdC 0 0) (.seq (WM.fwdC 0 0) (.seq (.whs 0 (copyPair 0 1 0 1)) (emitB 1 1 false))))

/-- The start state is the round state `rst` at input position `0` with an empty output. -/
theorem idealStart_rst (w : List Bool) :
    idealStart 1 2 w (fun _ => 0) =
      rst (idealStart 1 2 w (fun _ => 0)) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) [] 0 [] := by
  apply WState.eq
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [rst, idealStart, overlay]
  · funext j; fin_cases j <;> rfl
  · rfl

theorem dropP_run (b : Bool) (w : List Bool) :
    ∃ τ, WXExec (2 * w.length + 8) dropP (idealStart 1 2 (b :: w) (fun _ => 0)) τ (30 * w.length + 30) ∧
      τ.st 1 = frame w := by
  set σ0 := idealStart 1 2 (b :: w) (fun _ => 0) with hσ0
  set cap := 2 * w.length + 8
  have hAB : (0 : Fin 2) ≠ 1 := by decide
  have hC : (0 : Fin 2) ≠ 1 := by decide
  have f1 : WExec cap (WM.fwdC 0 0) (rst σ0 0 1 0 1 [] 0 []) (rst σ0 0 1 0 1 [] 1 []) 5 :=
    fwdA_rst cap σ0 [] hAB hC 0 [] (by omega)
  have f2 : WExec cap (WM.fwdC 0 0) (rst σ0 0 1 0 1 [] 1 []) (rst σ0 0 1 0 1 [] 2 []) 5 :=
    fwdA_rst cap σ0 [] hAB hC 1 [] (by omega)
  have hS : σ0.st 0 = [true, b] ++ frameP w ++ false :: [] := by
    simp [hσ0, idealStart, frame_eq_frameP]
  have c1 : WExec cap (WM.whs 0 (copyPair 0 1 0 1)) (rst σ0 0 1 0 1 [] 2 [])
      (rst σ0 0 1 0 1 [] (2 + 2 * w.length) (frameP w)) (30 * w.length + 1) := by
    simpa using copyLoop_rst cap σ0 [] hAB hC w [true, b] [] [] hS (by simp; omega) (by simp; omega)
  have e1 : WExec cap (emitB 1 1 false) (rst σ0 0 1 0 1 [] (2 + 2 * w.length) (frameP w))
      (rst σ0 0 1 0 1 [] (2 + 2 * w.length) (frameP w ++ [false])) 7 :=
    emitB_rst cap σ0 [] hAB hC (2 + 2 * w.length) (frameP w) false (by simp [frameP_length]; omega)
  refine ⟨rst σ0 0 1 0 1 [] (2 + 2 * w.length) (frameP w ++ [false]), ?_, ?_⟩
  · have h := WExec.seq f1 (WExec.seq f2 (WExec.seq c1 e1))
    have h0 : rst σ0 0 1 0 1 [] 0 [] = σ0 := by rw [hσ0]; exact (idealStart_rst (b :: w)).symm
    rw [h0] at h
    exact WXExec.wm (WExec.mono h (by omega))
  · simp [rst, overlay, frame_eq_frameP]

/-- **Drop the first bit** (`b :: w ↦ frame w`), an actual ordinary program. -/
noncomputable def dropWF {R : Type} (tag : R → Bool) (input : R → List Bool) :
    WordFunction R (fun r => tag r :: input r) (fun r => frame (input r))
      (fun r => 2 * (30 * (input r).length + 30) + 2) :=
  wordFunction_of_ideal dropP 1 (by decide) (fun r => 2 * (input r).length + 8) (fun _ _ => 0)
    (fun r => 30 * (input r).length + 30) (fun _ => le_rfl) (fun r => ⟨rfl, dropP_run (tag r) (input r)⟩)

/-- The budget of `W` behind a dropped leading bit. -/
def dropBudget (L B : ℕ) : ℕ := (2 * (2 * (30 * L + 30) + 2) + 2) + 1 + (2 * B + 2)

/-- **`W` behind a dropped leading bit.** -/
noncomputable def dropFirst {R : Type} {input output : R → List Bool} {budget : R → ℕ} (tag : R → Bool)
    (W : WordFunction R input output budget) :
    WordFunction R (fun r => tag r :: input r) output (fun r => dropBudget (input r).length (budget r)) :=
  NearCubicGates.Adapters.Code.composeFramed (dropWF tag input) W

/-! ## Two word functions behind one tag bit -/

section Sum

variable {RA RB : Type} {inA outA : RA → List Bool} {inB outB : RB → List Bool} {bA : RA → ℕ} {bB : RB → ℕ}

/-- The tagged input word. -/
def sumInput (inA : RA → List Bool) (inB : RB → List Bool) : RA ⊕ RB → List Bool
  | .inl a => true :: inA a
  | .inr b => false :: inB b

/-- The output word. -/
def sumOutput (outA : RA → List Bool) (outB : RB → List Bool) : RA ⊕ RB → List Bool
  | .inl a => outA a
  | .inr b => outB b

/-- The budget of the `inl` side (zero on `inr`). -/
def budgetL (inA : RA → List Bool) (bA : RA → ℕ) : RA ⊕ RB → ℕ
  | .inl a => dropBudget (inA a).length (bA a)
  | .inr _ => 0

/-- The budget of the `inr` side (zero on `inl`). -/
def budgetR (inB : RB → List Bool) (bB : RB → ℕ) : RA ⊕ RB → ℕ
  | .inl _ => 0
  | .inr b => dropBudget (inB b).length (bB b)

/-- The budget of the pair. -/
def sumBudget (inA : RA → List Bool) (bA : RA → ℕ) (inB : RB → List Bool) (bB : RB → ℕ) (r : RA ⊕ RB) : ℕ :=
  2 * (4 * 1 + 4 + budgetL inA bA r + budgetR (RA := RA) inB bB r) + 2

theorem cellAt_tag (b : Bool) (w : List Bool) : Branch.cellAt 1 (b :: w) = b := rfl

/-- **Two word functions behind one tag bit.** -/
noncomputable def sumWF (WA : WordFunction RA inA outA bA) (WB : WordFunction RB inB outB bB) :
    WordFunction (RA ⊕ RB) (sumInput inA inB) (sumOutput outA outB) (sumBudget inA bA inB bB) :=
  Branch.branch (budgetL inA bA) (budgetR inB bB) 1
    ⟨(dropFirst (fun _ => true) WA).program, fun r => by
      obtain ⟨r | r, h⟩ := r
      · exact (dropFirst (fun _ => true) WA).realizes r
      · exact absurd h (by simp [sumInput, cellAt_tag])⟩
    ⟨(dropFirst (fun _ => false) WB).program, fun r => by
      obtain ⟨r | r, h⟩ := r
      · exact absurd h (by simp [sumInput, cellAt_tag])
      · exact (dropFirst (fun _ => false) WB).realizes r⟩

/-- The pair's budget is at most a constant plus twice the sum of the two drop budgets. -/
theorem sumBudget_inl (a : RA) :
    sumBudget inA bA inB bB (.inl a) = 2 * (8 + dropBudget (inA a).length (bA a)) + 2 := by
  simp [sumBudget, budgetL, budgetR]

theorem sumBudget_inr (b : RB) :
    sumBudget inA bA inB bB (.inr b) = 2 * (8 + dropBudget (inB b).length (bB b)) + 2 := by
  simp [sumBudget, budgetL, budgetR]

end Sum

end NearCubicGates.Adapters.Machine.ComposeCarry
