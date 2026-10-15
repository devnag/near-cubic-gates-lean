import Proof.CaseAnalysis.RowsTouchingPascalBody

/-! The existing counted loop generates all q remaining Pascal rows. There
is one complete table, and both scratch row copies and every physical
driver are retained. The initializer is a separate required call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalTable
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsDegreeLoop.machine PascalBody.machine
def budget (q : ℕ):=q*(PascalBody.budget q+3)+3
def table (q : ℕ):=(List.range (q+1)).flatMap (fun m=>PascalRow.row (q+1) m q)
noncomputable def entry (q C m : ℕ) (out : List Bool):=
  (⟨PascalBody.machine.start,PascalBody.heads out,
    PascalBody.data q C (PascalRow.row (q+1) m q) (PascalRow.row (q+1) m q)
      (List.replicate (PascalReady.width q) false) out⟩ : Configuration 8 _)

theorem table_split (q : ℕ):table q=PascalRow.row (q+1) 0 q++
    (List.range q).flatMap (fun j=>PascalRow.row (q+1) (j+1) q):=by
  rw [table,List.range_succ_eq_map]
  simp only [List.flatMap_cons,List.flatMap_map]

theorem table_length (q : ℕ):(table q).length=(q+1)*PascalReady.width q:=by
  simp only [table,List.length_flatMap,PascalRow.row_length]
  simp [PascalReady.width,List.sum_replicate]

theorem table_run (q C : ℕ) (hnext:PascalNext.budget q+2≤C)
    (happend:2*PascalReady.width q+6≤C):
    ∃ r,runFrom machine (budget q)
      (RepeatMachine.cfg 0 (entry q C 0 (PascalRow.row (q+1) 0 q)) q 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry q C q (table q)) q 1 ∧ r.steps≤budget q:=by
  let source:=entry q C
  let emit:=fun j=>PascalRow.row (q+1) (j+1) q
  have supplier:∀ j<q,∀ out,∃ r,runFrom PascalBody.machine (PascalBody.budget q) (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤PascalBody.budget q:=by
    intro j hj out
    exact PascalBody.body_run q j C out hj hnext happend
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run PascalBody.machine source emit (PascalBody.budget q)
    q (by intro j hj out;rfl) supplier (PascalRow.row (q+1) 0 q)
  rw [←table_split q] at rf
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalTable
