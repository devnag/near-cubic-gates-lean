import Proof.CaseAnalysis.RowsTouchingSelectorBody
import Proof.CaseAnalysis.RowsTouchingSelectorExact

/-! The literal q driver executes the same original touching recursion.
Every iteration reuses the one original support stream and the same I mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsDegreeLoop.machine Coordinate.machine
def budget (q G w P : ℕ):ℕ:=q*(Coordinate.budget q G w P+3)+3
noncomputable def entry {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (initial : State q) (tail : List Bool) (j : ℕ) (_out : List Bool):=
  (⟨Coordinate.machine.start,Coordinate.heads,
    data support K w P C D E j (states support w P initial j) tail⟩:Configuration 35 _)

theorem loop_run {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (initial : State q) (tail : List Bool) (hi:Valid w P 0 initial)
    (hwidth:q+G+1≤w) (hprod:2*q+G≤w) (hP:q+1≤P)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P G≤D) (hE:4*q+3≤E):
    ∃ r,runFrom machine (budget q G w P)
      (RepeatMachine.cfg 0 (entry support K w P C D E initial tail 0 []) q 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry support K w P C D E initial tail q []) q 1 ∧
      r.steps≤budget q G w P:=by
  let source:=entry support K w P C D E initial tail
  have supplier:∀ j<q,∀ out,∃ r,runFrom Coordinate.machine (Coordinate.budget q G w P)
      (source j out)=some r ∧ r.final.heads=(source (j+1) (out++[])).heads ∧
      r.final.tapes=(source (j+1) (out++[])).tapes ∧ r.steps≤Coordinate.budget q G w P:=by
    intro j hj out
    exact body_run support K w P C D E j _ tail hj (states_valid support w P initial hP hi j hj.le)
      hwidth hprod hP hC hScan hW hLookup hD hE
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run Coordinate.machine source (fun _=>[])
    (Coordinate.budget q G w P) q (by intro j hj out;rfl) supplier []
  have emitted:(List.range q).flatMap (fun _ : ℕ=>([] : List Bool))=[]:=by simp
  rw [emitted,List.nil_append] at rf
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Selector
