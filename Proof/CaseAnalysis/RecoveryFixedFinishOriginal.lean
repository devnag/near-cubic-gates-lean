import Proof.CaseAnalysis.RecoveryFixedFinishBank

/-! The reusable continuation consumes the literal final fixed-count AND
and restores the same original row bank, with one saved output reference. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (i : Fin 38):=if i=37 then 1 else 0
theorem heads_eq (out stack : List Bool) :
    RecoveryBoundedFixedContinue.heads out stack extraHeads=
      fun i=>if i=20 then out.length else if i=74 then stack.length else if i=115 then 1 else 0 := by
  funext i
  fin_cases i <;> rfl

theorem ready_original (node C D F L n count Q clauses B : ℕ) (out source stack packet : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B) :
    RecoveryBoundedGrammarBank.ready (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses)
      node B out stack packet source=
    RecoveryBoundedRows.rowData node C D F L B out n count Q clauses [] source stack packet := by
  let A:=RecoveryBoundedGrammarBank.base node B out stack packet source
  have erased : RecoveryBoundedRowErase.data B A=A:=by
    funext i
    fin_cases i <;> simp [A,RecoveryBoundedRowErase.data,RecoveryBoundedGrammarBank.base]
  have h:=RecoveryBoundedRowPrototype.reload_original node C D F L n count Q clauses B out source A
    hC hD hL rfl rfl rfl
  rw [erased] at h
  funext i
  refine Fin.addCases (m:=73) (n:=5) ?_ ?_ i
  · intro j
    simpa only [RecoveryBoundedGrammarBank.ready,RecoveryBoundedRows.rowData,
      RecoveryBoundedRowAfter.data,Fin.addCases_left] using h j
  · intro j
    fin_cases j <;> rfl

open RecoveryBoundedCountConjunction
variable (node C D F L B n count Q clauses ref : ℕ) (out source pre : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

theorem result_upper (packet : List Bool) :
    upper (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes=
      Fin.addCases (m:=37) (n:=1) P (fun _=>RepairSource.VerifierDecoding.CompareMachine.word refs.length) := by
  funext i
  refine Fin.addCases (m:=37) (n:=1) ?_ ?_ i
  · intro j
    change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes
      (RecoveryBoundedRowRandomReset.outerSlots j)=_
    rw [projector]
    simp only [Fin.addCases_left]
  · intro j
    have hj : j=0:=Subsingleton.elim _ _
    subst j
    have h:=result_slot node C D F L B n count Q clauses ref out source pre packet refs P 34
    change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 115=
      ZeroPadding.pad 0 (RepairSource.VerifierDecoding.CompareMachine.word refs.length) at h
    simp only [upper,Fin.addCases_right]
    rw [show ((0 : Fin 1).natAdd 37).natAdd 78=(115 : Fin 116) by decide]
    simpa only [ZeroPadding.pad_zero] using h

theorem result_run (fields : Fin 78→List Bool) (tail : List Bool) (S : ℕ)
    (hC : C+1≤B)
    (hA : ∀ i,(RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source
      (RecoveryBoundedClauseCollect.pushed ref pre) (RecoveryBoundedRowReload.word fields++tail) refs P
        ((RecoveryBoundedRowErase.work i).castAdd 38)).length≤B)
    (hS : pre.length+(2*ref+1+(state node out refs).erased)≤S)
    (hRef : 2*(node+refs.length+1)+2≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hp : (RecoveryBoundedRowReload.word fields).length≤B) :
    let a:=result node C D F L B n count Q clauses ref out source pre (RecoveryBoundedRowReload.word fields++tail) refs P
    ∃ r,runFrom RecoveryBoundedFixedContinue.machine
      (RecoveryBoundedGrammarAfter.budget (node+refs.length+1) B fields)
      ⟨RecoveryBoundedFixedContinue.machine.start,a.heads,RecoveryBoundedFixedRows.stackPadded S a.tapes⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarAfter.budget (node+refs.length+1) B fields ∧
      r.final.heads=RecoveryBoundedFixedContinue.heads (a.tapes 20)
        (RecoveryBoundedAddress.pushed (node+refs.length+1) pre) extraHeads ∧
      r.final.tapes=RecoveryBoundedFixedContinue.data S
        (RecoveryBoundedGrammarBank.ready fields (node+refs.length+1+1) B (a.tapes 20)
          (RecoveryBoundedAddress.pushed (node+refs.length+1) pre) (RecoveryBoundedRowReload.word fields++tail) source)
        (Fin.addCases (m:=37) (n:=1) P (fun _=>RepairSource.VerifierDecoding.CompareMachine.word refs.length)) := by
  let packet:=RecoveryBoundedRowReload.word fields++tail
  let a:=result node C D F L B n count Q clauses ref out source pre packet refs P
  obtain ⟨r,rr,rs,rh,rt⟩:=run (a.tapes 20) pre source tail a.tapes fields extraHeads
    (node+refs.length+1) (2*ref+1+(state node out refs).erased) B S rfl
    (result_output node C D F L B n count Q clauses ref out source pre packet refs P)
    (literal_source node C D F L B n count Q clauses ref out source pre packet refs P)
    (scratch node C D F L B n count Q clauses ref out source pre packet refs P hC)
    (stack_tape node C D F L B n count Q clauses ref out source pre packet refs P)
    (prototype node C D F L B n count Q clauses ref out source pre packet refs P)
    (backing_driver node C D F L B n count Q clauses ref out source pre packet refs P)
    (backing_log node C D F L B n count Q clauses ref out source pre packet refs P) hS hRef
    (work_bound node C D F L B n count Q clauses ref out source pre packet refs P hC hA) hf hp
  have hh : a.heads=RecoveryBoundedFixedContinue.heads (a.tapes 20) pre extraHeads:=by
    rw [heads_eq]
    exact result_heads node C D F L B n count Q clauses ref out source pre packet refs P
  rw [←hh] at rr
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,result_upper node C D F L B n count Q clauses ref out source pre refs P packet]

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
