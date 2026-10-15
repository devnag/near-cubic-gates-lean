import Proof.CaseAnalysis.RowsRawProductBudget

/-! Raw polynomial addition uses the checked row writer with the empty
left monomial. Each original polynomial is scanned once; neither duplicate
monomials nor repeated variable occurrences are cancelled. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialAdd
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (lp rp : ℕ) (out : List Bool) : Fin 5→ℕ:=![lp,rp,out.length,0,0]
def data (C : ℕ) (left right out : List Bool) : Fin 5→List Bool:=
  ![left,right,out,[false],List.replicate C false]
def leftSlots : Fin 4→Fin 5:=![3,0,2,4]
def rightSlots : Fin 4→Fin 5:=![3,1,2,4]
noncomputable def leftMachine:=RecoveryFocus.machine leftSlots CloseoutRowsRawProductRow.machine
noncomputable def rightMachine:=RecoveryFocus.machine rightSlots CloseoutRowsRawProductRow.machine
def finish : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some false,none,none],
    ![.stay,.stay,.right,.stay,.stay]⟩ else none
noncomputable def machine:=Composition.machine (Composition.machine leftMachine rightMachine) finish
def body (p : List (List ℕ)):=p.flatMap ExtIncidence.monomialWord
def budget (left right : List (List ℕ)):=
  CloseoutRowsRawProductRow.budget [] left+CloseoutRowsRawProductRow.budget [] right+3

theorem empty_row (C : ℕ) (p : List (List ℕ)) (out : List Bool) (hc : 1≤C) :
    Step CloseoutRowsRawProductRow.machine (CloseoutRowsRawProductRow.budget [] p)
      (CloseoutRowsRawProductFields.heads 0 0 out)
      (CloseoutRowsRawProductFields.data C [false] (ExtIncidence.stream p) out)
      (CloseoutRowsRawProductFields.heads 0 (body p).length (out++body p))
      (CloseoutRowsRawProductFields.data C [false] (ExtIncidence.stream p) (out++body p)) := by
  have word:CloseoutRowsRawProductRow.word [] p=body p:=by
    unfold CloseoutRowsRawProductRow.word body
    have hm:p.map (fun r=>[]++r)=p:=by simp
    rw [hm]
  simpa only [List.flatMap_nil,List.nil_append,List.length_nil,word,body] using
    (CloseoutRowsRawProductRow.row_run C [] p [] [] out hc)

theorem left_run (C rp : ℕ) (left : List (List ℕ)) (right out : List Bool) (hc : 1≤C) :
    Step leftMachine (CloseoutRowsRawProductRow.budget [] left)
      (heads 0 rp out) (data C (ExtIncidence.stream left) right out)
      (heads (body left).length rp (out++body left))
      (data C (ExtIncidence.stream left) right (out++body left)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=empty_row C left out hc
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock leftSlots (by decide)
    CloseoutRowsRawProductRow.machine _ (heads 0 rp out)
    (data C (ExtIncidence.stream left) right out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  have other:=keep 1 (by intro i;fin_cases i <;> decide)
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    · exact other.1
    · exact (h 2).trans (congrArg (fun H=>H 2) rh)
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact (h 3).trans (congrArg (fun H=>H 3) rh)
  · funext i;fin_cases i
    · exact (t 1).trans (congrArg (fun T=>T 1) rt)
    · exact other.2
    · exact (t 2).trans (congrArg (fun T=>T 2) rt)
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)
    · exact (t 3).trans (congrArg (fun T=>T 3) rt)

theorem right_run (C lp : ℕ) (left : List Bool) (right : List (List ℕ)) (out : List Bool) (hc : 1≤C) :
    Step rightMachine (CloseoutRowsRawProductRow.budget [] right)
      (heads lp 0 out) (data C left (ExtIncidence.stream right) out)
      (heads lp (body right).length (out++body right))
      (data C left (ExtIncidence.stream right) (out++body right)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=empty_row C right out hc
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock rightSlots (by decide)
    CloseoutRowsRawProductRow.machine _ (heads lp 0 out)
    (data C left (ExtIncidence.stream right) out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  have other:=keep 0 (by intro i;fin_cases i <;> decide)
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact other.1
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    · exact (h 2).trans (congrArg (fun H=>H 2) rh)
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact (h 3).trans (congrArg (fun H=>H 3) rh)
  · funext i;fin_cases i
    · exact other.2
    · exact (t 1).trans (congrArg (fun T=>T 1) rt)
    · exact (t 2).trans (congrArg (fun T=>T 2) rt)
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)
    · exact (t 3).trans (congrArg (fun T=>T 3) rt)

theorem finish_run (C lp rp : ℕ) (left right out : List Bool) :
    Step finish 1 (heads lp rp out) (data C left right out)
      (heads lp rp (out++[false])) (data C left right (out++[false])) := by
  have hs:step finish ⟨0,heads lp rp out,data C left right out⟩=
      some ⟨1,heads lp rp (out++[false]),data C left right (out++[false])⟩:=by
    simp only [step,finish,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,heads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,data,heads,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem add_run (C : ℕ) (left right : List (List ℕ)) (out : List Bool) (hc : 1≤C) :
    Step machine (budget left right) (heads 0 0 out)
      (data C (ExtIncidence.stream left) (ExtIncidence.stream right) out)
      (heads (body left).length (body right).length (out++ExtIncidence.stream (left++right)))
      (data C (ExtIncidence.stream left) (ExtIncidence.stream right)
        (out++ExtIncidence.stream (left++right))) := by
  have first:=left_run C 0 left (ExtIncidence.stream right) out hc
  have second:=right_run C (body left).length (ExtIncidence.stream left) right (out++body left) hc
  have last:=finish_run C (body left).length (body right).length
    (ExtIncidence.stream left) (ExtIncidence.stream right) ((out++body left)++body right)
  have all:=(first.seq second).seq last
  have time:CloseoutRowsRawProductRow.budget [] left+1+
      CloseoutRowsRawProductRow.budget [] right+1+1=budget left right:=by unfold budget;omega
  rw [time] at all
  have output:((out++body left)++body right)++[false]=out++ExtIncidence.stream (left++right):=by
    simp [body,ExtIncidence.stream,List.flatMap_append,List.append_assoc]
  simpa only [machine,output] using all

theorem budget_bound (left right : List (List ℕ)) :
    budget left right≤32*(CloseoutRowsRawProductBudget.inputLength left right+2) := by
  have l:=CloseoutRowsRawProductBudget.row_bound [] left
  have r:=CloseoutRowsRawProductBudget.row_bound [] right
  simp only [List.flatMap_nil,List.length_nil] at l r
  unfold budget CloseoutRowsRawProductBudget.inputLength
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialAdd
