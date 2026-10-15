import Proof.CaseAnalysis.RowsRawAtomSeek

/-! One original variable block selects and appends its actual cached
polynomial. The index is consumed; only logical cache bytes are scanned.
The existing row copier and marker writer are used without reparsing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 2→Fin 5:=![0,1]
noncomputable def seek:=RecoveryFocus.machine seekSlots CloseoutRowsRawAtomSeek.machine
noncomputable def machine:=Composition.machine (Composition.machine seek rightMachine) finish
def budget (ps : List (List (List ℕ))) (p : List (List ℕ)):=
  CloseoutRowsRawAtomSeek.budget ps+CloseoutRowsRawProductRow.budget [] p+7

theorem seek_run (C : ℕ) (ps : List (List (List ℕ))) (ip it cp ct out : List Bool) :
    Step seek (CloseoutRowsRawAtomSeek.budget ps+4) (heads ip.length cp.length out)
      (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawAtomSeek.cacheWord ps++ct) out)
      (heads (ip.length+(ExtIncidence.block ps.length).length)
        (cp.length+(CloseoutRowsRawAtomSeek.cacheWord ps).length) out)
      (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawAtomSeek.cacheWord ps++ct) out) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawAtomSeek.seek_run ps ip it cp ct
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock seekSlots (by decide)
    CloseoutRowsRawAtomSeek.machine _ (heads ip.length cp.length out)
    (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawAtomSeek.cacheWord ps++ct) out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    all_goals exact (keep _ (by intro j;fin_cases j <;> decide)).1
  · funext i;fin_cases i
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)
    · exact (t 1).trans (congrArg (fun T=>T 1) rt)
    all_goals exact (keep _ (by intro j;fin_cases j <;> decide)).2

theorem empty_row_at (C : ℕ) (p : List (List ℕ)) (pre tail out : List Bool) (hc : 1≤C) :
    Step CloseoutRowsRawProductRow.machine (CloseoutRowsRawProductRow.budget [] p)
      (CloseoutRowsRawProductFields.heads 0 pre.length out)
      (CloseoutRowsRawProductFields.data C [false] (pre++ExtIncidence.stream p++tail) out)
      (CloseoutRowsRawProductFields.heads 0 (pre.length+(body p).length) (out++body p))
      (CloseoutRowsRawProductFields.data C [false] (pre++ExtIncidence.stream p++tail) (out++body p)) := by
  obtain ⟨time,ht,tr⟩:=CloseoutRowsRawProductRow.remaining C [] p [] [] pre tail out hc
  have word:CloseoutRowsRawProductRow.word [] p=body p:=by
    simp [CloseoutRowsRawProductRow.word,body]
  simp only [List.flatMap_nil,List.nil_append,List.length_nil,word] at tr
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [CloseoutRowsRawProductRow.machine,
    CloseoutRowsRawProductRow.final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel CloseoutRowsRawProductRow.machine time
    (CloseoutRowsRawProductRow.budget [] p-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem copy_run (C ip : ℕ) (index pre tail out : List Bool) (p : List (List ℕ)) (hc : 1≤C) :
    Step rightMachine (CloseoutRowsRawProductRow.budget [] p) (heads ip pre.length out)
      (data C index (pre++ExtIncidence.stream p++tail) out)
      (heads ip (pre.length+(body p).length) (out++body p))
      (data C index (pre++ExtIncidence.stream p++tail) (out++body p)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=empty_row_at C p pre tail out hc
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock rightSlots (by decide)
    CloseoutRowsRawProductRow.machine _ (heads ip pre.length out)
    (data C index (pre++ExtIncidence.stream p++tail) out) _
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

theorem read_run (C : ℕ) (ps : List (List (List ℕ))) (p : List (List ℕ))
    (ip it tail out : List Bool) (hc : 1≤C) :
    Step machine (budget ps p) (heads ip.length 0 out)
      (data C (ip++ExtIncidence.block ps.length++it)
        (CloseoutRowsRawAtomSeek.cacheWord ps++ExtIncidence.stream p++tail) out)
      (heads (ip.length+(ExtIncidence.block ps.length).length)
        ((CloseoutRowsRawAtomSeek.cacheWord ps).length+(body p).length) (out++ExtIncidence.stream p))
      (data C (ip++ExtIncidence.block ps.length++it)
        (CloseoutRowsRawAtomSeek.cacheWord ps++ExtIncidence.stream p++tail) (out++ExtIncidence.stream p)) := by
  let index:=ip++ExtIncidence.block ps.length++it
  let cache:=CloseoutRowsRawAtomSeek.cacheWord ps++ExtIncidence.stream p++tail
  have first:=seek_run C ps ip it [] (ExtIncidence.stream p++tail) out
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at first
  have middle:=copy_run C (ip.length+(ExtIncidence.block ps.length).length) index
    (CloseoutRowsRawAtomSeek.cacheWord ps) tail out p hc
  have last:=finish_run C (ip.length+(ExtIncidence.block ps.length).length)
    ((CloseoutRowsRawAtomSeek.cacheWord ps).length+(body p).length) index cache (out++body p)
  simp only [index,cache,List.append_assoc] at first middle last
  have all:=(first.seq middle).seq last
  have time:CloseoutRowsRawAtomSeek.budget ps+4+1+CloseoutRowsRawProductRow.budget [] p+1+1=
      budget ps p:=by unfold budget;omega
  rw [time] at all
  simpa only [machine,index,cache,body,ExtIncidence.stream,List.append_assoc] using all

theorem budget_bound (ps : List (List (List ℕ))) (p : List (List ℕ)) :
    budget ps p≤32*((CloseoutRowsRawAtomSeek.cacheWord ps).length+
      (ExtIncidence.stream p).length+ps.length+2) := by
  have h:=CloseoutRowsRawProductBudget.row_bound [] p
  simp only [List.flatMap_nil,List.length_nil] at h
  unfold budget CloseoutRowsRawAtomSeek.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
