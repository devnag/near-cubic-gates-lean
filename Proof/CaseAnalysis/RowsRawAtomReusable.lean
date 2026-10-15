import Proof.CaseAnalysis.RowsRawAtomCache

/-! Substitution reuses one actual atom cache. The existing paid masked
return restores its cursor; the variable and output cursors remain live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReusable
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawAtomRead.machine (fun i=>decide (i=1))
def heads (ip : ℕ) (out : List Bool) : Fin 6→ℕ:=![ip,0,out.length,0,0,0]
def data (C : ℕ) (index cache out : List Bool) : Fin 6→List Bool:=
  ![index,cache,out,[false],List.replicate C false,List.replicate C false]
def budget (ps : List (List (List ℕ))) (p : List (List ℕ)):=2*CloseoutRowsRawAtomRead.budget ps p+2
def capacityBound (cs : List (List (List ℕ))):=32*((cacheWord cs).length+cs.length+2)

theorem read_run (C : ℕ) (ps : List (List (List ℕ))) (p : List (List ℕ))
    (ip it tail out : List Bool) (hc : CloseoutRowsRawAtomRead.budget ps p≤C) :
    Step machine (budget ps p) (heads ip.length out)
      (data C (ip++ExtIncidence.block ps.length++it) (cacheWord ps++ExtIncidence.stream p++tail) out)
      (heads (ip.length+(ExtIncidence.block ps.length).length) (out++ExtIncidence.stream p))
      (data C (ip++ExtIncidence.block ps.length++it)
        (cacheWord ps++ExtIncidence.stream p++tail) (out++ExtIncidence.stream p)) := by
  have positive:1≤C:=by unfold CloseoutRowsRawAtomRead.budget at hc;omega
  have raw:=CloseoutRowsRawAtomRead.read_run C ps p ip it tail out positive
  have returned:=raw.mask (cap:=C) (fun i=>decide (i=1)) (by
    intro i hi
    have e:i=1:=of_decide_eq_true hi
    subst i;rfl) hc
  apply (returned.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

theorem split (cs : List (List (List ℕ))) (i : ℕ) (hi : i<cs.length) :
    cacheWord cs=cacheWord (cs.take i)++ExtIncidence.stream cs[i]++cacheWord (cs.drop (i+1)) := by
  have h:=congrArg cacheWord (List.take_append_drop (i+1) cs)
  rw [List.take_succ_eq_append_getElem hi] at h
  simpa only [cacheWord,List.flatMap_append,List.flatMap_singleton] using h.symm

theorem read_budget (cs : List (List (List ℕ))) (i : ℕ) (hi : i<cs.length) :
    CloseoutRowsRawAtomRead.budget (cs.take i) cs[i]≤capacityBound cs := by
  have h:=CloseoutRowsRawAtomRead.budget_bound (cs.take i) cs[i]
  have lens:=congrArg List.length (split cs i hi)
  simp only [List.length_append] at lens
  have count:(cs.take i).length≤cs.length:=(List.length_take_le i cs).trans hi.le
  unfold capacityBound
  omega

theorem cache_run (C : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i<cs.length)
    (ip it out : List Bool) (hc : capacityBound cs≤C) :
    Step machine (budget (cs.take i) cs[i]) (heads ip.length out)
      (data C (ip++ExtIncidence.block i++it) (cacheWord cs) out)
      (heads (ip.length+(ExtIncidence.block i).length) (out++ExtIncidence.stream cs[i]))
      (data C (ip++ExtIncidence.block i++it) (cacheWord cs) (out++ExtIncidence.stream cs[i])) := by
  have h:=read_run C (cs.take i) cs[i] ip it (cacheWord (cs.drop (i+1))) out ((read_budget cs i hi).trans hc)
  have count:(cs.take i).length=i:=List.length_take_of_le (by omega)
  rw [count,←split cs i hi] at h
  exact h

theorem cache_budget (C : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i<cs.length)
    (hc : capacityBound cs≤C) : budget (cs.take i) cs[i]≤2*C+2 := by
  have h:=(read_budget cs i hi).trans hc
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReusable
