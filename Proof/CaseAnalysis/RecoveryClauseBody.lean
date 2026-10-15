import Proof.CaseAnalysis.RecoveryClauseCollect

/-! One whole original clause and its paid output-stack push. The clause
bank is retained for the following literal's already-paid scratch reset. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseBody
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedClauseState
open RecoveryBoundedClauseCollect (old pushed)
open RecoveryBoundedLiteral (references)
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b : ℕ} (clause : Machine 72 a) (collect : Machine 72 b)
def machine:=Composition.machine clause collect
theorem join (H : Fin 72→ℕ) (A : Fin 72→List Bool) (u v : ℕ)
    (p : ExecutionReceipt 72 a) (q : ExecutionReceipt 72 b)
    (hp : runFrom clause u ⟨clause.start,H,A⟩=some p)
    (hq : runFrom collect v (restart p.final collect.start)=some q) :
    ∃ r,runFrom (machine clause collect) (u+1+v) ⟨(machine clause collect).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join clause collect _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Calls

noncomputable def clause:=RecoveryFocus.machine old RecoveryBoundedClauseRun.machine
noncomputable def machine:=Calls.machine clause RecoveryBoundedClauseCollect.machine
def budget (W C : ℕ):=RecoveryBoundedClauseRun.budget W C+4*W+7

theorem body_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (literals : Fin 3→Literal q)
    (H : Fin 72→ℕ) (A : Fin 72→List Bool) (left right W C L : ℕ) (out pre source tail stack : List Bool)
    (h : State (H∘old) (A∘old) b.nodes.length left right C L out pre source (sourceWord (references values)))
    (hSH : H 71=stack.length) (hSA : A 71=stack)
    (hSource : source=pre++RecoveryBoundedClauseRun.word literals++tail)
    (hFinal : (compileClause b values hv literals).compiled.final.nodes.length ≤ W)
    (hq : q ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hL : C+5*W+7 ≤ L) :
    let compiled:=compileClause b values hv literals
    ∃ result,runFrom machine (budget W C) ⟨machine.start,H,A⟩=some result ∧
      result.steps ≤ budget W C ∧
      State (result.final.heads∘old) (result.final.tapes∘old) compiled.compiled.final.nodes.length compiled.compiled.output.val
        (RecoveryBoundedClauseMeaning.third b values hv literals).compiled.output.val C L
        (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
        (pre++RecoveryBoundedClauseRun.word literals) source (sourceWord (references values)) ∧
      result.final.heads 71=(pushed compiled.compiled.output.val stack).length ∧
      result.final.tapes 71=pushed compiled.compiled.output.val stack := by
  let compiled:=compileClause b values hv literals
  obtain ⟨p,pr,ps,pstate⟩:=RecoveryBoundedClauseRun.clause_run b values hv literals (H∘old) (A∘old)
    left right W C L out pre source tail h hSource hFinal hq hl hr hC hL
  have hinj : Function.Injective old:=by intro i j he;apply Fin.ext;exact congrArg (fun k : Fin 72=>k.val) he
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock old hinj RecoveryBoundedClauseRun.machine _ H A
    ⟨RecoveryBoundedClauseRun.machine.start,H∘old,A∘old⟩ (by intro j;rfl) (by intro j;rfl) p pr
  have rH : r.final.heads∘old=p.final.heads:=funext rh
  have rA : r.final.tapes∘old=p.final.tapes:=funext rt
  have rstate : State (r.final.heads∘old) (r.final.tapes∘old) compiled.compiled.final.nodes.length compiled.compiled.output.val
      (RecoveryBoundedClauseMeaning.third b values hv literals).compiled.output.val C L
      (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
      (pre++RecoveryBoundedClauseRun.word literals) source (sourceWord (references values)) := by
    rw [rH,rA]
    exact pstate
  have hout : ∀ j,old j≠71 := by
    intro j he
    have hv:=congrArg (fun k : Fin 72=>k.val) he
    change j.val=71 at hv
    omega
  have rsH : r.final.heads 71=stack.length:=((rkeep 71 hout).1).trans hSH
  have rsA : r.final.tapes 71=stack:=((rkeep 71 hout).2).trans hSA
  have hcH : ∀ j,r.final.heads (RecoveryBoundedClauseCollect.slots j)=(![0,stack.length,0] : Fin 3→ℕ) j := by
    intro j;fin_cases j
    · exact rstate.restoreH 1
    · exact rsH
    · exact rstate.zeroH
  have hcA : ∀ j,r.final.tapes (RecoveryBoundedClauseCollect.slots j)=
      (![ZeroPadding.pad C (List.replicate compiled.compiled.output.val true),stack,List.replicate C false] : Fin 3→List Bool) j := by
    intro j;fin_cases j
    · exact rstate.gateA 1
    · exact rsA
    · exact rstate.zeroA
  have href : compiled.compiled.output.val ≤ W:=compiled.compiled.output.isLt.le.trans hFinal
  have hc : 2*compiled.compiled.output.val+2 ≤ C:=by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨s,sr,ss,sh,sa⟩:=RecoveryBoundedClauseCollect.collect_run r.final.heads r.final.tapes compiled.compiled.output.val
    C stack hcH hcA hc
  obtain ⟨result,hrun,hsteps,hheads,htapes⟩:=Calls.join clause RecoveryBoundedClauseCollect.machine H A
    (RecoveryBoundedClauseRun.budget W C) (4*compiled.compiled.output.val+6) r s rr sr
  have hb : RecoveryBoundedClauseRun.budget W C+1+(4*compiled.compiled.output.val+6) ≤ budget W C := by
    unfold budget
    omega
  have more:=runFrom_moreFuel machine _ (budget W C-(RecoveryBoundedClauseRun.budget W C+1+(4*compiled.compiled.output.val+6)))
    _ result hrun
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨result,more,?_,?_,?_,?_⟩
  · rw [hsteps]
    have rp:=rs.le.trans ps
    omega
  · rw [hheads,htapes,sh,sa,RecoveryBoundedClauseCollect.old_heads,RecoveryBoundedClauseCollect.old_data]
    exact rstate
  · rw [hheads,sh]
    rfl
  · rw [htapes,sa]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseBody
