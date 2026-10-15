import Proof.CaseAnalysis.RecoveryGrammarUnary

/-! The existing all-true address worker executes the literal original
grammar less-than expression inside the same reusable grammar bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarLessRun
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
open RecoveryBoundedGrammarWorker (positioned paddedData resultData resultHeads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 42) : Fin 78:=
  if j=34 then 41 else if j=37 then 42 else if j=39 then 44
  else if j=40 then 72 else if j=41 then 50 else j.castAdd 36
theorem slots_injective : Function.Injective slots:=by decide
theorem slots_stack (j : Fin 42) : slots j≠74:=by fin_cases j <;> decide
def driver (i : Fin 78):=decide (i=35 ∨ i=72)
noncomputable def body:=RecoveryFocus.machine slots RecoveryBoundedAddressReuse.machine
noncomputable def machine:=RecoveryBoundedGrammarWorker.machine body driver

theorem input_heads (out stack : List Bool) :
    ∀ j,positioned driver out stack (slots j)=RecoveryBoundedAddressReuse.finalHeads out j := by
  intro j;fin_cases j <;> rfl

theorem raw_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit upper W D L : ℕ) (out stack : List Bool)
    (A : Fin 78→List Bool) (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+upper*(3*limit+1)+3*limit≤W)
    (hg : (compileExpr b (BoolExpr.any ((List.range upper).map
      (fun value=>unaryEqualsExpr row start limit value hblock)))).final.nodes.length≤W)
    (hu : upper≤W) (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W)≤D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W≤L)
    (hA : ∀ j,A (slots j)=RecoveryBoundedAddressReuse.finalData
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) b.nodes.length (capacity W) D 0 limit upper L
      out (List.replicate (capacity W) true) j) :
    let compiled:=compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom body (RecoveryBoundedAddressReuse.resetBudget upper W)
      ⟨body.start,positioned driver out stack,A⟩=some r ∧
      r.steps≤RecoveryBoundedAddressReuse.resetBudget upper W ∧
      r.final.heads 20=result.length ∧ r.final.heads 74=stack.length ∧
      r.final.tapes=install slots A (RecoveryBoundedAddressReuse.finalData
        (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) compiled.output.val (capacity W) D upper limit upper L
        result (List.replicate (capacity W) true)) := by
  let compiled:=compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))
  let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedGrammarLess.less_run b row start limit upper W D L hblock out hi hp hg hu hD hL
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedAddressReuse.machine
    _ (positioned driver out stack) A (RecoveryBoundedAddressReuse.entry (n:=q) row start limit W D L
      b.nodes.length upper out (List.replicate (capacity W) true))
    (by rw [RecoveryBoundedAddressReuse.entry_heads];exact input_heads out stack)
    (by rw [RecoveryBoundedAddressReuse.entry_tapes];exact hA) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_,?_⟩
  · change r.final.heads (slots 20)=_
    rw [rh 20,ph]
    rfl
  · rw [(rkeep 74 slots_stack).1]
    rfl
  · exact (HierarchyWidth.install_eq slots slots_injective A r.final.tapes
      (RecoveryBoundedAddressReuse.finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start)
        compiled.output.val (capacity W) D upper limit upper L result (List.replicate (capacity W) true))
      (by intro j;rw [rt j,pt]) (by intro i h;exact (rkeep i h).2)).symm

theorem less_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit upper W D L S B : ℕ) (out stack : List Bool)
    (A : Fin 78→List Bool) (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+upper*(3*limit+1)+3*limit≤W)
    (hg : (compileExpr b (BoolExpr.any ((List.range upper).map
      (fun value=>unaryEqualsExpr row start limit value hblock)))).final.nodes.length≤W)
    (hu : upper≤W) (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W)≤D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W≤L)
    (hA : ∀ j,A (slots j)=RecoveryBoundedAddressReuse.finalData
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) b.nodes.length (capacity W) D 0 limit upper L
      out (List.replicate (capacity W) true) j)
    (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S) (hAB : ∀ i,(A i).length≤B)
    (hB : S+RecoveryBoundedAddressReuse.resetBudget upper W+3≤B) :
    let compiled:=compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let next:=install slots A (RecoveryBoundedAddressReuse.finalData
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) compiled.output.val (capacity W) D upper limit upper L
      result (List.replicate (capacity W) true))
    ∃ r,runFrom machine (2*(RecoveryBoundedAddressReuse.resetBudget upper W+2)+2)
      (RecoveryBoundedGrammarWorker.entry body driver out stack (paddedData B A) B)=some r ∧
      r.steps≤2*(RecoveryBoundedAddressReuse.resetBudget upper W+2)+2 ∧
      r.final.heads=resultHeads result.length stack.length ∧
      r.final.tapes=resultData (paddedData B next) B ∧
      (∀ i,i.val<73 → (paddedData B next i).length≤B) := by
  obtain ⟨p,pr,ps,ph,pk,pt⟩:=raw_run b row start limit upper W D L out stack A hblock hi hp hg hu hD hL hA
  obtain ⟨r,rr,rs,rh,rt,rb⟩:=RecoveryBoundedGrammarWorker.padded_reset_run body driver out stack A
    (RecoveryBoundedAddressReuse.resetBudget upper W) S B (by decide) (by decide) p pr ps hS ho hk hAB hB
  rw [ph,pk] at rh
  rw [pt] at rt rb
  exact ⟨r,rr,rs,rh,rt,rb⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarLessRun
