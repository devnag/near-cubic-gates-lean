import Proof.CaseAnalysis.RecoveryGrammarAfter

/-! The original unary-equality compiler in the reusable grammar bank.
The current index/value/limit are physical fields; the graph is the literal
compileExpr suffix and the returned25 scalar is its original output ref. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarUnary
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedGrammarWorker (heads positioned paddedData resultData resultHeads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 37) : Fin 78:=if j=34 then 41 else j.castAdd 41
theorem slots_injective : Function.Injective slots:=by decide
theorem slots_stack (j : Fin 37) : slots j≠74:=by fin_cases j <;> decide
def driver (i : Fin 78):=decide (i=35)
noncomputable def body:=RecoveryFocus.machine slots RecoveryBoundedUnaryReuse.machine
noncomputable def machine:=RecoveryBoundedGrammarWorker.machine body driver

theorem input_heads (out stack : List Bool) :
    ∀ j,positioned driver out stack (slots j)=RecoveryBoundedUnaryReuse.heads out j := by
  intro j;fin_cases j <;> rfl

theorem raw_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out stack : List Bool)
    (A : Fin 78→List Bool) (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C≤D)
    (hA : ∀ j,A (slots j)=RecoveryBoundedUnaryReuse.data
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) b.nodes.length C D value limit false out j) :
    let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let flag:=(RecoveryBoundedUnaryReuse.forward (n:=q) row start b.nodes.length value limit out).flag
    ∃ r,runFrom body (RecoveryBoundedUnaryReuse.budget limit C)
      ⟨body.start,positioned driver out stack,A⟩=some r ∧
      r.steps≤RecoveryBoundedUnaryReuse.budget limit C ∧
      r.final.heads 20=result.length ∧ r.final.heads 74=stack.length ∧
      r.final.tapes=install slots A (RecoveryBoundedUnaryReuse.data 0 compiled.output.val C D value limit flag result) := by
  let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
  let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let flag:=(RecoveryBoundedUnaryReuse.forward (n:=q) row start b.nodes.length value limit out).flag
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedUnaryReuse.literal_run b row start limit value W C D out hblock hi hp hC hD
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedUnaryReuse.machine
    _ (positioned driver out stack) A (RecoveryBoundedUnaryReuse.entry (n:=q) row start b.nodes.length C D value limit out)
    (by rw [RecoveryBoundedUnaryReuse.entry_heads];exact input_heads out stack)
    (by rw [RecoveryBoundedUnaryReuse.entry_tapes];exact hA) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_,?_⟩
  · change r.final.heads (slots 20)=_
    rw [rh 20,ph]
    rfl
  · rw [(rkeep 74 slots_stack).1]
    rfl
  · exact (HierarchyWidth.install_eq slots slots_injective A r.final.tapes
      (RecoveryBoundedUnaryReuse.data 0 compiled.output.val C D value limit flag result)
      (by intro j;rw [rt j,pt]) (by intro i h;exact (rkeep i h).2)).symm

theorem unary_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit value W C D S B : ℕ) (out stack : List Bool)
    (A : Fin 78→List Bool) (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C≤D)
    (hA : ∀ j,A (slots j)=RecoveryBoundedUnaryReuse.data
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) b.nodes.length C D value limit false out j)
    (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S) (hAB : ∀ i,(A i).length≤B)
    (hB : S+RecoveryBoundedUnaryReuse.budget limit C+3≤B) :
    let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let flag:=(RecoveryBoundedUnaryReuse.forward (n:=q) row start b.nodes.length value limit out).flag
    let next:=install slots A (RecoveryBoundedUnaryReuse.data 0 compiled.output.val C D value limit flag result)
    ∃ r,runFrom machine (2*(RecoveryBoundedUnaryReuse.budget limit C+2)+2)
      (RecoveryBoundedGrammarWorker.entry body driver out stack (paddedData B A) B)=some r ∧
      r.steps≤2*(RecoveryBoundedUnaryReuse.budget limit C+2)+2 ∧
      r.final.heads=resultHeads result.length stack.length ∧
      r.final.tapes=resultData (paddedData B next) B ∧
      (∀ i,i.val<73 → (paddedData B next i).length≤B) := by
  obtain ⟨p,pr,ps,ph,pk,pt⟩:=raw_run b row start limit value W C D out stack A hblock hi hp hC hD hA
  obtain ⟨r,rr,rs,rh,rt,rb⟩:=RecoveryBoundedGrammarWorker.padded_reset_run body driver out stack A
    (RecoveryBoundedUnaryReuse.budget limit C) S B (by decide) (by decide) p pr ps hS ho hk hAB hB
  rw [ph,pk] at rh
  rw [pt] at rt rb
  exact ⟨r,rr,rs,rh,rt,rb⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarUnary
