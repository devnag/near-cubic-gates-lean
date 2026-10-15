import Proof.CaseAnalysis.RecoveryTableState

/-! The checked physical original-node iteration advances the literal
compileUniversalNodes prefix and returns its entire reusable bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTable
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def StepFits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (k : ℕ) (hk : k+1 ≤ bound) (W : ℕ) : Prop :=
  let before:=compileUniversalNodes b address k (by omega)
  RecoveryBoundedTableNode.Fits before.final ⟨k,by omega⟩ address before.values W

theorem step_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (W D L : ℕ) (out addressTail : List Bool)
    (k : ℕ) (hk : k+1 ≤ bound) (h : StepFits b address k hk W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    ∃ r,runFrom RecoveryBoundedTableNode.machine (RecoveryBoundedTableNode.budget W)
      (entry b address W D L out addressTail k (by omega))=some r ∧
      r.steps ≤ RecoveryBoundedTableNode.budget W ∧
      r.final.heads=(entry b address W D L out addressTail (k+1) hk).heads ∧
      r.final.tapes=(entry b address W D L out addressTail (k+1) hk).tapes := by
  let before:=compileUniversalNodes b address k (by omega)
  let row : Fin (bound+1):=⟨k,by omega⟩
  let node:=compileUniversalNode before.final row address before.values
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let beforeWord:=out++native b address k (by omega)
  let result:=beforeWord++node.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  have hlen : before.values.length=k:=compileUniversalNodes_values_length b address k (by omega)
  obtain ⟨r,hr,rs,rh,rt⟩:=RecoveryBoundedTableNode.node_run before.final row address W D L before.values
    beforeWord addressTail h hD hL
  change runFrom RecoveryBoundedTableNode.machine (RecoveryBoundedTableNode.budget W)
    ⟨RecoveryBoundedTableNode.machine.start,heads beforeWord,
      data (index n bound k 6) before.final.nodes.length C D 0 F before.values.length L beforeWord
        (ZeroPadding.pad C (sourceWord (references b address k (by omega))))
        (index n bound k (6+F)) (index n bound k 0) 0 0 0 (List.ofFn address++addressTail) n []⟩=some r at hr
  rw [hlen] at hr
  change r.final.heads=heads result at rh
  change r.final.tapes=data (index n bound k 6+(2*F+6)) node.compiled.final.nodes.length C D 0 F (before.values.length+1) L
    result (ZeroPadding.pad C (sourceWord (references b address k (by omega)++[node.compiled.output.val])))
    (index n bound k (6+F)+(2*F+6)) (index n bound k 0+(2*F+6)) 0 0 0
    (List.ofFn address++addressTail) n [] at rt
  rw [hlen,index_succ,index_succ,index_succ] at rt
  have hw : out++native b address (k+1) hk=result := by
    rw [native_succ]
    change out++(native b address k (by omega)++node.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)=result
    exact (List.append_assoc _ _ _).symm
  have hrefs : references b address (k+1) hk=references b address k (by omega)++[node.compiled.output.val]:=
    references_succ b address k hk
  have hf : (compileUniversalNodes b address (k+1) hk).final=node.compiled.final:=final_succ b address k hk
  refine ⟨r,hr,rs,?_,?_⟩
  · change r.final.heads=heads (out++native b address (k+1) hk)
    rw [hw]
    exact rh
  · dsimp only [entry]
    rw [hw,hrefs,hf]
    exact rt

end NearCubicWires.RepairOrdinary.RecoveryBoundedTable
