import Proof.CaseAnalysis.RecoveryTableOutputRun

/-! The existing original address-expression compiler already compiles the
grammar's less-than fields when its actual input bits are all true. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarLess
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem items_true {n bound : ℕ} (row : Fin (bound+1)) (start limit upper : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    RecoveryBoundedAddress.items row start limit hblock 0 (List.replicate upper true)=
      (List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock) := by
  rw [←List.ofFn_const upper true,RecoveryBoundedAddressFinish.items_ofFn]
  simp only [if_true,Nat.zero_add]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]

theorem first_original {n bound : ℕ} (row : Fin (bound+1)) (upper : ℕ)
    (hblock : 6+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ rowWidth n bound) :
    BoolExpr.any (RecoveryBoundedAddress.items row 6 (OuterPCPRecovery.boundedCircuitFieldLimit n bound)
      hblock 0 (List.replicate upper true))=firstFieldLessExpr row upper := by
  rw [items_true]
  rfl
theorem second_original {n bound : ℕ} (row : Fin (bound+1)) (upper : ℕ)
    (hblock : (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound)+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ rowWidth n bound) :
    BoolExpr.any (RecoveryBoundedAddress.items row (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound)
      (OuterPCPRecovery.boundedCircuitFieldLimit n bound) hblock 0 (List.replicate upper true))=secondFieldLessExpr row upper := by
  rw [items_true]
  rfl

theorem less_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit upper W D L : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (out : List Bool) (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+upper*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))).final.nodes.length ≤ W)
    (hc : upper ≤ W) (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let compiled:=compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom RecoveryBoundedAddressReuse.machine (RecoveryBoundedAddressReuse.resetBudget upper W)
      (RecoveryBoundedAddressReuse.entry (n:=n) row start limit W D L b.nodes.length upper out (List.replicate (capacity W) true))=some r ∧
      r.steps ≤ RecoveryBoundedAddressReuse.resetBudget upper W ∧
      r.final.heads=RecoveryBoundedAddressReuse.finalHeads result ∧
      r.final.tapes=RecoveryBoundedAddressReuse.finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val (capacity W) D upper limit upper L result (List.replicate (capacity W) true) := by
  have hcap : upper ≤ capacity W:=by unfold capacity;nlinarith [Nat.zero_le (W^2)]
  have hs : List.replicate upper true++List.replicate (capacity W-upper) true=List.replicate (capacity W) true := by
    rw [←List.replicate_add,Nat.add_sub_of_le hcap]
  obtain ⟨r,hr,rs,rh,rt⟩:=RecoveryBoundedAddressReuse.reset_run b row start limit W D L hblock
    (List.replicate upper true) out (List.replicate (capacity W-upper) true) hi
    (by simpa only [List.length_replicate] using hp) (by rw [items_true];exact hg)
    (by simpa only [List.length_replicate] using hc) hD hL
  simp only [List.length_replicate,hs] at hr rs rt
  rw [items_true] at rh rt
  exact ⟨r,hr,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarLess
