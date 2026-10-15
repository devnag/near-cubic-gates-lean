import Proof.CaseAnalysis.RecoveryAddressNodeCall

/-! One enclosing run moves from the original constant output through the
paid scalar handoff and the complete original address expression. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine prepare addressMachine
def budget (prior index count W : ℕ):=4*capacity W+4*prior+4*index+30+RecoveryBoundedAddressReuse.resetBudget count W

theorem expression_next {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) :
    (compileExpr b e).output.val+1=(compileExpr b e).final.nodes.length := by
  rw [compileExpr_output,compileExpr_length]
  have h:=nodeCount_pos e
  omega

theorem after_constant_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit prior W D total L : ℕ) (flag : Bool)
    (hblock : start+limit ≤ rowWidth n bound) (bits out tail source : List Bool)
    (secondIndex : ℕ) (savedFirst savedSecond : List Bool) (hbase : prior+1=b.nodes.length)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))).final.nodes.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let compiled:=compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (budget prior index bits.length W)
      ⟨machine.start,heads out,before index prior (capacity W) D limit total L flag out source secondIndex
        savedFirst savedSecond (bits++tail) bits.length⟩=some r ∧
      r.steps ≤ budget prior index bits.length W ∧ r.final.heads=heads result ∧
      r.final.tapes=data index compiled.output.val (capacity W) D bits.length limit total L result source secondIndex
        savedFirst savedSecond (ZeroPadding.pad (capacity W) (List.replicate prior true)) (bits++tail) bits.length := by
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  have hprior : prior+1 ≤ capacity W := by unfold capacity;nlinarith [Nat.zero_le (W^2)]
  have hindex : index+1 ≤ capacity W := by
    change RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+1 ≤ capacity W
    unfold capacity
    nlinarith [Nat.zero_le (W^2)]
  obtain ⟨a,ar,asteps,ah,atapes⟩:=prepare_run index prior (capacity W) D limit total L flag out source secondIndex
    savedFirst savedSecond (bits++tail) bits.length hprior hindex
  obtain ⟨r,hr,rs,rh,rt⟩:=address_run b row start limit W D total L hblock bits out tail source secondIndex
    savedFirst savedSecond (ZeroPadding.pad (capacity W) (List.replicate prior true)) hi hp hg hc hD hL
  have hlast : runFrom addressMachine (RecoveryBoundedAddressReuse.resetBudget bits.length W)
      (restart a.final addressMachine.start)=some r := by
    change runFrom addressMachine _ ⟨addressMachine.start,a.final.heads,a.final.tapes⟩=some r
    rw [ah,atapes,hbase]
    exact hr
  have full:=Composition.run_join prepare addressMachine _ _ _ a r ar hlast
  have hbudget : (4*capacity W+4*prior+4*index+29)+1+RecoveryBoundedAddressReuse.resetBudget bits.length W=
      budget prior index bits.length W := by unfold budget;omega
  rw [hbudget] at full
  refine ⟨joinedReceipt a r,full,?_,rh,rt⟩
  change a.steps+1+r.steps ≤ budget prior index bits.length W
  rw [asteps]
  unfold budget
  omega

theorem budget_quartic (prior index count W : ℕ) (hp : prior ≤ W) (hi : index ≤ W) (hc : count ≤ W) :
    budget prior index count W ≤ 536871700*(W+1)^4 := by
  have h:=RecoveryBoundedAddressReuse.reset_budget_quartic count W hc
  unfold budget capacity
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
