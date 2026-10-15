import Proof.CaseAnalysis.RecoveryTableRestore

/-! One complete original node iteration, including every paid handoff to
the next node. Fits contains only allocation dominations for the actual
original compiler objects; the enclosing graph bound must discharge them. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableNode
open LocalBitMultitape RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (wires : List (LiveWire b)) (W : ℕ) : Prop :=
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let left:=compileFirstFieldSelect b row wires
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6+(2*F+6) ≤ W ∧
  RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+F)+(2*F+6) ≤ W ∧
  RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0+(2*F+6) ≤ W ∧
  b.nodes.length+wires.length*(3*F+2)+3*F ≤ W ∧ wires.length ≤ W ∧ n ≤ W ∧
  left.final.nodes.length ≤ W ∧ left.final.nodes.length+wires.length*(3*F+2)+3*F ≤ W ∧
  right.final.nodes.length ≤ W ∧ right.final.nodes.length+3*F ≤ W ∧
  constant.final.nodes.length+n*(3*F+1)+3*F ≤ W ∧ input.final.nodes.length ≤ W ∧
  (RecoveryBoundedUniversalNode.cases b row address wires).final.nodes.length+118 ≤ W ∧
  (compileUniversalNode b row address wires).compiled.final.nodes.length ≤ W

noncomputable def machine:=Composition.machine RecoveryBoundedUniversalNode.machine RecoveryBoundedTableRestore.machine
def budget (W : ℕ):=4000000000*(W+1)^4

theorem node_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (W D L : ℕ)
    (wires : List (LiveWire b)) (out addressTail : List Bool) (h : Fits b row address wires W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let C:=capacity W
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let first:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
    let second:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+F)
    let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
    let node:=compileUniversalNode b row address wires
    let refs:=wires.map (fun w=>w.output.val)
    let result:=out++node.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (budget W)
      ⟨machine.start,heads out,data first b.nodes.length C D 0 F wires.length L out
        (ZeroPadding.pad C (sourceWord refs)) second tag 0 0 0 (List.ofFn address++addressTail) n []⟩=some r ∧
      r.steps ≤ budget W ∧ r.final.heads=heads result ∧
      r.final.tapes=data (first+(2*F+6)) node.compiled.final.nodes.length C D 0 F (wires.length+1) L result
        (ZeroPadding.pad C (sourceWord (refs++[node.compiled.output.val])))
        (second+(2*F+6)) (tag+(2*F+6)) 0 0 0 (List.ofFn address++addressTail) n [] := by
  let C:=capacity W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let first:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
  let second:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+F)
  let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
  let left:=compileFirstFieldSelect b row wires
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let node:=compileUniversalNode b row address wires
  let refs:=wires.map (fun w=>w.output.val)
  let result:=out++node.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  dsimp only
  rcases h with ⟨hfirst,hsecond,htag,hp,hcount,ha,hl,hp2,hr,hp3,hp4,hinput,hseven,hnode⟩
  change first+(2*F+6) ≤ W at hfirst
  change second+(2*F+6) ≤ W at hsecond
  change tag+(2*F+6) ≤ W at htag
  change b.nodes.length+wires.length*(3*F+2)+3*F ≤ W at hp
  change left.final.nodes.length ≤ W at hl
  change right.final.nodes.length ≤ W at hr
  change constant.final.nodes.length+n*(3*F+1)+3*F ≤ W at hp4
  change input.final.nodes.length ≤ W at hinput
  change node.compiled.final.nodes.length ≤ W at hnode
  have hbase : b.nodes.length ≤ W:=by omega
  have hleft : left.output.val ≤ W:=left.output.isLt.le.trans hl
  have hright : right.output.val ≤ W:=right.output.isLt.le.trans hr
  have hconstant : constant.output.val ≤ W:=constant.output.isLt.le.trans (by omega)
  have hcurrent : input.output.val ≤ W:=input.output.isLt.le.trans hinput
  have houtput : node.compiled.output.val ≤ W:=node.compiled.output.isLt.le.trans hnode
  have hlen : refs.length=wires.length:=by simp only [refs,List.length_map]
  have hrefs : ∀ r∈refs,r≤W := by
    intro r hmem
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hmem
    exact w.output.isLt.le.trans hbase
  have hfirstField : first+F ≤ W:=by omega
  have hsecondField : second+F ≤ W:=by omega
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedUniversalNode.node_run b row address W D L wires out
    (List.replicate (C-(sourceWord refs).length) false) addressTail hfirstField hsecondField hp hcount ha hD hL
    hl hp2 hr hp3 hp4 hinput hseven hnode
  rw [RecoveryBoundedUniversalNodeTableBoundary.tag_output] at pt
  change p.final.heads=heads result at ph
  change p.final.tapes=RecoveryBoundedUniversalNodeTableBoundary.finished first node.compiled.output.val C D F wires.length L
    result (ZeroPadding.pad C (sourceWord refs)) second tag left.output.val right.output.val constant.output.val input.output.val
    (List.ofFn address++addressTail) n at pt
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedTableRestore.restore_run refs first node.compiled.output.val D F L W result
    second tag left.output.val right.output.val constant.output.val input.output.val (List.ofFn address++addressTail) n
    hfirst hsecond htag houtput hleft hright hconstant hcurrent (by rw [hlen];exact hcount) hrefs hD
  let nodeBudget:=RecoveryBoundedUniversalNode.budget wires.length left.output.val right.output.val constant.output.val
    input.output.val first second tag F n W
  let restoreBudget:=RecoveryBoundedTableRestore.budget refs (first+(2*F+6)) node.compiled.output.val F C W
  have qr' : runFrom RecoveryBoundedTableRestore.machine restoreBudget
      (restart p.final RecoveryBoundedTableRestore.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    change runFrom RecoveryBoundedTableRestore.machine restoreBudget
      ⟨RecoveryBoundedTableRestore.machine.start,heads result,
        RecoveryBoundedUniversalNodeTableBoundary.finished first node.compiled.output.val C D F refs.length L result
          (ZeroPadding.pad C (sourceWord refs)) second tag left.output.val right.output.val constant.output.val input.output.val
          (List.ofFn address++addressTail) n⟩=some q at qr
    rw [hlen] at qr
    exact qr
  have full:=Composition.run_join RecoveryBoundedUniversalNode.machine RecoveryBoundedTableRestore.machine _ _ _ p q pr qr'
  have hnBudget:=RecoveryBoundedUniversalNode.budget_quartic wires.length left.output.val right.output.val constant.output.val
    input.output.val first second tag F n W hcount hleft hright hconstant hcurrent (by omega) (by omega) (by omega)
    (by omega) ha (by omega)
  have hrBudget:=RecoveryBoundedTableRestore.budget_quadratic refs (first+(2*F+6)) node.compiled.output.val F W
    (by rw [hlen];exact hcount) hrefs houtput hfirst (by omega) (by omega)
  change nodeBudget ≤ 3000000000*(W+1)^4 at hnBudget
  change restoreBudget ≤ 524288*(W+1)^2 at hrBudget
  have hbound : nodeBudget+1+restoreBudget ≤ budget W := by
    unfold budget
    nlinarith [Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2)]
  have more:=runFrom_moreFuel machine _ (budget W-(nodeBudget+1+restoreBudget)) _ (joinedReceipt p q) full
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨joinedReceipt p q,more,?_,qh,?_⟩
  · change p.steps+1+q.steps ≤ budget W
    change p.steps ≤ nodeBudget at ps
    change q.steps ≤ restoreBudget at qs
    omega
  · change q.final.tapes=_
    have hnext : node.compiled.output.val+1=node.compiled.final.nodes.length:=
      RecoveryBoundedUniversalNodeTableBoundary.original_next b row address wires
    rw [hnext] at qt
    simpa only [hlen] using qt

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableNode
