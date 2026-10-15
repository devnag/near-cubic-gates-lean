import Proof.CaseAnalysis.RecoverySelectorPairCall

/-! Both original field selectors execute consecutively. The first actual
output is saved, the next graph count is installed by paid increment, and
the second selector reads exactly the same prior live-reference stream. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine (Composition.machine selector handoff) selector
def budget (count acc next W : ℕ):=RecoveryBoundedSelectorReuse.resetBudget count W+1+
  (2*capacity W+4*acc+4*next+24)+1+RecoveryBoundedSelectorReuse.resetBudget count W

theorem pair_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start nextStart limit W D L : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (hnext : nextStart+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hn : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) (hL : logCapacity W ≤ L) :
    let left:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
    let values:=liftLiveWires left.extension wires
    let right:=compileFieldSelect left.final (fun row value=>unaryEqualsExpr row nextStart limit value hnext) row values
    let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
    let out1:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let result:=out1++right.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let next:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart
    left.final.nodes.length ≤ W →
    left.final.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W →
    right.final.nodes.length ≤ W →
    ∃ r,runFrom machine (budget wires.length left.output.val next W)
      ⟨machine.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length (capacity W) D 0 limit wires.length L out source next (List.replicate (capacity W) false)⟩=some r ∧
      r.steps ≤ budget wires.length left.output.val next W ∧ r.final.heads=heads result ∧
      r.final.tapes=data next right.output.val (capacity W) D wires.length limit wires.length L result source next
        (ZeroPadding.pad (capacity W) (List.replicate left.output.val true)) := by
  let left:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
  let values:=liftLiveWires left.extension wires
  let right:=compileFieldSelect left.final (fun row value=>unaryEqualsExpr row nextStart limit value hnext) row values
  let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
  let out1:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let next:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart
  dsimp only
  intro hg1 hp2 hg2
  have hvlen : values.length=wires.length := by simp only [values,liftLiveWires,List.length_map]
  have hvraw : values.map (fun w=>w.output.val)=wires.map (fun w=>w.output.val) := raw_lift left.extension wires
  have hcount : left.output.val+1=left.final.nodes.length :=
    RecoveryBoundedSelectorReuse.output_next b row start limit hblock wires
  have haC : left.output.val+1 ≤ capacity W := by
    unfold capacity
    nlinarith [Nat.zero_le (W*W)]
  have hiC : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start ≤ capacity W := by
    unfold capacity
    nlinarith [Nat.zero_le (W*W)]
  have hnC : next+1 ≤ capacity W := by
    change RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart+1 ≤ capacity W
    unfold capacity
    nlinarith [Nat.zero_le (W*W)]
  have hcC : wires.length ≤ capacity W := by
    unfold capacity
    nlinarith [Nat.zero_le (W*W)]
  obtain ⟨a,ar,ast,ah,atp⟩:=selector_run b row start limit W D L hblock wires out tail next
    (List.replicate (capacity W) false) hi hp hg1 hc hD hL
  obtain ⟨z,zr,zs,zh,zt⟩:=handoff_run (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    left.output.val (capacity W) D wires.length limit wires.length L out1 source next haC hiC hnC hcC
  have hz : runFrom handoff (2*capacity W+4*left.output.val+4*next+24)
      (restart a.final handoff.start)=some z := by
    change runFrom handoff _ ⟨handoff.start,a.final.heads,a.final.tapes⟩=some z
    rw [ah,atp]
    exact zr
  let joined:=joinedReceipt a z
  have joinedRun:=Composition.run_join selector handoff _ _ _ a z ar hz
  have hp2' : left.final.nodes.length+values.length*(3*limit+2)+3*limit ≤ W := by rw [hvlen]; exact hp2
  have hc' : values.length ≤ W := by rw [hvlen]; exact hc
  obtain ⟨r,rr,rs,rh,rt⟩:=selector_run left.final row nextStart limit W D L hnext values out1 tail next
    (ZeroPadding.pad (capacity W) (List.replicate left.output.val true)) hn hp2' hg2 hc' hD hL
  have hlast : runFrom selector (RecoveryBoundedSelectorReuse.resetBudget wires.length W)
      (restart joined.final selector.start)=some r := by
    change runFrom selector _ ⟨selector.start,z.final.heads,z.final.tapes⟩=some r
    rw [zh,zt,hcount]
    simpa only [hvlen,hvraw] using rr
  have full:=Composition.run_join (Composition.machine selector handoff) selector _ _ _ joined r joinedRun hlast
  refine ⟨joinedReceipt joined r,full,?_,?_,?_⟩
  · change a.steps+1+z.steps+1+r.steps ≤ budget wires.length left.output.val next W
    rw [zs]
    rw [hvlen] at rs
    unfold budget
    omega
  · change r.final.heads=_
    exact rh
  · change r.final.tapes=_
    simpa only [hvlen,hvraw] using rt

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
