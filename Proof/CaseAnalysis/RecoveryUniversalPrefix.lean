import Proof.CaseAnalysis.RecoveryConstantRun

/-! Execute the first three original universal-node calls: both child-field
selectors, then the constant-value equality. All original live references,
graph node order and the shared description-variable block are preserved. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalPrefix
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=TapeEmbedding.machine 2 RecoveryBoundedSelectorPair.machine
noncomputable def machine:=Composition.machine first RecoveryBoundedConstant.machine
def budget (count left right firstIndex secondIndex limit W : ℕ):=
  RecoveryBoundedSelectorPair.budget count left secondIndex W+1+
    RecoveryBoundedConstant.budget right firstIndex limit (capacity W)

theorem prefix_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
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
    let constant:=compileExpr right.final (unaryEqualsExpr row start limit 1 hblock)
    let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
    let out2:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native++right.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let out3:=out2++constant.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart
    left.final.nodes.length ≤ W →
    left.final.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W →
    right.final.nodes.length ≤ W → right.final.nodes.length+3*limit ≤ W →
    ∃ r,runFrom machine (budget wires.length left.output.val right.output.val firstIndex secondIndex limit W)
      ⟨machine.start,RecoveryBoundedConstant.heads out,
        RecoveryBoundedConstant.data firstIndex b.nodes.length (capacity W) D 0 limit wires.length L out source
          secondIndex firstIndex (List.replicate (capacity W) false) (List.replicate (capacity W) false)⟩=some r ∧
      r.steps ≤ budget wires.length left.output.val right.output.val firstIndex secondIndex limit W ∧
      r.final.heads=RecoveryBoundedConstant.heads out3 ∧
      r.final.tapes=RecoveryBoundedConstant.afterUnary firstIndex constant.output.val (capacity W) D limit wires.length L
        (RecoveryBoundedUnaryReuse.forward (n:=n) row start right.final.nodes.length 1 limit out2).flag
        out3 source secondIndex firstIndex (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
        (ZeroPadding.pad (capacity W) (List.replicate right.output.val true)) := by
  let left:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
  let values:=liftLiveWires left.extension wires
  let right:=compileFieldSelect left.final (fun row value=>unaryEqualsExpr row nextStart limit value hnext) row values
  let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
  let out2:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native++right.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart
  let extra : Fin 2→List Bool:=![List.replicate firstIndex true,List.replicate (capacity W) false]
  dsimp only
  intro hleft hp2 hright hp3
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedSelectorPair.pair_run b row start nextStart limit W D L hblock hnext
    wires out tail hi hn hp hc hD hL hleft hp2 hright
  let a:=TapeEmbedding.receipt (fun _ : Fin 2=>0) extra p
  have ar:=TapeEmbedding.run_embed RecoveryBoundedSelectorPair.machine (fun _ : Fin 2=>0) extra _ _ p hpRun
  have ah : a.final.heads=RecoveryBoundedConstant.heads out2 := by
    change Fin.addCases (m:=46) (n:=2) (motive:=fun _=>ℕ) p.final.heads (fun _=>0)=_
    rw [ph]
    rfl
  have atapes : a.final.tapes=RecoveryBoundedConstant.data secondIndex right.output.val (capacity W) D wires.length limit wires.length L
      out2 source secondIndex firstIndex (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
      (List.replicate (capacity W) false) := by
    change Fin.addCases (m:=46) (n:=2) (motive:=fun _=>List Bool) p.final.tapes extra=_
    rw [pt]
    rfl
  have hcount : right.output.val+1=right.final.nodes.length :=
    RecoveryBoundedSelectorReuse.output_next left.final row nextStart limit hnext values
  have hlimit : limit ≤ W := by omega
  have hguard:=RecoveryBoundedNativeGuarded.budget_cubic limit W hlimit
  have hUnary : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D := by
    unfold RecoveryBoundedNativeGuarded.budget at hguard
    change RecoveryBoundedNativeUnaryJoin.budget limit (16384*(W+1)^2) ≤ D
    omega
  have hs : secondIndex ≤ W := by change RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row nextStart ≤ W; omega
  obtain ⟨r,hr,rs,rh,rt⟩:=RecoveryBoundedConstant.constant_run right.final row start limit right.output.val W (capacity W) D
    wires.length L out2 source secondIndex (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
    hblock hcount hi hp3 hs hc (Nat.le_refl _) hUnary
  have hlast : runFrom RecoveryBoundedConstant.machine
      (RecoveryBoundedConstant.budget right.output.val firstIndex limit (capacity W))
      (restart a.final RecoveryBoundedConstant.machine.start)=some r := by
    change runFrom RecoveryBoundedConstant.machine _ ⟨RecoveryBoundedConstant.machine.start,a.final.heads,a.final.tapes⟩=some r
    rw [ah,atapes]
    exact hr
  have full:=Composition.run_join first RecoveryBoundedConstant.machine _ _ _ a r ar hlast
  refine ⟨joinedReceipt a r,full,?_,rh,rt⟩
  change p.steps+1+r.steps ≤ budget wires.length left.output.val right.output.val firstIndex secondIndex limit W
  change p.steps ≤ RecoveryBoundedSelectorPair.budget wires.length left.output.val secondIndex W at ps
  change r.steps ≤ RecoveryBoundedConstant.budget right.output.val firstIndex limit (capacity W) at rs
  unfold budget
  omega

theorem budget_quartic (count left right firstIndex secondIndex limit W : ℕ)
    (hc : count ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hf : firstIndex ≤ W) (hs : secondIndex ≤ W) (hb : limit ≤ W) :
    budget count left right firstIndex secondIndex limit W ≤ 1200000000*(W+1)^4 := by
  have hp:=RecoveryBoundedSelectorPair.budget_quartic count left secondIndex W hc hl hs
  have hq:=RecoveryBoundedConstant.budget_cubic right firstIndex limit W hr hf hb
  unfold budget capacity
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalPrefix
