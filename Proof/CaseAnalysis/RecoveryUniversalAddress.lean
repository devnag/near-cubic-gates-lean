import Proof.CaseAnalysis.RecoveryAddressNodeRun

/-! One fixed machine executes the literal original universal node's first
four calls: its two shared-child selectors, constant and actual address. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop (capacity)
open RecoveryBoundedSelectorFinish (logCapacity)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=TapeEmbedding.machine 3 RecoveryBoundedUniversalPrefix.machine
noncomputable def machine:=Composition.machine first RecoveryBoundedNodeAddress.machine
def budget (count left right constant firstIndex secondIndex limit addressCount W : ℕ):=
  RecoveryBoundedUniversalPrefix.budget count left right firstIndex secondIndex limit W+1+
    RecoveryBoundedNodeAddress.budget constant firstIndex addressCount W

theorem original_prefix_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (W D L : ℕ)
    (wires : List (LiveWire b)) (out referenceTail addressTail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hn : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound)+
      OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hp : b.nodes.length+wires.length*(3*OuterPCPRecovery.boundedCircuitFieldLimit n bound+2)+
      3*OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hc : wires.length ≤ W) (ha : n ≤ W) (hD : 8388608*(W+1)^3 ≤ D) (hL : logCapacity W ≤ L) :
    let limit:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let left:=compileFirstFieldSelect b row wires
    let values:=liftLiveWires left.extension wires
    let right:=compileSecondFieldSelect left.final row values
    let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
    let addressValue:=compileExpr constant.final (constantAddressSelectionExpr row address)
    let source:=RecoveryBoundedSelectorLoop.sourceWord (wires.map (fun w=>w.output.val))++referenceTail
    let out2:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native++right.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let out3:=out2++constant.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let out4:=out3++addressValue.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
    let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+limit)
    left.final.nodes.length ≤ W → left.final.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W →
    right.final.nodes.length ≤ W → right.final.nodes.length+3*limit ≤ W →
    constant.final.nodes.length+n*(3*limit+1)+3*limit ≤ W → addressValue.final.nodes.length ≤ W →
    ∃ r,runFrom machine (budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W)
      ⟨machine.start,RecoveryBoundedNodeAddress.heads out,
        RecoveryBoundedNodeAddress.data firstIndex b.nodes.length (capacity W) D 0 limit wires.length L out source secondIndex
          (List.replicate (capacity W) false) (List.replicate (capacity W) false) (List.replicate (capacity W) false)
          (List.ofFn address++addressTail) n⟩=some r ∧
      r.steps ≤ budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W ∧
      r.final.heads=RecoveryBoundedNodeAddress.heads out4 ∧
      r.final.tapes=RecoveryBoundedNodeAddress.data firstIndex addressValue.output.val (capacity W) D n limit wires.length L out4 source secondIndex
        (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
        (ZeroPadding.pad (capacity W) (List.replicate right.output.val true))
        (ZeroPadding.pad (capacity W) (List.replicate constant.output.val true)) (List.ofFn address++addressTail) n := by
  let limit:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let left:=compileFirstFieldSelect b row wires
  let values:=liftLiveWires left.extension wires
  let right:=compileSecondFieldSelect left.final row values
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let source:=RecoveryBoundedSelectorLoop.sourceWord (wires.map (fun w=>w.output.val))++referenceTail
  let out2:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native++right.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let out3:=out2++constant.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
  let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+limit)
  have hblock : 6+limit ≤ rowWidth n bound := by unfold rowWidth;omega
  have hnext : 6+limit+limit ≤ rowWidth n bound := by unfold rowWidth;omega
  dsimp only
  intro hleft hp2 hright hp3 hp4 haddress
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedUniversalPrefix.prefix_run b row 6 (6+limit) limit W D L hblock hnext
    wires out referenceTail hi hn hp hc hD hL hleft hp2 hright hp3
  let eh : Fin 3→ℕ:=![0,0,1]
  let et : Fin 3→List Bool:=![List.replicate (capacity W) false,List.ofFn address++addressTail,CompareMachine.word n]
  let a:=TapeEmbedding.receipt eh et p
  have ar:=TapeEmbedding.run_embed RecoveryBoundedUniversalPrefix.machine eh et _ _ p hpRun
  have ah : a.final.heads=RecoveryBoundedNodeAddress.heads out3 := by
    change Fin.addCases (m:=48) (n:=3) (motive:=fun _=>ℕ) p.final.heads eh=_
    rw [ph]
    rfl
  let flag:=(RecoveryBoundedUnaryReuse.forward (n:=n) row 6 right.final.nodes.length 1 limit out2).flag
  have atapes : a.final.tapes=RecoveryBoundedNodeAddress.before firstIndex constant.output.val (capacity W) D limit wires.length L flag
      out3 source secondIndex (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
        (ZeroPadding.pad (capacity W) (List.replicate right.output.val true)) (List.ofFn address++addressTail) n := by
    rw [RecoveryBoundedNodeAddress.before_constant]
    change Fin.addCases (m:=48) (n:=3) (motive:=fun _=>List Bool) p.final.tapes et=_
    rw [pt]
    rfl
  have hlimit : limit ≤ W := by omega
  have hguard:=RecoveryBoundedNativeGuarded.budget_cubic limit W hlimit
  have hUnary : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D := by
    unfold RecoveryBoundedNativeGuarded.budget at hguard
    change RecoveryBoundedNativeUnaryJoin.budget limit (16384*(W+1)^2) ≤ D
    omega
  have hitems:=RecoveryBoundedAddressFinish.original_address row address hblock
  obtain ⟨r,hr,rs,rh,rt⟩:=RecoveryBoundedNodeAddress.after_constant_run constant.final row 6 limit constant.output.val W D wires.length L
    flag hblock (List.ofFn address) out3 addressTail source secondIndex
    (ZeroPadding.pad (capacity W) (List.replicate left.output.val true))
    (ZeroPadding.pad (capacity W) (List.replicate right.output.val true))
    (RecoveryBoundedNodeAddress.expression_next right.final (firstFieldEqualsExpr row 1)) hi
    (by simpa only [List.length_ofFn] using hp4) (by rw [hitems];exact haddress)
    (by simpa only [List.length_ofFn] using ha) hUnary hL
  simp only [List.length_ofFn] at hr rs rh rt
  rw [hitems] at rh rt
  have hlast : runFrom RecoveryBoundedNodeAddress.machine
      (RecoveryBoundedNodeAddress.budget constant.output.val firstIndex n W)
      (restart a.final RecoveryBoundedNodeAddress.machine.start)=some r := by
    change runFrom RecoveryBoundedNodeAddress.machine _ ⟨RecoveryBoundedNodeAddress.machine.start,a.final.heads,a.final.tapes⟩=some r
    rw [ah,atapes]
    exact hr
  have full:=Composition.run_join first RecoveryBoundedNodeAddress.machine _ _ _ a r ar hlast
  refine ⟨joinedReceipt a r,full,?_,rh,rt⟩
  change p.steps+1+r.steps ≤ budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W
  change p.steps ≤ RecoveryBoundedUniversalPrefix.budget wires.length left.output.val right.output.val firstIndex secondIndex limit W at ps
  change r.steps ≤ RecoveryBoundedNodeAddress.budget constant.output.val firstIndex n W at rs
  unfold budget
  omega

theorem budget_quartic (count left right constant firstIndex secondIndex limit addressCount W : ℕ)
    (hc : count ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hk : constant ≤ W)
    (hf : firstIndex ≤ W) (hs : secondIndex ≤ W) (hb : limit ≤ W) (ha : addressCount ≤ W) :
    budget count left right constant firstIndex secondIndex limit addressCount W ≤ 1800000000*(W+1)^4 := by
  have hp:=RecoveryBoundedUniversalPrefix.budget_quartic count left right firstIndex secondIndex limit W hc hl hr hf hs hb
  have hq:=RecoveryBoundedNodeAddress.budget_quartic constant firstIndex addressCount W hk hf ha
  unfold budget
  have h : 0 < (W+1)^4 := by positivity
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalAddress
