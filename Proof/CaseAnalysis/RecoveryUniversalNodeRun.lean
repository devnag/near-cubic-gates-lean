import Proof.CaseAnalysis.RecoveryUniversalNodeSeven

/-! One fixed machine executes the literal original compileUniversalNode.
The same shared description variables, graph suffix, output and full bank
are retained; allocation and the enclosing table remain separate producers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNode
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine RecoveryBoundedUniversalNodeSeven.machine RecoveryBoundedUniversalNodeTags.machine
def budget (count left right constant current firstIndex secondIndex tag limit addressCount W : ℕ):=
  RecoveryBoundedUniversalNodeSeven.budget count left right constant firstIndex secondIndex limit addressCount W+1+
    RecoveryBoundedUniversalNodeTags.budget constant current tag W

theorem node_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (W D L : ℕ)
    (wires : List (LiveWire b)) (out referenceTail addressTail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hn : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound)+
      OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hp : b.nodes.length+wires.length*(3*OuterPCPRecovery.boundedCircuitFieldLimit n bound+2)+
      3*OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ W)
    (hc : wires.length ≤ W) (ha : n ≤ W) (hD : 8388608*(W+1)^3 ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let limit:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let left:=compileFirstFieldSelect b row wires
    let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
    let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
    let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
    let source:=sourceWord (wires.map (fun w=>w.output.val))++referenceTail
    let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
    let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+limit)
    let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
    let seven:=cases b row address wires
    let original:=compileUniversalNode b row address wires
    let out7:=out++seven.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let A:=data firstIndex input.output.val (capacity W) D n limit wires.length L out7 source
      secondIndex tag left.output.val right.output.val constant.output.val (List.ofFn address++addressTail) n []
    let result:=out++original.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    left.final.nodes.length ≤ W → left.final.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W →
    right.final.nodes.length ≤ W → right.final.nodes.length+3*limit ≤ W →
    constant.final.nodes.length+n*(3*limit+1)+3*limit ≤ W → input.final.nodes.length ≤ W →
    seven.final.nodes.length+118 ≤ W → original.compiled.final.nodes.length ≤ W →
    ∃ r,runFrom machine (budget wires.length left.output.val right.output.val constant.output.val input.output.val
        firstIndex secondIndex tag limit n W)
      ⟨machine.start,heads out,data firstIndex b.nodes.length (capacity W) D 0 limit wires.length L out source
        secondIndex tag 0 0 0 (List.ofFn address++addressTail) n []⟩=some r ∧
      r.steps ≤ budget wires.length left.output.val right.output.val constant.output.val input.output.val
        firstIndex secondIndex tag limit n W ∧ r.final.heads=heads result ∧
      r.final.tapes=RecoveryBoundedNodeTagSelect.output (prepared A constant.output.val input.output.val tag (capacity W))
        original.compiled.output.val (capacity W) result := by
  let limit:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let left:=compileFirstFieldSelect b row wires
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let source:=sourceWord (wires.map (fun w=>w.output.val))++referenceTail
  let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
  let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+limit)
  let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
  let seven:=cases b row address wires
  let original:=compileUniversalNode b row address wires
  let selected:=compileFieldSelect seven.final tagEqualsExpr row seven.values
  let out7:=out++seven.extension.suffix.flatMap PCPPRequestNodeSchema.native
  dsimp only
  intro hleft hp2 hright hp3 hp4 hinput hseven horiginal
  change constant.final.nodes.length+n*(3*limit+1)+3*limit ≤ W at hp4
  change seven.final.nodes.length+118 ≤ W at hseven
  change original.compiled.final.nodes.length ≤ W at horiginal
  change firstIndex+limit ≤ W at hi
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedUniversalNodeSeven.seven_run b row address W D L wires out referenceTail addressTail
    hi hn hp hc ha hD hL hleft hp2 hright hp3 hp4 hinput
  have layout:=cases_layout b row address wires
  have meaning:=original_node b row address wires
  have hcount : seven.final.nodes.length=input.output.val+4:=layout.2.1
  have hk : constant.output.val ≤ W:=constant.output.isLt.le.trans (by omega)
  have hcurrent : input.output.val+3 ≤ W := by omega
  have htag : tag+6 ≤ W := by
    have he : tag+6=firstIndex := by simp only [tag,firstIndex,RecoveryBoundedNativeUnaryLoop.firstIndex,Nat.add_zero]
    rw [he]
    omega
  have hselected : selected.final.nodes.length ≤ W := by
    have he:=congrArg (fun x=>x.nodes.length) meaning.1
    change original.compiled.final.nodes.length=selected.final.nodes.length at he
    omega
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedUniversalNodeTags.tags_run seven.final row seven.values
    constant.output.val input.output.val firstIndex n limit wires.length W D L out7 source secondIndex
    left.output.val right.output.val (List.ofFn address++addressTail) n layout.1 hcount hk hcurrent (by omega) ha
    htag hseven hselected hD hL
  have qr' : runFrom RecoveryBoundedUniversalNodeTags.machine
      (RecoveryBoundedUniversalNodeTags.budget constant.output.val input.output.val tag W)
      (restart p.final RecoveryBoundedUniversalNodeTags.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join RecoveryBoundedUniversalNodeSeven.machine RecoveryBoundedUniversalNodeTags.machine _ _ _ p q pr qr'
  have hword : out7++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      out++original.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
    rw [meaning.2.2,List.flatMap_append]
    simp only [out7,List.append_assoc]
    rfl
  refine ⟨joinedReceipt p q,full,?_,?_,?_⟩
  · change p.steps+1+q.steps ≤ budget wires.length left.output.val right.output.val constant.output.val input.output.val
      firstIndex secondIndex tag limit n W
    change p.steps ≤ RecoveryBoundedUniversalNodeSeven.budget wires.length left.output.val right.output.val constant.output.val
      firstIndex secondIndex limit n W at ps
    change q.steps ≤ RecoveryBoundedUniversalNodeTags.budget constant.output.val input.output.val tag W at qs
    unfold budget
    omega
  · change q.final.heads=_
    rw [qh,hword]
  · change q.final.tapes=_
    change q.final.tapes=RecoveryBoundedNodeTagSelect.output
      (prepared (data firstIndex input.output.val (capacity W) D n limit wires.length L out7 source
        secondIndex tag left.output.val right.output.val constant.output.val (List.ofFn address++addressTail) n [])
        constant.output.val input.output.val tag (capacity W)) selected.output.val (capacity W)
      (out7++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native) at qt
    have hout : original.compiled.output.val=selected.output.val:=meaning.2.1
    rw [hword,←hout] at qt
    exact qt

theorem budget_quartic (count left right constant current firstIndex secondIndex tag limit addressCount W : ℕ)
    (hc : count ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hk : constant ≤ W) (hi : current ≤ W)
    (hf : firstIndex ≤ W) (hs : secondIndex ≤ W) (ht : tag ≤ W) (hb : limit ≤ W) (ha : addressCount ≤ W) (h5 : 5 ≤ W) :
    budget count left right constant current firstIndex secondIndex tag limit addressCount W ≤ 3000000000*(W+1)^4 := by
  have hp:=RecoveryBoundedUniversalNodeSeven.budget_quartic count left right constant firstIndex secondIndex limit addressCount W
    hc hl hr hk hf hs hb ha
  have hq:=RecoveryBoundedUniversalNodeTags.budget_quartic constant current tag W hk hi ht h5
  have hpos : 0 < (W+1)^4 := by positivity
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNode
