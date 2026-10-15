import Proof.CaseAnalysis.RecoveryUniversalNodeTags

/-! Execute the literal original first seven universal-node operations in
one retained bank, immediately before its paid five-tag stage. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeSeven
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def localMachine:=Composition.machine RecoveryBoundedUniversalAddress.machine RecoveryBoundedNodeAddress.gates
noncomputable def machine:=TapeEmbedding.machine 4 localMachine
def budget (count left right constant firstIndex secondIndex limit addressCount W : ℕ):=
  RecoveryBoundedUniversalAddress.budget count left right constant firstIndex secondIndex limit addressCount W+1+
    RecoveryBoundedUniversalGates.budget left right (capacity W)

theorem seven_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
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
    let result:=out++(RecoveryBoundedUniversalNode.cases b row address wires).extension.suffix.flatMap PCPPRequestNodeSchema.native
    left.final.nodes.length ≤ W → left.final.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W →
    right.final.nodes.length ≤ W → right.final.nodes.length+3*limit ≤ W →
    constant.final.nodes.length+n*(3*limit+1)+3*limit ≤ W → input.final.nodes.length ≤ W →
    ∃ r,runFrom machine (budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W)
      ⟨machine.start,heads out,data firstIndex b.nodes.length (capacity W) D 0 limit wires.length L out source
        secondIndex tag 0 0 0 (List.ofFn address++addressTail) n []⟩=some r ∧
      r.steps ≤ budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W ∧
      r.final.heads=heads result ∧
      r.final.tapes=data firstIndex input.output.val (capacity W) D n limit wires.length L result source
        secondIndex tag left.output.val right.output.val constant.output.val (List.ofFn address++addressTail) n [] := by
  let limit:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let left:=compileFirstFieldSelect b row wires
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let source:=sourceWord (wires.map (fun w=>w.output.val))++referenceTail
  let firstIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6
  let secondIndex:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row (6+limit)
  let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
  let out4:=out++left.extension.suffix.flatMap PCPPRequestNodeSchema.native++right.extension.suffix.flatMap PCPPRequestNodeSchema.native++
    constant.extension.suffix.flatMap PCPPRequestNodeSchema.native++input.extension.suffix.flatMap PCPPRequestNodeSchema.native
  dsimp only
  intro hleft hp2 hright hp3 hp4 hinput
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedUniversalAddress.original_prefix_run b row address W D L wires out referenceTail addressTail
    hi hn hp hc ha hD hL hleft hp2 hright hp3 hp4 hinput
  have hl : left.output.val ≤ W:=left.output.isLt.le.trans hleft
  have hr : right.output.val ≤ W:=right.output.isLt.le.trans hright
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedNodeAddress.gates_run firstIndex input.output.val (capacity W) D n limit wires.length L
    left.output.val right.output.val W out4 source secondIndex
    (ZeroPadding.pad (capacity W) (List.replicate constant.output.val true)) (List.ofFn address++addressTail) n hl hr (by rfl)
  have qr' : runFrom RecoveryBoundedNodeAddress.gates (RecoveryBoundedUniversalGates.budget left.output.val right.output.val (capacity W))
      (restart p.final RecoveryBoundedNodeAddress.gates.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join RecoveryBoundedUniversalAddress.machine RecoveryBoundedNodeAddress.gates _ _ _ p q pr qr'
  let et:=extraData (capacity W) tag []
  let r:=TapeEmbedding.receipt extraHeads et (joinedReceipt p q)
  have rr:=TapeEmbedding.run_embed localMachine extraHeads et _ _ (joinedReceipt p q) full
  have layout:=RecoveryBoundedUniversalNode.cases_layout b row address wires
  have hword : out4++RecoveryBoundedUniversalGates.emitted left.output.val right.output.val=
      out++(RecoveryBoundedUniversalNode.cases b row address wires).extension.suffix.flatMap PCPPRequestNodeSchema.native := by
    rw [layout.2.2]
    simp only [out4,List.append_assoc]
    rfl
  refine ⟨r,rr,?_,?_,?_⟩
  · change p.steps+1+q.steps ≤ budget wires.length left.output.val right.output.val constant.output.val firstIndex secondIndex limit n W
    change p.steps ≤ RecoveryBoundedUniversalAddress.budget wires.length left.output.val right.output.val constant.output.val
      firstIndex secondIndex limit n W at ps
    unfold budget
    omega
  · change Fin.addCases (m:=51) (n:=4) (motive:=fun _=>ℕ) q.final.heads extraHeads=_
    rw [qh,hword]
    rfl
  · change Fin.addCases (m:=51) (n:=4) (motive:=fun _=>List Bool) q.final.tapes et=_
    rw [qt,hword]
    rfl

theorem budget_quartic (count left right constant firstIndex secondIndex limit addressCount W : ℕ)
    (hc : count ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hk : constant ≤ W)
    (hf : firstIndex ≤ W) (hs : secondIndex ≤ W) (hb : limit ≤ W) (ha : addressCount ≤ W) :
    budget count left right constant firstIndex secondIndex limit addressCount W ≤ 2000000000*(W+1)^4 := by
  have hp:=RecoveryBoundedUniversalAddress.budget_quartic count left right constant firstIndex secondIndex limit addressCount W
    hc hl hr hk hf hs hb ha
  have hg:=RecoveryBoundedUniversalGates.budget_bound left right W (capacity W) hl hr (by rfl)
  unfold budget capacity at *
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeSeven
