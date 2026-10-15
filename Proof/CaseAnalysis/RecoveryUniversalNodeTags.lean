import Proof.CaseAnalysis.RecoveryUniversalNodeBank

/-! Execute the entire original node's tag stage: physical five-reference
packet, paid rewind, actual index preparation and original shared selector. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeTags
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepare:=Composition.machine RecoveryBoundedNodeTagPacket.machine RecoveryBoundedNodeTagPrepare.machine
noncomputable def machine:=Composition.machine prepare RecoveryBoundedNodeTagSelect.machine
def budget (constant current tag W : ℕ):=
  RecoveryBoundedTagPacketReset.budget constant current (capacity W)+1+
    RecoveryBoundedTagPrepare.budget tag (capacity W)+1+RecoveryBoundedSelectorReuse.resetBudget 5 W

theorem tags_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (wires : List (LiveWire b)) (constant current index value limit total W D L : ℕ)
    (out source : List Bool) (secondIndex left right : ℕ) (address : List Bool) (count : ℕ)
    (hraw : wires.map (fun w=>w.output.val)=[constant,current,current+1,current+2,current+3])
    (hb : b.nodes.length=current+4) (hk : constant ≤ W) (hc : current+3 ≤ W)
    (hi : index ≤ W) (hv : value ≤ W)
    (ht : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0+6 ≤ W)
    (hp : b.nodes.length+118 ≤ W)
    (hg : (compileFieldSelect b tagEqualsExpr row wires).final.nodes.length ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
    let A:=data index current (capacity W) D value limit total L out source secondIndex tag left right constant address count []
    let compiled:=compileFieldSelect b tagEqualsExpr row wires
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (budget constant current tag W) ⟨machine.start,heads out,A⟩=some r ∧
      r.steps ≤ budget constant current tag W ∧ r.final.heads=heads result ∧
      r.final.tapes=RecoveryBoundedNodeTagSelect.output (prepared A constant current tag (capacity W))
        compiled.output.val (capacity W) result := by
  let tag:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 0
  let C:=capacity W
  let A:=data index current C D value limit total L out source secondIndex tag left right constant address count []
  have hkw : 2*constant+1 ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have hcw : 2*(current+3)+1 ≤ C :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1).trans (by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)])
  have hiw : index ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have hvw : value ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have htw : tag+1 ≤ C := by dsimp [C,capacity];dsimp [tag] at *;nlinarith [Nat.zero_le (W^2)]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedNodeTagPacket.packet_run (heads out) A constant current C D
    (packet_heads out) (packet_tapes index current C D value limit total L out source secondIndex tag left right constant address count)
    hkw hcw (RecoveryBoundedTagPacket.budget_log constant current W D hk (by omega) hD)
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedNodeTagPrepare.prepare_run (heads out)
    (RecoveryBoundedNodeTagPacket.output A constant current C) tag index value C (prepare_heads out)
    (prepare_tapes index current C D value limit total L out source secondIndex tag left right constant address count) hiw hvw htw
  have qr' : runFrom RecoveryBoundedNodeTagPrepare.machine (RecoveryBoundedTagPrepare.budget tag C)
      (restart p.final RecoveryBoundedNodeTagPrepare.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have ready:=Composition.run_join RecoveryBoundedNodeTagPacket.machine RecoveryBoundedNodeTagPrepare.machine _ _ _ p q pr qr'
  have hw : wires.length=5 := by
    have h:=congrArg List.length hraw
    simpa only [List.length_map,List.length_cons,List.length_nil] using h
  let tail:=List.replicate (C-(RecoveryBoundedTagPacket.word constant current).length) false
  have hs : ZeroPadding.pad C (RecoveryBoundedTagPacket.word constant current)=
      sourceWord (wires.map (fun w=>w.output.val))++tail := by
    rw [hraw,←RecoveryBoundedTagPacket.word_original]
    rfl
  have hA : ∀ j,prepared A constant current tag C (RecoveryBoundedNodeTagSelect.slots j)=
      RecoveryBoundedSelectorReuse.finalData tag b.nodes.length C D 0 6 5 L out
        (sourceWord (wires.map (fun w=>w.output.val))++tail) j := by
    intro j
    have h:=selector_tapes index current C D value limit total L out source secondIndex tag left right constant address count j
    simpa only [←hb,hs] using h
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedNodeTagSelect.selector_run b row W D L wires hw out tail
    (heads out) (prepared A constant current tag C) (selector_heads out) hA ht hp hg hD hL
  have rr' : runFrom RecoveryBoundedNodeTagSelect.machine (RecoveryBoundedSelectorReuse.resetBudget 5 W)
      (restart (joinedReceipt p q).final RecoveryBoundedNodeTagSelect.machine.start)=some r := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some r
    rw [qh,qt]
    exact rr
  have full:=Composition.run_join prepare RecoveryBoundedNodeTagSelect.machine _ _ _ (joinedReceipt p q) r ready rr'
  refine ⟨joinedReceipt (joinedReceipt p q) r,full,?_,?_,rt⟩
  · change p.steps+1+q.steps+1+r.steps ≤ budget constant current tag W
    change p.steps ≤ RecoveryBoundedTagPacketReset.budget constant current (capacity W) at ps
    change q.steps=RecoveryBoundedTagPrepare.budget tag (capacity W) at qs
    unfold budget
    omega
  · change r.final.heads=_
    rw [rh,selected_heads]

theorem budget_quartic (constant current tag W : ℕ) (hk : constant ≤ W) (hc : current ≤ W) (ht : tag ≤ W) (h5 : 5 ≤ W) :
    budget constant current tag W ≤ 600000000*(W+1)^4 := by
  have hp:=RecoveryBoundedTagPacketReset.budget_quadratic constant current W hk hc
  have ht:=RecoveryBoundedNodeTagPrepare.budget_quadratic tag W ht
  have hs:=RecoveryBoundedSelectorFinish.reset_budget_quartic 5 W h5
  change RecoveryBoundedSelectorReuse.resetBudget 5 W ≤ 536871202*(W+1)^4 at hs
  unfold budget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeTags
