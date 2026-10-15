import Proof.CaseAnalysis.RecoveryTagSelectorBank

/-! Name the literal original node's seven-case prefix and its five live
tag values. The final selector is exactly the existing field selector. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNode
open SourceInterfaces BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cases {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (prior : List (LiveWire b)) : CompiledWireList b :=
  let left:=compileFirstFieldSelect b row prior
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension prior)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let leftInput:=((left.live.lift right.extension).lift constant.extension).lift input.extension
  let rightInput:=(right.live.lift constant.extension).lift input.extension
  let negated:=compileNot input.final leftInput
  let conjunction:=compileAnd negated.final (leftInput.lift negated.extension) (rightInput.lift negated.extension)
  let disjunction:=compileOr conjunction.final
    ((leftInput.lift negated.extension).lift conjunction.extension)
    ((rightInput.lift negated.extension).lift conjunction.extension)
  { final:=disjunction.final
    extension:=left.extension.trans (right.extension.trans (constant.extension.trans (input.extension.trans
      (negated.extension.trans (conjunction.extension.trans disjunction.extension)))))
    values:=[constant.live.lift (input.extension.trans (negated.extension.trans (conjunction.extension.trans disjunction.extension))),
      input.live.lift (negated.extension.trans (conjunction.extension.trans disjunction.extension)),
      negated.live.lift (conjunction.extension.trans disjunction.extension),
      conjunction.live.lift disjunction.extension,disjunction.live] }

theorem cases_length {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (prior : List (LiveWire b)) :
    (cases b row address prior).values.length=5 := by rfl

theorem original_node {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (prior : List (LiveWire b)) :
    let seven:=cases b row address prior
    let selected:=compileFieldSelect seven.final tagEqualsExpr row seven.values
    let original:=compileUniversalNode b row address prior
    original.compiled.final=selected.final ∧ original.compiled.output.val=selected.output.val ∧
      original.compiled.extension.suffix=seven.extension.suffix++selected.extension.suffix := by
  exact ⟨rfl,rfl,rfl⟩

theorem cases_layout {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (prior : List (LiveWire b)) :
    let left:=compileFirstFieldSelect b row prior
    let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension prior)
    let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
    let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
    let seven:=cases b row address prior
    seven.values.map (fun w=>w.output.val)=
      [constant.output.val,input.output.val,input.output.val+1,input.output.val+2,input.output.val+3] ∧
    seven.final.nodes.length=input.output.val+4 ∧
    seven.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      left.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      right.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      constant.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      input.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      RecoveryBoundedUniversalGates.emitted left.output.val right.output.val := by
  dsimp only
  let left:=compileFirstFieldSelect b row prior
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension prior)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let leftInput:=((left.live.lift right.extension).lift constant.extension).lift input.extension
  let rightInput:=(right.live.lift constant.extension).lift input.extension
  let negated:=compileNot input.final leftInput
  let conjunction:=compileAnd negated.final (leftInput.lift negated.extension) (rightInput.lift negated.extension)
  let disjunction:=compileOr conjunction.final
    ((leftInput.lift negated.extension).lift conjunction.extension)
    ((rightInput.lift negated.extension).lift conjunction.extension)
  have hn:=RecoveryBoundedNodeAddress.expression_next constant.final (constantAddressSelectionExpr row address)
  change input.output.val+1=input.final.nodes.length at hn
  have hg:=RecoveryBoundedUniversalGates.original_three input.final leftInput rightInput
  dsimp only at hg
  refine ⟨?_,?_,?_⟩
  · change [constant.output.val,input.output.val,negated.output.val,conjunction.output.val,disjunction.output.val]=_
    exact RecoveryBoundedUniversalGates.original_tag_references input.final leftInput rightInput constant.output.val input.output.val hn
  · change disjunction.final.nodes.length=input.output.val+4
    rw [hg.2.2.2.1]
    omega
  · change (left.extension.trans (right.extension.trans (constant.extension.trans (input.extension.trans
        (negated.extension.trans (conjunction.extension.trans disjunction.extension)))))).suffix.flatMap PCPPRequestNodeSchema.native=_
    have hs:=congrArg (fun xs=>xs.flatMap PCPPRequestNodeSchema.native) hg.2.2.2.2
    change (negated.extension.trans (conjunction.extension.trans disjunction.extension)).suffix.flatMap
      PCPPRequestNodeSchema.native=([.not left.output.val,.and left.output.val right.output.val,
        .or left.output.val right.output.val] : List (BooleanNode (descriptionWidth n bound))).flatMap PCPPRequestNodeSchema.native at hs
    rw [←RecoveryBoundedUniversalGates.emitted_nodes] at hs
    simp only [BooleanDAGExtension.trans,List.flatMap_append] at hs
    simp only [BooleanDAGExtension.trans,List.flatMap_append,List.append_assoc,hs]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNode
