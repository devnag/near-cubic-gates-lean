import Proof.CaseAnalysis.RecoverySelectorPairBank

/-! The reusable, paid-rewind selector returns the literal original graph
suffix and live output, in the exact bank consumed by the next selector. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish RecoveryBoundedUniversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_next {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) :
    let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
    compiled.output.val+1=compiled.final.nodes.length := by
  change (compileGuardedAny b _).output.val+1=(compileGuardedAny b _).final.nodes.length
  rw [compileGuardedAny_output,compileGuardedAny_length,guardCount_prefix]
  omega

theorem reset_original_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D L : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hg : (compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires).final.nodes.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) (hL : logCapacity W ≤ L) :
    let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
    let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (resetBudget wires.length W)
      (entry (n:=n) row start limit W D L b.nodes.length wires.length out source)=some r ∧
      r.steps ≤ resetBudget wires.length W ∧ r.final.heads=finalHeads result ∧
      r.final.tapes=finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val (capacity W) D wires.length limit wires.length L result source := by
  let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
  let raw:=wires.map (fun w=>w.output.val)
  let xs:=fieldItems row start limit hblock 0 raw
  let source:=sourceWord raw++tail
  let a:=(initial b.nodes.length out [] []).iterate row start limit hblock raw
  let refs:=RecoveryBoundedUniversal.references b.nodes.length xs
  let f:=folded a.position (a.out++falseBits) refs
  have hchoices : xs=choices (fieldChoices (fun row value=>unaryEqualsExpr row start limit value hblock) row wires) :=
    fieldItems_choices b row start limit hblock wires
  have hlen : xs.length=wires.length := by simp only [xs,fieldItems_length,raw,List.length_map]
  have hf : b.nodes.length+prefixSize xs+wires.length ≤ W := by
    change (compileGuardedAny b _).final.nodes.length ≤ W at hg
    rw [compileGuardedAny_length,←hchoices,guardCount_prefix,hlen] at hg
    omega
  have hC : 1 ≤ capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨old,_,_,oldGraph,oldOutput,_,oldData⟩:=
    original_run b row start limit W D hblock wires out [] tail [] hi hp hg hc hD
  have hn:=endBank_tapes (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position (capacity W) D wires.length limit wires.length a.skipped.length
    (a.out++falseBits) source [] refs hC
  have hd : old.final.tapes=(endBank (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      a.position (capacity W) D wires.length limit wires.length a.skipped.length
      (a.out++falseBits) source [] refs).tapes := by
    simpa only [List.nil_append] using oldData
  rw [hd,hn] at oldGraph oldOutput
  change f.out=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native at oldGraph
  change List.replicate f.acc true=List.replicate compiled.output.val true at oldOutput
  have ha : f.acc=compiled.output.val := by
    have h:=congrArg List.length oldOutput
    simpa only [List.length_replicate] using h
  obtain ⟨r,hr,rs,rh,rt⟩:=reset_run b row start limit W D L hblock wires out tail hi hp hf hc hD hL
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh,oldGraph]
  · rw [rt,oldGraph,ha]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
