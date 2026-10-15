import Proof.CaseAnalysis.RecoverySelectorJoinRun

/-! The complete selector run appends the literal original compileFieldSelect
suffix and returns its actual live output address. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedUniversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem endBank_graph {n : ℕ} (index base C D value limit total pos : ℕ)
    (out source pre : List Bool) (refs : List ℕ) :
    (endBank index base C D value limit total pos out source pre refs).tapes 20=
      out++(foldNodes (n:=n) false base refs.reverse).flatMap PCPPRequestNodeSchema.native := by
  unfold endBank
  change (RecoveryFocus.config foldSlots _ _ _).tapes (foldSlots 20)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective]
  change ZeroPadding.pad 0 (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩).out=_
  rw [ZeroPadding.pad_zero]
  exact (RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=n) false refs.reverse ⟨base,0,0,out⟩).2

theorem endBank_counter (index base C D value limit total pos : ℕ)
    (out source pre : List Bool) (refs : List ℕ) :
    (endBank index base C D value limit total pos out source pre refs).tapes 25=
      List.replicate (base+refs.length) true := by
  unfold endBank
  change (RecoveryFocus.config foldSlots _ _ _).tapes (foldSlots 25)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective]
  change ZeroPadding.pad 0 (List.replicate
    (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩).acc true)=_
  rw [ZeroPadding.pad_zero,(RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=0) false refs.reverse ⟨base,0,0,out⟩).1,
    List.length_reverse]

theorem original_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out skipped tail pre : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hg : (compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires).final.nodes.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) :
    let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
    let raw:=wires.map (fun w=>w.output.val)
    let source:=skipped++sourceWord raw++tail
    let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock raw
    let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
    ∃ r,runFrom machine (budget wires.length W)
      (entry (n:=n) row start limit W D b.nodes.length wires.length out skipped source pre)=some r ∧
      r.steps ≤ budget wires.length W ∧
      r.final.tapes 20=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate compiled.output.val true ∧
      r.final.heads=(endBank (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (capacity W) D wires.length limit wires.length a.skipped.length (a.out++falseBits) source pre refs).heads ∧
      r.final.tapes=(endBank (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (capacity W) D wires.length limit wires.length a.skipped.length (a.out++falseBits) source pre refs).tapes := by
  let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
  let raw:=wires.map (fun w=>w.output.val)
  let xs:=fieldItems row start limit hblock 0 raw
  let source:=skipped++sourceWord raw++tail
  let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock raw
  let refs:=RecoveryBoundedUniversal.references b.nodes.length xs
  have hchoices : xs=choices (fieldChoices (fun row value=>unaryEqualsExpr row start limit value hblock) row wires) :=
    fieldItems_choices b row start limit hblock wires
  have hlen : xs.length=wires.length := by simp only [xs,fieldItems_length,raw,List.length_map]
  have hrlen : refs.length=wires.length := by rw [RecoveryBoundedUniversal.references_length,hlen]
  have hf : b.nodes.length+prefixSize xs+wires.length ≤ W := by
    change (compileGuardedAny b (fieldChoices (fun row value=>unaryEqualsExpr row start limit value hblock) row wires)).final.nodes.length ≤ W at hg
    rw [compileGuardedAny_length,←hchoices,guardCount_prefix,hlen] at hg
    omega
  obtain ⟨r,hr,rs,rh,rt⟩:=join_run b row start limit W D hblock wires out skipped tail pre hi hp hf hc hD
  have hs:=iterate_schedule row start limit hblock raw (initial b.nodes.length out skipped pre)
  have haPos : a.position=b.nodes.length+prefixSize xs := hs.1
  have haOut : a.out=out++(prefixNodes b.nodes.length xs).flatMap PCPPRequestNodeSchema.native := hs.2.2.1
  have hnodes : compiled.extension.suffix=prefixNodes b.nodes.length xs++[BooleanNode.const false]++
      foldNodes false (b.nodes.length+prefixSize xs) refs.reverse := by
    rw [field_select_suffix,←hchoices]
  have hout : compiled.output.val=b.nodes.length+prefixSize xs+wires.length := by
    change (compileGuardedAny b (fieldChoices (fun row value=>unaryEqualsExpr row start limit value hblock) row wires)).output.val=_
    rw [compileGuardedAny_output,←hchoices,guardCount_prefix,hlen]
    omega
  refine ⟨r,hr,rs,?_,?_,rh,rt⟩
  · rw [rt,endBank_graph (n:=descriptionWidth n bound),haOut,haPos,hnodes]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    rfl
  · rw [rt,endBank_counter,haPos,hrlen,hout]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
