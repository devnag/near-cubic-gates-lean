import Proof.CaseAnalysis.RecoveryAddressJoin

/-! The complete run returns the literal original address-expression graph
suffix and live output address, alongside every retained bank field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_graph {n : ℕ} (index base C D value limit total pos : ℕ)
    (out source pre : List Bool) (refs : List ℕ) :
    (reverseOutput index base C D value limit total pos out source pre refs).tapes 20=
      out++(foldNodes (n:=n) false base refs.reverse).flatMap PCPPRequestNodeSchema.native := by
  unfold reverseOutput
  change (RecoveryFocus.config foldSlots _ _ _).tapes (foldSlots 20)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective]
  change ZeroPadding.pad 0 (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩).out=_
  rw [ZeroPadding.pad_zero]
  exact (RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=n) false refs.reverse ⟨base,0,0,out⟩).2

theorem output_counter (index base C D value limit total pos : ℕ)
    (out source pre : List Bool) (refs : List ℕ) :
    (reverseOutput index base C D value limit total pos out source pre refs).tapes 25=
      List.replicate (base+refs.length) true := by
  unfold reverseOutput
  change (RecoveryFocus.config foldSlots _ _ _).tapes (foldSlots 25)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots fold_injective]
  change ZeroPadding.pad 0 (List.replicate
    (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩).acc true)=_
  rw [ZeroPadding.pad_zero,(RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=0) false refs.reverse ⟨base,0,0,out⟩).1,
    List.length_reverse]

theorem original_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (bits out skipped tail pre : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))).final.nodes.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (RecoveryBoundedSelectorLoop.capacity W) ≤ D) :
    let compiled:=compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))
    let source:=skipped++bits++tail
    let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock bits
    let refs:=references b.nodes.length (items row start limit hblock 0 bits)
    ∃ r,runFrom machine (budget bits.length W)
      (entry (n:=n) row start limit W D b.nodes.length bits.length out skipped source pre)=some r ∧
      r.steps ≤ budget bits.length W ∧
      r.final.tapes 20=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate compiled.output.val true ∧
      r.final.heads=(reverseOutput (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (RecoveryBoundedSelectorLoop.capacity W) D bits.length limit bits.length a.skipped.length
        (a.out++RecoveryBoundedSelectorFinish.falseBits) source pre refs).heads ∧
      r.final.tapes=(reverseOutput (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        a.position (RecoveryBoundedSelectorLoop.capacity W) D bits.length limit bits.length a.skipped.length
        (a.out++RecoveryBoundedSelectorFinish.falseBits) source pre refs).tapes := by
  let xs:=items row start limit hblock 0 bits
  let compiled:=compileExpr b (BoolExpr.any xs)
  let a:=(initial b.nodes.length out skipped pre).iterate row start limit hblock bits
  let refs:=references b.nodes.length xs
  have hlen : xs.length=bits.length:=items_length row start limit 0 hblock bits
  have hrlen : refs.length=bits.length := by rw [RecoveryBoundedAddress.references_length,hlen]
  have hf : b.nodes.length+prefixSize xs+bits.length ≤ W := by
    rw [compileExpr_length,any_count,items_length] at hg
    dsimp only [xs]
    omega
  obtain ⟨r,hr,rs,rh,rt⟩:=join_run b row start limit W D hblock bits out skipped tail pre hi hp hf hc hD
  have hs:=iterate_schedule row start limit hblock bits (initial b.nodes.length out skipped pre)
  have haPos : a.position=b.nodes.length+prefixSize xs:=hs.1
  have haOut : a.out=out++(prefixNodes b.nodes.length xs).flatMap PCPPRequestNodeSchema.native:=hs.2.2.1
  have hnodes : compiled.extension.suffix=prefixNodes b.nodes.length xs++[BooleanNode.const false]++
      foldNodes false (b.nodes.length+prefixSize xs) refs.reverse:=any_suffix b xs
  have hout : compiled.output.val=b.nodes.length+prefixSize xs+bits.length := by
    rw [compileExpr_output,any_count,hlen]
    omega
  refine ⟨r,hr,rs,?_,?_,rh,rt⟩
  · rw [rt,output_graph (n:=descriptionWidth n bound),haOut,haPos,hnodes]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    rfl
  · rw [rt,output_counter,haPos,hrlen,hout]

theorem items_ofFn {n bound m : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bits : Fin m→Bool) :
    items row start limit hblock value (List.ofFn bits)=
      List.ofFn (fun i=>if bits i then unaryEqualsExpr row start limit (value+i.val) hblock else .const false) := by
  induction m generalizing value with
  | zero=>simp only [List.ofFn_zero,items]
  | succ m ih=>
    rw [List.ofFn_succ,items,ih]
    conv_rhs=>rw [List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1]

theorem original_address {n bound : ℕ} (row : Fin (bound+1)) (address : BitInput n)
    (hblock : 6+OuterPCPRecovery.boundedCircuitFieldLimit n bound ≤ rowWidth n bound) :
    BoolExpr.any (items row 6 (OuterPCPRecovery.boundedCircuitFieldLimit n bound) hblock 0 (List.ofFn address))=
      constantAddressSelectionExpr row address := by
  rw [items_ofFn]
  simp only [Nat.zero_add]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
