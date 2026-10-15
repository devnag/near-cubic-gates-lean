import Proof.SourceAssembly.SourceThresholdPhysical

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdCanonical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline CompilerSemantics
open CloseoutRowsOriginalClause (index negative)
open SourceAssemblyThresholdPhysical
noncomputable section

theorem card_eq {q : Nat} (S : Finset (Fin q)) :
    (normalizedThresholdParityCircuit S).top.support.card=S.card := by
  simp [normalizedThresholdParityCircuit,thresholdParityTopGate]

theorem index_val {q : Nat} (S : Finset (Fin q))
    (i : Fin (normalizedThresholdParityCircuit S).top.support.card) :
    (retainedTopIndex (normalizedThresholdParityCircuit S) i).val=i.val := by
  have hc : (Finset.univ : Finset (Fin S.card)).card=S.card := by simp
  have he := Finset.orderEmbOfFin_unique (s:=(Finset.univ : Finset (Fin S.card))) rfl
    (f:=Fin.cast hc) (fun _=>Finset.mem_univ _) (Fin.cast_strictMono hc)
  exact (congrArg Fin.val (congrFun he i)).symm

theorem ofFn_range {α : Type} (n : Nat) (f : Nat→α) :
    List.ofFn (fun i : Fin n=>f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem signed_eq (j : Nat) :
    intWord (if Even j then (1 : Int) else -1)=[Alternating.flag j,true,false,true] := by
  rw [Alternating.flag_odd]
  rcases Nat.even_or_odd j with he | ho
  · simp only [he,if_true,decide_eq_false (Nat.not_odd_iff_even.mpr he)];rfl
  · simp only [Nat.not_even_iff_odd.mpr ho,if_false,decide_eq_true ho];rfl

theorem top_eq {q : Nat} (S : Finset (Fin q)) :
    thresholdWord (nonStrictAsStrict (retainedTopGate (normalizedThresholdParityCircuit S)))=
      SourceAssemblyThresholdTop.payload S.card := by
  change natWord _ ++ (List.ofFn (fun i=>if Even (retainedTopIndex (normalizedThresholdParityCircuit S) i).val
      then (1 : Int) else -1)).flatMap intWord ++ intWord (1-1) = _
  simp only [index_val]
  rw [ofFn_range _ (fun j=>if Even j then (1 : Int) else -1),card_eq]
  simp only [List.flatMap_map]
  unfold SourceAssemblyThresholdTop.payload
  simp only [signed_eq]
  rfl

theorem bottom_eq {q : Nat} (S : Finset (Fin q))
    (i : Fin (normalizedThresholdParityCircuit S).top.support.card) :
    PacketProduction.bottomWord
      ((normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))=
      natWord q++weights (SourceAssemblySymmetricMeaning.bitmap S)++false::natWord i.val := by
  change CloseoutRowsCircuitBottom.nativeWord (thresholdParityBottomGate S _)=_
  rw [staircase_native,index_val]
  simp only [bottomWord,CloseoutRowsGateSupport.gateMembers,List.length_ofFn]
  rfl

theorem bottoms_eq {q : Nat} (S : Finset (Fin q)) :
    (List.ofFn (fun i=>(normalizedThresholdParityCircuit S).bottom
      (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (PacketProduction.bottomWord g))=
      CloseoutRowsTupleSeek.nativeWord (gates q S.card
        (SourceAssemblySymmetricMeaning.bitmap S)) := by
  rw [show (List.ofFn (fun i=>(normalizedThresholdParityCircuit S).bottom
      (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (PacketProduction.bottomWord g))=
      (List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
        frame (natWord q++weights (SourceAssemblySymmetricMeaning.bitmap S)++false::natWord i.val))).flatten by
    simp only [List.ofFn_eq_map,List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    rw [bottom_eq]]
  rw [ofFn_range _ (fun j=>frame (natWord q++weights (SourceAssemblySymmetricMeaning.bitmap S)++false::natWord j)),card_eq]
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map]
  rfl

theorem bytes_eq {q : Nat} (S : Finset (Fin q)) :
    native q S.card (SourceAssemblySymmetricMeaning.bitmap S)=
      PacketProduction.thrWord (normalizedThresholdParityCircuit S) := by
  unfold native SourceAssemblySymmetricAssemble.circuitWord
    SourceAssemblySymmetricAssemble.prefixWord
    PacketProduction.thrWord
  rw [gates_length,top_eq,bottoms_eq]
  have hw : (normalizedThresholdParityCircuit S).top.wireCount=S.card := card_eq S
  rw [hw]

theorem native_eq (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    native r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
      (SourceAssemblyThresholdCache.bits a r ci hk)=
      PacketProduction.thrWord
        (normalizedThresholdParityCircuit ((a.output r).systematicSupport
          ⟨index ((a.output r).clauses ci).left,hk⟩)) := by
  have hb : SourceAssemblySymmetricQuery.bitmap a r ci=
      ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblySymmetricMeaning.bitmap
          ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)) := by
    simp only [SourceAssemblySymmetricQuery.bitmap,
      SourceAssemblyLiteralSupport.value,dif_pos hk]
    rfl
  unfold SourceAssemblySymmetricHeaderQuery.count
  rw [hb,SourceAssemblySymmetricMeaning.count_eq]
  exact bytes_eq _

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C hk) (fun _=>0)
      (SourceAssemblyThresholdReady.input a r ci C) (finalHeads a r ci hk) A ∧
      A 207=PacketProduction.thrWord
        (normalizedThresholdParityCircuit ((a.output r).systematicSupport
          ⟨index ((a.output r).clauses ci).left,hk⟩)) ∧
      A 208=CloseoutRowsTupleSeek.supportWord (gates r.arity
        (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk)) := by
  obtain ⟨A,ha,hn,hs⟩:=SourceAssemblyThresholdPhysical.run a r ci C hc hk
  exact ⟨A,ha,hn.trans (native_eq a r ci hk),hs⟩

theorem native_head (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    finalHeads a r ci hk 207=(PacketProduction.thrWord
      (normalizedThresholdParityCircuit ((a.output r).systematicSupport
        ⟨index ((a.output r).clauses ci).left,hk⟩))).length := by
  change finalHeads a r ci hk (slots 5)=_
  rw [finalHeads,dockH_slot _ slots_inj _ _ 5]
  change (native r.arity (SourceAssemblySymmetricHeaderQuery.count a r ci)
    (SourceAssemblyThresholdCache.bits a r ci hk)).length=_
  rw [native_eq]

end
end SourceAssemblyThresholdCanonical
