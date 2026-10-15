import Proof.SourceAssembly.SourceSymmetricPhysical

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricCanonical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline
open CloseoutRowsOriginalClause (index negative)
open SourceAssemblySymmetricPhysical
noncomputable section

theorem top_eq {q : Nat} (S : Finset (Fin q)) :
    SourceAssemblySymmetricTop.table S.card=List.ofFn (normalizedParityCircuit S).top := by
  apply congrArg List.ofFn
  funext i
  exact Alternating.flag_odd i.val

theorem bytes_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    SourceAssemblySymmetricAssemble.circuitWord
      (SourceAssemblySymmetricTop.table
        (SourceAssemblySymmetricScan.selected (ZeroPadding.pad C
          (SourceAssemblySymmetricMeaning.bitmap S)) q).length)
      (gates q (ZeroPadding.pad C (SourceAssemblySymmetricMeaning.bitmap S)))=
        PacketProduction.symWord (normalizedParityCircuit S) := by
  unfold SourceAssemblySymmetricAssemble.circuitWord
    SourceAssemblySymmetricAssemble.prefixWord
  rw [gates_length,SourceAssemblySymmetricMeaning.count_eq,top_eq,
    gates_native,SourceAssemblySymmetricMeaning.native_eq]
  rfl

theorem native_eq (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    native a r ci=PacketProduction.symWord
      (normalizedParityCircuit ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)) := by
  have hb : SourceAssemblySymmetricQuery.bitmap a r ci=
      ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblySymmetricMeaning.bitmap
          ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)) := by
    simp only [SourceAssemblySymmetricQuery.bitmap,
      SourceAssemblyLiteralSupport.value,dif_pos hk]
    rfl
  unfold native top selectedGates SourceAssemblySymmetricHeaderQuery.count
  rw [hb]
  exact bytes_eq _ _

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0)
      (SourceAssemblySymmetricReset.input a r ci C) (finalHeads a r ci) A ∧
      A 167=PacketProduction.symWord
        (normalizedParityCircuit ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)) ∧
      A 168=CloseoutRowsTupleSeek.supportWord (selectedGates a r ci) := by
  obtain ⟨A,ha,hn,hs⟩:=SourceAssemblySymmetricPhysical.run a r ci C hc
  exact ⟨A,ha,hn.trans (native_eq a r ci hk),hs⟩

end
end SourceAssemblySymmetricCanonical
