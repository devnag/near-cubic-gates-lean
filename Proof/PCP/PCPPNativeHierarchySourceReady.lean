import Proof.PCP.PCPPNativeHierarchyNodesReady

/-! Original hierarchy input to the single selected faithful source cache.
The separated hierarchy bound is retained in the actual execution fuel. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def originalBudget (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :=
  PCPPNativeClauseDescriptorConsumer.sourceBudget a
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)

theorem original_run (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let request:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    ∃ result,run (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (originalBudget source a H Cpad hpad r oracle)
      (input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))=some result ∧
      result.steps≤originalBudget source a H Cpad hpad r oracle ∧
      (∀ j : Fin 19,result.final.tapes (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,result.final.heads (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=List.replicate request.circuit.size true ∧
      result.final.heads (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=0 := by
  obtain ⟨native,hr,_,hout,hhead,_,hindex,_,hsize,_,hwidth⟩ :=
    PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hr' : run (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)
      (PCPPNativeHierarchyNodes.input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))=some native := by
    rw [PCPPNativeHierarchyNodes.input_word]
    exact hr
  have hd:=PCPPNativeHierarchyNodes.scalar_distinct source k
  exact PCPPNativeClauseDescriptorConsumer.source_run a
    (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.slots source k 177) (PCPPNativeHierarchyNodes.slots source k 72)
    (PCPPNativeHierarchyNodes.slots source k 91) (PCPPNativeHierarchyNodes.slots source k 89)
    hd.1 hd.2.1 hd.2.2 (PCPPNativeHierarchyNodes.forward source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)
    (PCPPNativeHierarchyNodes.input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))
    native hr' hout hhead hwidth hsize hindex

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
