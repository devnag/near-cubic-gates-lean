import Proof.PCP.PCPPNativeHierarchyEnvelope

/-! Closed ordinary execution of the original hierarchy/native/source/cache
constructor with source-fixed input/log exponents and original oracle cost. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem polynomial_run (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let request:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    ∃ result,run (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (envelope source a H Cpad r oracle)
      (input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))=some result ∧
      result.steps≤envelope source a H Cpad r oracle ∧
      (∀ j : Fin 19,result.final.tapes (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,result.final.heads (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=List.replicate request.circuit.size true ∧
      result.final.heads (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=0 := by
  obtain ⟨result,hr,hs,rest⟩:=original_run source a H Cpad hcoeff hpad r oracle
  have hb:=original_budget_bound source a H Cpad hcoeff hpad r oracle
  have more:=run_moreFuel (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    (envelope source a H Cpad r oracle-originalBudget source a H Cpad hpad r oracle) _ result hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨result,more,hs.trans hb,rest⟩

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
