import Proof.CaseAnalysis.CaseTwoNativeSourceDock
import Proof.CaseAnalysis.CaseTwoRequestDescriptor

/-! The original hierarchy word and converted canonical circuit feed the
same projection substitution and faithful PCPP request, with the honest input
retained inside the actual run. No second native or source construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OriginalSource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem distinct (k : ℕ) : RequestDescriptor.frameSlot source k≠RequestDescriptor.sizeSlot source k ∧
    RequestDescriptor.frameSlot source k≠RequestDescriptor.aritySlot source k ∧
    RequestDescriptor.sizeSlot source k≠RequestDescriptor.aritySlot source k:=by
  have vals : (RequestDescriptor.frameSlot source k).val=PCPPNativeHierarchyNodes.tapes source k+71 ∧
      (RequestDescriptor.sizeSlot source k).val=PCPPNativeHierarchyNodes.tapes source k+31 ∧
      (RequestDescriptor.aritySlot source k).val=PCPPNativeHierarchyNodes.tapes source k+14:=by
    simp [RequestDescriptor.frameSlot,RequestDescriptor.sizeSlot,RequestDescriptor.aritySlot,
      RequestDescriptor.base,PCPPNativeClauseDescriptorConsumer.tapes,PCPPNativeClauseDescriptorConsumer.slots,
      PCPPNativeFrame.old,Nat.add_assoc]
  refine ⟨?_,?_,?_⟩
  all_goals intro he;have hv:=congrArg Fin.val he;omega
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool):=
  NativeSourceDock.machine a (RequestDescriptor.machine source a k CH Cpad code)
    (RequestDescriptor.frameSlot source k) (RequestDescriptor.sizeSlot source k) (RequestDescriptor.aritySlot source k)
def tapes (a : PointwisePCPPAlgorithm) (k : ℕ):=NativeSourceDock.tapes a (RequestDescriptor.tapes source k)
def input (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy oracle : List Bool):=
  NativeSourceDock.input a (RequestDescriptor.input source k hierarchy oracle)
def slots (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (RequestSource.tapes a)):=
  NativeSourceDock.slots a (RequestDescriptor.frameSlot source k) (RequestDescriptor.sizeSlot source k)
    (RequestDescriptor.aritySlot source k) j
def budget (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : ℕ) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)):=
  let request:=PCPPRequestBoundary.request a
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
  RequestDescriptor.budget source a H Cpad hpad r oracle+1+RequestSource.budget a request

theorem source_run (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let request:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    ∃ result,run (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source a H Cpad hpad r oracle)
      (input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))=some result ∧
      result.steps≤budget source a H Cpad hpad r oracle ∧
      (∀ j,result.final.tapes (slots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,result.final.heads (slots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (slots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=frame (pcppInput request) ∧
      result.final.heads (slots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=0:=by
  obtain ⟨out,hr,hf,ha,hs⟩:=RequestDescriptor.descriptor_run source a H Cpad hcoeff hpad r oracle
  exact NativeSourceDock.source_run a (RequestDescriptor.machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (RequestDescriptor.frameSlot source k) (RequestDescriptor.sizeSlot source k) (RequestDescriptor.aritySlot source k)
    (distinct source k).1 (distinct source k).2.1 (distinct source k).2.2 _ _ _ out hr hf hs ha

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OriginalSource
