import Proof.PCP.PCPPNativeHierarchyNodesReady
import Proof.PCP.PCPPNativeFrame

/-! The original hierarchy/substitution producer emits the exact native
descriptor of the one faithful request. Actual request arity and size are
retained through paid framing; no semantic dimensions are supplied free. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestDescriptor
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def width (k : ℕ):=PCPPNativeHierarchyNodes.slots source k 72
def size (k : ℕ):=PCPPNativeHierarchyNodes.slots source k 91
def index (k : ℕ):=PCPPNativeHierarchyNodes.slots source k 89
def target (k : ℕ):=PCPPNativeClauseDescriptorConsumer.slots (width source k) (size source k) (index source k) 26
def native (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool):=
  PCPPNativeClauseDescriptorConsumer.machine a (PCPPNativeHierarchyNodes.machine source k CH Cpad code)
    (PCPPNativeHierarchyNodes.slots source k 177) (width source k) (size source k) (index source k)
def base (k : ℕ):=PCPPNativeClauseDescriptorConsumer.tapes (PCPPNativeHierarchyNodes.tapes source k)
def tapes (k : ℕ):=(base source k+2)+2
def frameSlot (k : ℕ) : Fin (tapes source k):=(0 : Fin 2).natAdd (base source k+2)
def aritySlot (k : ℕ):=PCPPNativeFrame.old
  (PCPPNativeClauseDescriptorConsumer.slots (width source k) (size source k) (index source k) 10)
def sizeSlot (k : ℕ):=PCPPNativeFrame.old
  (PCPPNativeClauseDescriptorConsumer.slots (width source k) (size source k) (index source k) 27)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool):=
  AppendOutputFrame.machine (native source a k CH Cpad code) (target source k)
def input (k : ℕ) (hierarchy oracle : List Bool):=
  AppendOutputFrame.input (PCPPNativeClauseDescriptorConsumer.input
    (PCPPNativeHierarchyNodes.input source k hierarchy oracle))
def budget (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad : ℕ) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)):=
  let c:=PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
  2*PCPPNativeClauseDescriptorConsumer.budget a c (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)+
    4*(PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit).length+7

theorem descriptor_run (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let request:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    ∃ out,ClockJoin.ReadyRun (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source a H Cpad hpad r oracle)
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) out ∧
      out (frameSlot source k)=frame (PCPPNative.descriptor request.circuit) ∧
      out (aritySlot source k)=List.replicate request.arity true ∧
      out (sizeSlot source k)=List.replicate request.circuit.size true:=by
  let request:=PCPPRequestBoundary.request a
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
  obtain ⟨nodes,hn,_,nt,nh,_,ni,_,ns,_,nw⟩:=PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hn' : run (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)
      (PCPPNativeHierarchyNodes.input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle))=some nodes:=by
    rw [PCPPNativeHierarchyNodes.input_word]
    exact hn
  have hd:=PCPPNativeHierarchyNodes.scalar_distinct source k
  obtain ⟨nativeResult,hr,hs,ht,hh,_,ha,_,hz⟩:=PCPPNativeClauseDescriptorConsumer.descriptor_run a
    (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.slots source k 177) (width source k) (size source k) (index source k)
    hd.1 hd.2.1 hd.2.2 (PCPPNativeHierarchyNodes.forward source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ _ nodes hn' nt nh nw ns ni
  have forward:=PCPPNativeClauseDescriptorConsumer.forward a
    (PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (PCPPNativeHierarchyNodes.slots source k 177) (width source k) (size source k) (index source k) hd.1 hd.2.1 hd.2.2
  obtain ⟨result,rr,rt,rh,keep,rs⟩:=PCPPNativeFrame.frame_run (native source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (target source k) forward _ _ nativeResult hr _ ht hh
  have ready : ClockJoin.ReadyRun (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2*nativeResult.steps+4*(PCPPNative.descriptor request.circuit).length+7)
      (input source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)) result.final.tapes:=
    ⟨result,rr,rfl,rh,rs⟩
  refine ⟨result.final.tapes,ClockJoin.enlarge _ _ _ _ _ ready (by dsimp only [budget,request];omega),rt,?_,?_⟩
  · exact (keep _).trans ha
  · exact (keep _).trans hz

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestDescriptor
