import Proof.PCP.PCPPNativeHierarchyNodesForward
import Proof.PCP.PCPPNativeClauseDescriptorSource

/-! The original hierarchy/oracle request now runs through the single
selected projection source, exact native substitution and descriptor, and
the single faithful pointwise PCPP source into its physical shared cache. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  PCPPNativeClauseDescriptorConsumer.sourceMachine a (PCPPNativeHierarchyNodes.machine source k CH Cpad code)
    (PCPPNativeHierarchyNodes.slots source k 177) (PCPPNativeHierarchyNodes.slots source k 72)
    (PCPPNativeHierarchyNodes.slots source k 91) (PCPPNativeHierarchyNodes.slots source k 89)
def input (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy oracle : List Bool) :=
  PCPPNativeClauseDescriptorConsumer.sourceInput a (PCPPNativeHierarchyNodes.input source k hierarchy oracle)
def cacheSlots (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (PCPPSourceCache.tapes a)) :=
  PCPPNativeClauseDescriptorConsumer.cacheSlots a (PCPPNativeHierarchyNodes.slots source k 72)
    (PCPPNativeHierarchyNodes.slots source k 91) (PCPPNativeHierarchyNodes.slots source k 89) j
def budget (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n)
    (bound : List Bool) (hpad : k+3≤Cpad) (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k CH Cpad code x)) :=
  PCPPNativeClauseDescriptorConsumer.sourceBudget a (PCPPNativeHierarchyNodes.circuit source k CH Cpad code x hpad oracle)
    (PCPPNativeHierarchyNodes.budget source k CH Cpad code x bound oracle)

theorem source_run (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (bound : List Bool) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k CH Cpad code x)) :
    let request:=PCPPRequestBoundary.request a (PCPPNativeHierarchyNodes.circuit source k CH Cpad code x hpad oracle)
    ∃ result,run (machine source a k CH Cpad code) (budget source a k CH Cpad code x bound hpad oracle)
      (input source a k (frame (List.ofFn x)++frame bound) (PCPPNative.descriptor oracle))=some result ∧
      result.steps≤budget source a k CH Cpad code x bound hpad oracle ∧
      (∀ j : Fin 19,result.final.tapes (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,result.final.heads (cacheSlots source a k (PCPPSourceCache.cacheSlots a j))=PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=List.replicate request.circuit.size true ∧
      result.final.heads (cacheSlots source a k (PCPPSourceCache.sizeSlot a))=0 := by
  obtain ⟨native,hr,_,hout,hhead,_,hindex,_,hsize,_,hwidth⟩ :=
    PCPPNativeHierarchyNodes.raw_run source k CH Cpad code x bound hpad oracle
  have hd:=PCPPNativeHierarchyNodes.scalar_distinct source k
  exact PCPPNativeClauseDescriptorConsumer.source_run a (PCPPNativeHierarchyNodes.machine source k CH Cpad code)
    (PCPPNativeHierarchyNodes.slots source k 177) (PCPPNativeHierarchyNodes.slots source k 72)
    (PCPPNativeHierarchyNodes.slots source k 91) (PCPPNativeHierarchyNodes.slots source k 89)
    hd.1 hd.2.1 hd.2.2 (PCPPNativeHierarchyNodes.forward source k CH Cpad code)
    (PCPPNativeHierarchyNodes.circuit source k CH Cpad code x hpad oracle)
    (PCPPNativeHierarchyNodes.budget source k CH Cpad code x bound oracle)
    (PCPPNativeHierarchyNodes.input source k (frame (List.ofFn x)++frame bound) (PCPPNative.descriptor oracle))
    native hr hout hhead hwidth hsize hindex

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
