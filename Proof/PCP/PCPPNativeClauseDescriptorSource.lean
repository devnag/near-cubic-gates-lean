import Proof.PCP.PCPPNativeClauseDescriptorConsumer

/-! The actual original node emitter feeds the typed descriptor and the
single faithful PCPP source call, ending in its physically prepared cache. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sourceMachine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target width size index : Fin t) :=
  PCPPNativeSource.machine a (machine a p target width size index)
    (slots width size index 26) (slots width size index 27) (slots width size index 10)
def sourceInput (a : PointwisePCPPAlgorithm) {t : ℕ} (nativeInput : Fin t→List Bool) :=
  PCPPNativeSource.input a (input nativeInput)
def sourceBudget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ) :=
  PCPPNativeSource.budget a (PCPPRequestBoundary.request a c) (budget a c fuel)
def cacheSlots (a : PointwisePCPPAlgorithm) {t : ℕ} (width size index : Fin t)
    (j : Fin (PCPPSourceCache.tapes a)) :=
  PCPPNativeSource.sourceSlots a (slots width size index 27) (slots width size index 10) j

theorem source_run (a : PointwisePCPPAlgorithm) {t s n : ℕ} (p : Machine t s)
    (target width size index : Fin t) (ws : width≠size) (wi : width≠index) (si : size≠index)
    (nodeForward : CursorRestore.NoLeft p target) (c : BooleanCircuit n)
    (fuel : ℕ) (nativeInput : Fin t→List Bool) (native : ExecutionReceipt t s)
    (hr : run p fuel nativeInput=some native)
    (hout : native.final.tapes target=c.nodes.flatMap PCPPRequestNodeSchema.native)
    (hhead : native.final.heads target=(c.nodes.flatMap PCPPRequestNodeSchema.native).length)
    (hwidth : native.final.tapes width=List.replicate n true)
    (hsize : native.final.tapes size=List.replicate c.size true)
    (hindex : native.final.tapes index=List.replicate c.output.val true) :
    let request:=PCPPRequestBoundary.request a c
    ∃ result,run (sourceMachine a p target width size index) (sourceBudget a c fuel) (sourceInput a nativeInput)=some result ∧
      result.steps ≤ sourceBudget a c fuel ∧
      (∀ j : Fin 19,result.final.tapes (cacheSlots a width size index (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,result.final.heads (cacheSlots a width size index (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (cacheSlots a width size index (PCPPSourceCache.sizeSlot a))=
        List.replicate request.circuit.size true ∧
      result.final.heads (cacheSlots a width size index (PCPPSourceCache.sizeSlot a))=0 := by
  obtain ⟨descriptor,hd,_,dt,dh,_,dd,_,ds⟩:=descriptor_run a p target width size index ws wi si
    nodeForward c fuel nativeInput native hr hout hhead hwidth hsize hindex
  have distinct : slots width size index 27≠slots width size index 10 :=
    fun h=> (by decide : (27 : Fin 65)≠10) ((slots_injective width size index ws wi si) h)
  exact PCPPNativeSource.source_run a (machine a p target width size index)
    (slots width size index 26) (slots width size index 27) (slots width size index 10) distinct
    (forward a p target width size index ws wi si) (PCPPRequestBoundary.request a c)
    (budget a c fuel) (input nativeInput) descriptor hd dt dh ds dd

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
