import Proof.CaseAnalysis.WitnessNativeScreen
import Proof.PCP.PCPPNativeClauseDescriptorSource
import Proof.PCP.PCPPNativeClauseQueryForward
import Proof.PCP.PCPPNativeCompactCircuit

/-! The guarded measured fields feed the original node emitter, its exact
typed descriptor, and one faithful PCPP call with the reusable cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def nativeMachine:=TapeEmbedding.machine 1 PCPPNativeClauseOracle.machine
def nativeInput {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  Fin.addCases (m:=363) (n:=1) (motive:=fun _=>List Bool)
    (PCPPNativeCounterNodes.nodeInput (PCPPNative.descriptor oracle)
      (PCPPNativeMetadataMass.queryBytes p R Q) (DedupBytes.fields p) R Q oracle.size
      (Codec.clauses p).length (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length)
    (fun _=>List.replicate R true)
def nativeBudget {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  PCPPNativeClauseOracle.budget oracle Q (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length
def machine (a : PointwisePCPPAlgorithm):=
  PCPPNativeClauseDescriptorConsumer.sourceMachine a nativeMachine 102 363 16 14
def input (a : PointwisePCPPAlgorithm) {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  PCPPNativeClauseDescriptorConsumer.sourceInput a (nativeInput oracle p Q)
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin (PCPPSourceCache.tapes a)):=
  PCPPNativeClauseDescriptorConsumer.cacheSlots a (363 : Fin 364) 16 14 j
def request (a : PointwisePCPPAlgorithm) (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R):=
  PCPPRequestBoundary.request a (PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle)
def budget (a : PointwisePCPPAlgorithm) (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R):=
  PCPPNativeClauseDescriptorConsumer.sourceBudget a
    (PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle) (nativeBudget oracle p Q)

theorem native_forward : CursorRestore.NoLeft nativeMachine 102:=
  EquationRowCuts.embedded_forward 1 PCPPNativeClauseOracle.machine 102 PCPPNativeClauseForward.whole

theorem cache_run (a : PointwisePCPPAlgorithm) (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    let r:=request a p R Q hR hQ x oracle
    ∃ actual,run (machine a) (budget a p R Q hR hQ x oracle) (input a oracle p Q)=some actual ∧
      actual.steps≤budget a p R Q hR hQ x oracle ∧
      (∀ j : Fin 19,actual.final.tapes (cacheSlots a (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      (∀ j : Fin 19,actual.final.heads (cacheSlots a (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      actual.final.tapes (cacheSlots a (PCPPSourceCache.sizeSlot a))=List.replicate r.circuit.size true ∧
      actual.final.heads (cacheSlots a (PCPPSourceCache.sizeSlot a))=0:=by
  let c:=PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle
  obtain ⟨b,hb,bt,bh,_,b14,_,b16,_⟩:=PCPPNativeClauseOracle.original_run p R Q hR hQ x oracle []
    (PCPPNativeCompactNodes.clauses p R Q hR hQ x)
  simp only [List.append_nil,PCPPNativeCompactNodes.count,PCPPNativeCompactNodes.fields] at hb b14 b16
  rw [PCPPNativeCounterNodes.node_input] at hb
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>List.replicate R true) b
  have firstRun:=TapeEmbedding.run_embed PCPPNativeClauseOracle.machine (fun _ : Fin 1=>0)
    (fun _=>List.replicate R true) _ _ b hb
  rw [StreamPrepare.embed_initial] at firstRun
  have cn:c.nodes=PCPPNativeCompactNodes.nodes p R Q hR hQ x oracle:=
    PCPPNativeCompactNodes.circuit_nodes _ _ _ _ _ _ _
  have cs:c.size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length:=
    PCPPNativeCompactNodes.circuit_size _ _ _ _ _ _ _
  have co:c.output.val=PCPPNativeCount.outputIndex Q oracle.size (Codec.clauses p).length:=
    PCPPNativeCompactNodes.circuit_output _ _ _ _ _ _ _
  apply PCPPNativeClauseDescriptorConsumer.source_run a nativeMachine 102 363 16 14
    (by decide) (by decide) (by decide) native_forward c (nativeBudget oracle p Q)
    (nativeInput oracle p Q) lifted firstRun
  · rw [cn]
    exact (TapeEmbedding.receipt_tapes_old _ _ b (102 : Fin 363)).trans bt
  · rw [cn]
    exact (TapeEmbedding.receipt_heads_old _ _ b (102 : Fin 363)).trans bh
  · exact TapeEmbedding.receipt_tapes_new _ _ b (0 : Fin 1)
  · rw [cs]
    exact (TapeEmbedding.receipt_tapes_old _ _ b (16 : Fin 363)).trans b16
  · rw [co]
    exact (TapeEmbedding.receipt_tapes_old _ _ b (14 : Fin 363)).trans b14

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
