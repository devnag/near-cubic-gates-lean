import Proof.CaseAnalysis.WitnessSelectedNodes
import Proof.PCP.PCPPNativeClauseDescriptorSource

/-! Original x and the same raw oracle reach one faithful pointwise-PCPP
call and its allocated reusable cache. The actual padded request arity is
already retained at public cache slot13/head1 for family circuit validation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad G : ℕ) (code : List Bool):=
  PCPPNativeClauseDescriptorConsumer.sourceMachine a (SelectedNodes.machine source k CH Cpad G code)
    (SelectedNodes.slots source k G 102) (SelectedNodes.widthSlot source k G)
    (SelectedNodes.slots source k G 16) (SelectedNodes.slots source k G 14)
def input (a : PointwisePCPPAlgorithm) (k G : ℕ) (x raw : List Bool):=
  PCPPNativeClauseDescriptorConsumer.sourceInput a (SelectedNodes.input source k G x raw)
def cacheSlots (a : PointwisePCPPAlgorithm) (k G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  PCPPNativeClauseDescriptorConsumer.cacheSlots a (SelectedNodes.widthSlot source k G)
    (SelectedNodes.slots source k G 16) (SelectedNodes.slots source k G 14) j
def request (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (hpad : k+3  ≤  Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  PCPPRequestBoundary.request a (SelectedNodes.circuit source k CH Cpad code x hpad oracle)
def budget (a : PointwisePCPPAlgorithm) (k CH Cpad G : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (raw : List Bool) (hpad : k+3  ≤  Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  PCPPNativeClauseDescriptorConsumer.sourceBudget a (SelectedNodes.circuit source k CH Cpad code x hpad oracle)
    (SelectedNodes.budget source k CH Cpad G code x raw oracle)

theorem source_run (a : PointwisePCPPAlgorithm) (k CH Cpad G : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (raw : List Bool) (hpad : k+3  ≤  Cpad) (hN : 2  ≤  n) (hcap : 16*raw.length  ≤  n)
    (hwidth : (SelectedOracle.width source k CH Cpad code (List.ofFn x)).bits.length  ≤  n+1)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hd : decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle) :
    let r:=request source a k CH Cpad code x hpad oracle
    ∃ actual,run (machine source a k CH Cpad G code) (budget source a k CH Cpad G code x raw hpad oracle)
      (input source a k G (List.ofFn x) raw)=some actual ∧
      actual.steps  ≤  budget source a k CH Cpad G code x raw hpad oracle ∧
      (∀ j : Fin 19,actual.final.tapes (cacheSlots source a k G (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      (∀ j : Fin 19,actual.final.heads (cacheSlots source a k G (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      actual.final.tapes (cacheSlots source a k G (PCPPSourceCache.sizeSlot a))=
        List.replicate r.circuit.size true ∧
      actual.final.heads (cacheSlots source a k G (PCPPSourceCache.sizeSlot a))=0:=by
  obtain ⟨native,hr,_,hout,hhead,_,hindex,_,hsize,_,hwidth⟩:=
    SelectedNodes.nodes_run source k CH Cpad G code x raw hpad hN hcap hwidth oracle hd
  have hs:=SelectedNodes.scalar_distinct source k G
  exact PCPPNativeClauseDescriptorConsumer.source_run a (SelectedNodes.machine source k CH Cpad G code)
    (SelectedNodes.slots source k G 102) (SelectedNodes.widthSlot source k G)
    (SelectedNodes.slots source k G 16) (SelectedNodes.slots source k G 14)
    hs.1 hs.2.1 hs.2.2 (SelectedNodes.forward source k CH Cpad G code)
    (SelectedNodes.circuit source k CH Cpad code x hpad oracle)
    (SelectedNodes.budget source k CH Cpad G code x raw oracle)
    (SelectedNodes.input source k G (List.ofFn x) raw) native hr hout hhead hwidth hsize hindex

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
