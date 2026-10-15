import Proof.CaseAnalysis.RecoveryGraphBudgetFits
import Proof.CaseAnalysis.RecoveryCountResources
import Proof.CaseAnalysis.RecoveryOriginalRowSupport
import Proof.CaseAnalysis.RecoveryRowMetadataSupport

/-! Assemble the original count compiler's uniform resources from one
explicit support envelope. The caller still physically produces this S and
its unchanged backing; no resource field is supplied without dominance. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization SourceInterfaces CanonicalRecoveryLanguage
open BoundedOracleStructuralCircuit FinitePredicateCircuit OuterPCPRecovery
open CloseoutRecoveryWorkspace CloseoutRecoveryGrammarResources
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def support (W R Q bound : ℕ) (source : List Bool) :=
  (capacity W+1)+8388608*(W+1)^3+268435600*(W+1)^4+(W+7)+
    W*(6*(W+W+5)+3)+source.length+Q*R+
    (RecoveryProjectionRowsRewind.batchBudget R Q+2)+
    (bound+W)*(2*W+1)+(bound+2^R+1)*(2*W+1)

private theorem stream_length {t : ℕ} (fields : Fin t→List Bool) (js : List (Fin t)) (S : ℕ)
    (h : ∀ j∈js,(fields j).length ≤ S) :
    (CloseoutRowsPacketLoad.stream fields js).length ≤ js.length*(2*S+1) := by
  induction js with
  | nil=>simp [CloseoutRowsPacketLoad.stream]
  | cons j js ih=>
    have hf := h j (by simp)
    have ht := ih (fun k hk=>h k (by simp [hk]))
    simp only [CloseoutRowsPacketLoad.stream,List.flatMap_cons,List.length_append,frame_length,
      List.length_cons] at *
    nlinarith

private theorem log_room (W : ℕ) : capacity W+5*W+7 ≤ 268435600*(W+1)^4 := by
  have hp : (W+1)^2 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold capacity
  nlinarith

theorem workspace_description (R bound G W : ℕ) (hW : workspace R bound G ≤ W) :
    R ≤ W ∧ bound ≤ W ∧ boundedCircuitFieldLimit R bound ≤ W ∧ descriptionWidth R bound ≤ W := by
  have h := workspace_bounds R bound G
  have hm := Nat.mul_le_mul_right (rowWidth R bound) (show bound+1 ≤ bound+2 by omega)
  change (bound+1)*rowWidth R bound ≤ (bound+2)*rowWidth R bound at hm
  have hd : descriptionWidth R bound=(bound+1)*rowWidth R bound := rfl
  have hf : boundedCircuitFieldLimit R bound=R+bound+1 := rfl
  rw [hd,hf]
  exact ⟨by omega,by omega,by omega,by omega⟩

variable (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
variable {n bound : ℕ} (x : BitInput n) (G W S : ℕ) (sourceTail : List Bool)
variable (hW : workspace R bound G ≤ W) (hQ : Q ≤ W) (hc : (Codec.clauses p).length ≤ W)
variable (hS : support W R Q bound (DedupBytes.fields p++sourceTail) ≤ S)

include hW hQ hc hS in
private theorem metadata_all (count : ℕ) (hk : count ≤ bound) :
    ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields (capacity W) (8388608*(W+1)^3)
        (boundedCircuitFieldLimit R bound) (268435600*(W+1)^4) R count Q (Codec.clauses p).length j).length ≤ S := by
  have hw := workspace_description R bound G W hW
  have hs := hS
  unfold support at hs
  exact CloseoutRecoveryRowMetadataSupport.original_fields _ _ _ _ _ _ _ _ S
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

include hW hQ hc hS in
private theorem packet_all (count : ℕ) (hk : count ≤ bound) :
    (RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields (capacity W) (8388608*(W+1)^3)
        (boundedCircuitFieldLimit R bound) (268435600*(W+1)^4) R count Q (Codec.clauses p).length)).length ≤ backing W S := by
  have hm := metadata_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS) count hk
  have h := stream_length _ RecoveryBoundedRowReload.ports S hm
  change (RecoveryBoundedRowReload.word _).length ≤ 15*(2*S+1) at h
  unfold backing
  omega

include hW hS in
private theorem graph_all (b : BooleanDAGBuilder (descriptionWidth R bound))
    (hg : b.nodes.length ≤ G) : (b.nodes.flatMap PCPPRequestNodeSchema.native).length ≤ S := by
  have ha := (workspace_description R bound G W hW).2.2.2
  have hG := graph_le_workspace (n:=R) (bound:=bound) (Nat.le_refl G)
  have h := CloseoutRecoveryGraphSupport.workspace_word_bound b 0 [] ha (hg.trans (hG.trans hW)) (by simp)
  simp only [List.nil_append,Nat.zero_add] at h
  unfold support at hS
  omega

include hW hQ hc hS in
private theorem input_all (count : ℕ) (hk : count ≤ bound)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (randomness : BitInput R)
    (hg : b.nodes.length ≤ G) :
    ∀ i,(RecoveryBoundedRow.data b.nodes.length (capacity W) (8388608*(W+1)^3)
      (boundedCircuitFieldLimit R bound) (268435600*(W+1)^4)
      ([]++b.nodes.flatMap PCPPRequestNodeSchema.native) R count
      (RecoveryBoundedQueries.addressWord
        (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)) [] Q
      (DedupBytes.fields p++sourceTail) [] (Codec.clauses p).length i).length ≤ S := by
  have hh := hS
  unfold support at hh
  have hG := (graph_le_workspace (n:=R) (bound:=bound) (Nat.le_refl G)).trans hW
  exact CloseoutRecoveryOriginalRowSupport.input_bound p R Q hr hq x count b randomness
    W (8388608*(W+1)^3) (268435600*(W+1)^4) S [] sourceTail
    (by omega) (by omega) (by omega) (by omega)
    (by simpa only [List.nil_append] using graph_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hS:=hS) b hg)
    (by omega) (by omega)
    (metadata_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS) count hk)

/-- The original reusable row bank, with one common support/backing. -/
noncomputable def baseResources : RecoveryBoundedRows.Resources p R Q hr hq x 0 (Nat.zero_le bound) := by
  have hw := workspace_description R bound G W hW
  have hG := (graph_le_workspace (n:=R) (bound:=bound) (Nat.le_refl G)).trans hW
  have hs := hS
  unfold support at hs
  have hsB : S ≤ backing W S := by unfold backing;omega
  have room := CloseoutRecoveryGrammarResources.room W S (by omega)
  have metadata :=  metadata_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS)
  have packet := packet_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS)
  have inputs := input_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS) (hr:=hr) (hq:=hq) (x:=x)
  exact {
    W:=W, G:=G, D:=8388608*(W+1)^3, L:=268435600*(W+1)^4, B:=backing W S, S:=S
    pre:=[], sourceTail:=sourceTail, packetTail:=[]
    graph_bound:=hG, native_bound:=hw.1, query_bound:=hQ
    dock_bound:=le_rfl, log_bound:=le_rfl, log_capacity:=log_room W
    backing_capacity:=by have h:=room.packet;omega
    backing_dock:=room.dB, backing_log:=room.lB, support_positive:=by omega
    backing_row:=by
      have h := RecoveryBoundedRow.budget_sextic Q (Codec.clauses p).length W hQ hc
      unfold backing
      omega
    projector_bound:=by omega
    metadata_bound:=fun j hj=>(metadata 0 (Nat.zero_le bound) j hj).trans hsB
    packet_bound:=packet 0 (Nat.zero_le bound)
    output_bound:=fun b hb=>by
      simpa only [List.nil_append] using graph_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail) (hW:=hW) (hS:=hS) b hb
    input_bound:=inputs 0 (Nat.zero_le bound)
    query_fits:=fun b r hg=>row_fits_coarse (compactProjectionPCP (p.normalized R Q hr hq)) x b 0 G W (Nat.zero_le bound) r hW hg }

/-- All original count-dependent metadata, packet, input and query contracts
are proofs about one physical bank and the same normalized source. -/
noncomputable def resources : RecoveryBoundedCountUniform.Resources p R Q hr hq (bound:=bound) x := by
  have hs := hS
  unfold support at hs
  have hsB : S ≤ backing W S := by unfold backing;omega
  exact {
    base:=baseResources p R Q hr hq x G W S sourceTail hW hQ hc hS
    metadata_all:=fun count hk j hj=>
      (metadata_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail)
        (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS) count hk j hj).trans hsB
    packet_all:=packet_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail)
      (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS)
    input_all:=input_all (p:=p) (R:=R) (Q:=Q) (G:=G) (W:=W) (S:=S) (sourceTail:=sourceTail)
      (hW:=hW) (hQ:=hQ) (hc:=hc) (hS:=hS) (hr:=hr) (hq:=hq) (x:=x)
    queries_all:=fun count hk b r hg=>row_fits_coarse
      (compactProjectionPCP (p.normalized R Q hr hq)) x b count G W hk r hW hg
    P:=backing W S
    room:=CloseoutRecoveryGrammarResources.room W S (by omega)
    allocation:=allocation_coarse R bound G W hW
    clauses_bound:=hc, source_bound:=by
      change (DedupBytes.fields p++sourceTail).length ≤ backing W S
      omega }

include hS in
theorem empty_stack_bounds :
    (bound+W)*(2*W+1) ≤ S ∧ (bound+2^R+1)*(2*W+1) ≤ backing W S := by
  unfold support at hS
  unfold backing
  constructor <;> omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
