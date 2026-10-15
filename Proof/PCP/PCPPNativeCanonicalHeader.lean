import Proof.PCP.PCPPNativeCanonicalBounds
import Proof.Hierarchy.CompetitorWitnessTripleSemantics

/-! The existing total cold extractor consumes the canonical circuit's
tagged pair. Its ordered node tree and encoded output index are physical
framed payloads of the original width, including permitted high zeros. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonical
open LocalBitMultitape SourceInterfaces RepairRepresentation CanonicalBinary ExecutableInterfaces
open RadixSemantics CompetitorWitnessTriple RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nodeWord (bits : List Bool) := RecoveryFixedUnpair.leftWord (word bits 1)
def outputWord (bits : List Bool) := RecoveryFixedUnpair.leftWord (word bits 3)
def headerValid (bits : List Bool) : Prop := field bits 0=1 ∧ field bits 2=1 ∧ node bits 4=0

theorem header_valid_iff (bits : List Bool) : headerValid bits ↔
    value bits=encodeTaggedList [value (nodeWord bits),value (outputWord bits)] := by
  constructor
  · rintro ⟨h0,h2,h4⟩
    change node bits 0=_
    rw [←pair_node bits 0,←pair_node bits 1,←pair_node bits 2,←pair_node bits 3,h0,h2,h4]
    rfl
  · intro h
    simp only [headerValid,field_eq,node_eq,h,nodeCode,encodeTaggedList,Nat.unpair_pair]
    trivial

theorem circuit_values {n : ℕ} (c : BooleanCircuit n) (bits : List Bool)
    (hc : value bits=encodeBooleanCircuit c) :
    headerValid bits ∧ value (nodeWord bits)=encodeBalancedList (c.nodes.map encodeBooleanNode) ∧
      value (outputWord bits)=encodeNat c.output.val := by
  change headerValid bits ∧ field bits 1=_ ∧ field bits 3=_
  simp only [headerValid,field_eq,node_eq,hc,encodeBooleanCircuit,nodeCode,encodeTaggedList,Nat.unpair_pair]
  trivial

theorem tail_retained (x bits : List Bool) : stage x bits 6 79=frame (word bits 4) := by
  have h:=stage_stable x bits 5 1 79 (by decide)
  rw [h]
  change stage x bits (4+1) (slots 4 0)=_
  rw [stage,dif_pos (by omega : 4<6)]
  exact (install_slot (slots (4 : Fin 6)) (slots_injective 4) _ _ 0).trans (by rfl)

theorem header_run (x bits : List Bool) : ∃ result,
    run CompetitorWitnessTriple.machine (CompetitorWitnessTriple.budget bits)
      (CompetitorWitnessTriple.input x bits)=some result ∧
      result.steps≤25000*(bits.length+1)^2 ∧
      result.final.tapes 38=frame (nodeWord bits) ∧ result.final.tapes 78=frame (outputWord bits) ∧
      result.final.tapes 18=frame (RecoveryFixedUnpair.leftWord (word bits 0)) ∧
      result.final.tapes 58=frame (RecoveryFixedUnpair.leftWord (word bits 2)) ∧
      result.final.tapes 79=frame (word bits 4) ∧ (∀ i,result.final.heads i=0) := by
  obtain ⟨result,hr,ht,hh,hs⟩:=triple_run x bits
  refine ⟨result,hr,hs,?_,?_,?_,?_,?_,hh⟩
  · rw [ht]; exact field_output x bits 1
  · rw [ht]; exact field_output x bits 3
  · rw [ht]; exact field_output x bits 0
  · rw [ht]; exact field_output x bits 2
  · rw [ht]; exact tail_retained x bits

end NearCubicWires.RepairOrdinary.PCPPNativeCanonical
