import Proof.CaseAnalysis.RecoveryRowInputSupport
import Proof.CaseAnalysis.RecoveryRowAddressMeaning

/-! Apply the physical input-support lemma to the original normalized PCP,
original builder and actual projected addresses. This is the input_bound
field of RecoveryBoundedRows.Resources; cold funding remains separately paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryOriginalRowSupport
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_bound (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n bound : ℕ} (x : BitInput n) (count : ℕ)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (randomness : BitInput R)
    (W D L S : ℕ) (pre sourceTail : List Bool)
    (hC : capacity W+1≤S) (hD : D≤S) (hL : L≤S) (hb : b.nodes.length≤S)
    (hout : (pre++b.nodes.flatMap PCPPRequestNodeSchema.native).length≤S)
    (hsource : (DedupBytes.fields p++sourceTail).length≤S) (hQR : Q*R≤S)
    (hmeta : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields (capacity W) D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) L R count Q (Codec.clauses p).length j).length≤S) :
    ∀ i,(RecoveryBoundedRow.data b.nodes.length (capacity W) D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) L
      (pre++b.nodes.flatMap PCPPRequestNodeSchema.native) R count
      (RecoveryBoundedQueries.addressWord
        (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)) [] Q
      (DedupBytes.fields p++sourceTail) [] (Codec.clauses p).length i).length≤S := by
  have ha : (RecoveryBoundedQueries.addressWord
      (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)).length≤S := by
    rw [RecoveryBoundedQueries.addressWord_length,projectedAddresses_length]
    exact hQR
  exact CloseoutRecoveryRowInputSupport.data_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hC hD hL hb hout hsource ha (Nat.zero_le S) (Nat.zero_le S) hmeta

end NearCubicWires.RepairOrdinary.CloseoutRecoveryOriginalRowSupport
