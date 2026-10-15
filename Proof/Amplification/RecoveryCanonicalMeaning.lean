import Proof.Amplification.RecoveryCanonicalBuffers

/-! The chosen certificate's exact semantic dispatch supplies the branch
that the existing checker must execute positively. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_code (code : Nat) (c : Certificate) (hc : Fits code c)
    (ht : RawSyntaxCertificate.tagsValid c.view=true) :
    code=Encodable.encode (RawSyntaxCertificate.project c.view) := by
  apply (encode_of_decodeCNF ?_).symm
  rw [RawSyntaxCertificate.certified_decode code c.view hc.1,ht]
  rfl

theorem marker_case (c : Certificate) (hs : selected c=c)
    (hm : markerCheck (RawSyntaxCertificate.project c.view) c.table c.inner c.outer=true) :
    ∃ flat : Bool,∃ payload : List Bool,∃ tail : RecoveryMarker.TailWords,
      RawSyntaxCertificate.project c.view=RecoveryMarker.formula flat payload tail ∧
      RecoveryMarkerPayload.certificateAnswer flat (RecoveryMarker.tailCommitted tail)
        (RecoveryMarker.tailCount tail) (RadixSemantics.value payload) c.table c.inner c.outer=true := by
  unfold markerCheck at hm
  split at hm
  next payload hf=>
    have hi := selected_flat_rows c hs payload hf
    refine ⟨true,payload.bits,none,?_,?_⟩
    · simpa only [RecoveryMarker.formula,RecoveryMarker.tailClauses,RecoveryUnpair.bits_value] using hf
    · simpa only [RecoveryMarkerPayload.certificateAnswer,ite_true,RecoveryMarker.tailCommitted,
        RecoveryMarker.tailCount,RecoveryUnpair.bits_value,hi] using hm
  next payload committed count hf=>
    have hi := selected_flat_prefix_rows c hs payload committed count hf
    refine ⟨true,payload.bits,some (committed.bits,count.bits),?_,?_⟩
    · simpa only [RecoveryMarker.formula,RecoveryMarker.tailClauses,RecoveryUnpair.bits_value] using hf
    · simpa only [RecoveryMarkerPayload.certificateAnswer,ite_true,RecoveryMarker.tailCommitted,
        RecoveryMarker.tailCount,RecoveryUnpair.bits_value,hi] using hm
  next payload hf=>
    refine ⟨false,payload.bits,none,?_,?_⟩
    · simpa only [RecoveryMarker.formula,RecoveryMarker.tailClauses,RecoveryUnpair.bits_value] using hf
    · simpa only [RecoveryMarkerPayload.certificateAnswer,Bool.false_eq_true,ite_false,
        RecoveryMarker.tailCommitted,RecoveryMarker.tailCount,RecoveryUnpair.bits_value] using hm
  next payload committed count hf=>
    refine ⟨false,payload.bits,some (committed.bits,count.bits),?_,?_⟩
    · simpa only [RecoveryMarker.formula,RecoveryMarker.tailClauses,RecoveryUnpair.bits_value] using hf
    · simpa only [RecoveryMarkerPayload.certificateAnswer,Bool.false_eq_true,ite_false,
        RecoveryMarker.tailCommitted,RecoveryMarker.tailCount,RecoveryUnpair.bits_value] using hm
  next _=>exact False.elim (Bool.false_ne_true hm)

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
