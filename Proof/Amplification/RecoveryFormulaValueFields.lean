import Proof.Amplification.RecoveryFormulaPayload

/-! Intermediate clause words may retain high zero bits. The already
executed balanced serializer interprets their exact original natural codes;
canonical output is produced only once at the final payload boundary. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPayload
open LocalBitMultitape RepairOrdinary RadixSemantics CanonicalBinary BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_code (formula : EncodedCNF) (words : List (List Bool))
    (hv : words.map value=formula.map Encodable.encode) :
    PCPTraversal.code words=balancedCNFPayload formula := by
  unfold PCPTraversal.code PCPSerializerMass.values
  rw [hv]
  rfl

theorem value_field_runs (oracle : Nat→Bool) (formula : EncodedCNF) (words : List (List Bool))
    (hv : words.map value=formula.map Encodable.encode) :
    OrdinaryOracleRuns oracle program (ProjectionNormalization.FieldList.stream words)
      (balancedCNFPayload formula).bits (RecoveryFormulaFrame.budget words) := by
  have h := field_runs oracle words
  rw [value_code formula words hv] at h
  exact h

end NearCubicWires.RepairSource.RecoveryFormulaPayload
