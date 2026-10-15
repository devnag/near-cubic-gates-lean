import Proof.Amplification.RecoveryPrefixColdBudget

/-! The checked cold search at the two actual canonical recovery formulas.
The existing balanced payload is its input; the remaining emitter must
produce this input from the retained normalized PCP word. All decoding,
formula-size guards, and full canonical-output identities are discharged. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPrefix
open RepairOrdinary CanonicalBinary CanonicalRecoveryLanguage
open CanonicalSATSelfReduction BoundedOracleStructuralCircuit TseitinCNF
open BalancedCNFSATEncoding CircuitInputCNF SourceInterfaces OuterPCPRecovery
open RecoveryScheduleEnvelope RecoveryChoice RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload (formula : EncodedCNF) := balancedCNFPayload formula

theorem payload_decodes (formula : EncodedCNF) : PayloadDecodes true (payload formula) formula := by
  simp [PayloadDecodes,payload,balancedCNFPayload]

theorem formula_runs (formula : EncodedCNF) (total : Nat)
    (hw : wellSizedCNFEncoding (Encodable.encode formula) formula=true)
    (hr : total ≤ natBitLength (Encodable.encode formula)) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (RecoveryPrefixCold.program 1073741824 true)
      (RecoveryPrefixMeasure.request (payload formula) total) (recoveredPrefix total formula)
      (68719476736*(RecoveryPrefixCold.radius (payload formula) total)^3) := by
  have h := RecoveryPrefixCold.polynomial_runs (payload formula) total true
  rw [RecoveryPrefixBody.search_canonical true (payload formula) formula total (payload_decodes formula) hw hr] at h
  exact h

def proofCount {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (n : Nat) := 2^pcp.nativeWidth n

def oracleCount {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d n : Nat) :=
  descriptionWidth (pcp.nativeWidth n) (oracleSizeBound d (pcp.nativeWidth n))

theorem proof_range {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n) :
    proofCount pcp n ≤ natBitLength (Encodable.encode (outerProofRecoveryFormula pcp input)) :=
  (outerProofVariables_le_formula_length pcp input).trans (list_length_le_encoded_bitLength _)

theorem oracle_range {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) :
    oracleCount pcp d n ≤ natBitLength (Encodable.encode
      (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n)))) := by
  let verifier := boundedOracleVerifierCircuit pcp input (oracleSizeBound d (pcp.nativeWidth n))
  have hv : oracleCount pcp d n ≤ (circuitInputFormula verifier).length :=
    (Nat.le_add_right _ verifier.nodes.length).trans (circuitInputVariables_le_formula_length verifier)
  exact hv.trans (list_length_le_encoded_bitLength _)

theorem proof_runs {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n)
    (complete : ∃ proof,∀ randomness,pcp.accepts input proof randomness) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (RecoveryPrefixCold.program 1073741824 true)
      (RecoveryPrefixMeasure.request (payload (outerProofRecoveryFormula pcp input)) (proofCount pcp n))
      (List.ofFn (proofSelector pcp input complete).proof)
      (68719476736*(RecoveryPrefixCold.radius (payload (outerProofRecoveryFormula pcp input)) (proofCount pcp n))^3) := by
  have h := formula_runs (outerProofRecoveryFormula pcp input) (proofCount pcp n)
    (outerProofRecoveryFormula_wellSized pcp input) (proof_range pcp input)
  rw [proof_prefix pcp input complete (proofCount pcp n) (show proofCount pcp n ≤ 2^pcp.nativeWidth n from Nat.le_refl _)] at h
  rw [List.take_of_length_le (by simp [proofCount])] at h
  exact h

theorem oracle_runs {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n)
    (small : SmallOracle pcp d input) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (RecoveryPrefixCold.program 1073741824 true)
      (RecoveryPrefixMeasure.request
        (payload (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n))))
        (oracleCount pcp d n))
      (List.ofFn (canonicalDescriptionInput (oracleSelector pcp d input small).circuit
        (oracleSelector pcp d input small).sizeBounded))
      (68719476736*(RecoveryPrefixCold.radius
        (payload (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n))))
        (oracleCount pcp d n))^3) := by
  have h := formula_runs (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n)))
    (oracleCount pcp d n) (boundedOracleRecoveryFormula_wellSized pcp input _) (oracle_range pcp d input)
  rw [oracle_prefix pcp d input small (oracleCount pcp d n) (show oracleCount pcp d n ≤ descriptionWidth (pcp.nativeWidth n) (oracleSizeBound d (pcp.nativeWidth n)) from Nat.le_refl _)] at h
  rw [List.take_of_length_le (by rw [List.length_ofFn]; exact Nat.le_refl _)] at h
  exact h

end NearCubicWires.RepairSource.RecoveryFormulaPrefix
