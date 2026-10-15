import Proof.Amplification.RecoveryQueryPairSuccessor
import Proof.Foundations.RecoveryCaseOne
import Proof.Amplification.CanonicalRecoveryLanguage

/-! Shared case predicate and canonical objects for repaired recovery and
hardness.  The selectors use the existing zero-first table/typed-description
orders; no arbitrary ScheduledOuterCase witness determines the language. -/
namespace NearCubicWires.RepairSource.RecoveryChoice
open SourceInterfaces OuterPCPRecovery RecoveryScheduleEnvelope
open CanonicalRecoveryLanguage CanonicalSATSelfReduction BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def SmallOracle {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) : Prop :=
  ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
    circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) ∧
      ∀ randomness,acceptsOracleCircuit pcp input circuit randomness

noncomputable def caseTwo {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) : Bool := by
  classical
  exact decide (SmallOracle pcp d input)

@[simp] theorem caseTwo_true {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) :
    caseTwo pcp d input=true ↔ SmallOracle pcp d input := by simp [caseTwo]

noncomputable def proofSelector {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n)
    (complete : ∃ proof,∀ randomness,pcp.accepts input proof randomness) :
    CanonicalAcceptingProof pcp input :=
  Classical.choice (existsCanonicalAcceptingProof pcp input complete)

noncomputable def oracleSelector {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n)
    (small : SmallOracle pcp d input) :
    CanonicalAcceptingOracle (sizeBound := oracleSizeBound d) pcp input :=
  Classical.choice (existsCanonicalAcceptingOracle pcp input small)

theorem proof_eq_any {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n)
    (complete : ∃ proof,∀ randomness,pcp.accepts input proof randomness)
    (other : CanonicalAcceptingProof pcp input) :
    (proofSelector pcp input complete).proof=other.proof := by
  apply List.ofFn_injective
  exact le_antisymm ((proofSelector pcp input complete).minimal other.proof other.accepts)
    (other.minimal _ (proofSelector pcp input complete).accepts)

theorem oracle_description_eq_any {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n)
    (small : SmallOracle pcp d input)
    (other : CanonicalAcceptingOracle (sizeBound := oracleSizeBound d) pcp input) :
    canonicalBoundedCircuitDescription (oracleSizeBound d (pcp.nativeWidth n))
        (oracleSelector pcp d input small).circuit=
      canonicalBoundedCircuitDescription (oracleSizeBound d (pcp.nativeWidth n)) other.circuit := by
  exact le_antisymm ((oracleSelector pcp d input small).minimal _ other.sizeBounded other.accepts)
    (other.minimal _ (oracleSelector pcp d input small).sizeBounded
      (oracleSelector pcp d input small).accepts)

theorem case_formula_iff {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) :
    (∃ assignment : Nat→Bool,TseitinCNF.formulaEval assignment
      (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n)))=true) ↔
      caseTwo pcp d input=true := by
  rw [caseTwo_true,boundedOracleRecoveryFormula_satisfiable_iff]
  constructor
  · rintro ⟨_,circuit,hsize,_,haccepts⟩
    exact ⟨circuit,hsize,haccepts⟩
  · rintro ⟨circuit,hsize,haccepts⟩
    exact ⟨canonicalDescriptionInput circuit hsize,circuit,hsize,rfl,haccepts⟩

theorem proof_prefix {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n)
    (complete : ∃ proof,∀ randomness,pcp.accepts input proof randomness)
    (count : Nat) (hcount : count ≤ 2^pcp.nativeWidth n) :
    recoveredPrefix count (outerProofRecoveryFormula pcp input)=
      (List.ofFn (proofSelector pcp input complete).proof).take count :=
  recoveredOuterProofPrefix_eq_canonical pcp input (proofSelector pcp input complete) count hcount

theorem oracle_prefix {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n)
    (small : SmallOracle pcp d input) (count : Nat)
    (hcount : count ≤ descriptionWidth (pcp.nativeWidth n) (oracleSizeBound d (pcp.nativeWidth n))) :
    recoveredPrefix count (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n)))=
      (List.ofFn (canonicalDescriptionInput (oracleSelector pcp d input small).circuit
        (oracleSelector pcp d input small).sizeBounded)).take count :=
  recoveredBoundedOraclePrefix_eq_canonical pcp input (oracleSelector pcp d input small) count hcount

end NearCubicWires.RepairSource.RecoveryChoice
