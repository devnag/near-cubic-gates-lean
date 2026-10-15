import Proof.Amplification.RecoverySourceClauseBudget
import Proof.Amplification.RecoveryFormulaValueFields

/-! The actual source-clause words seal the original outer-proof formula.
Randomness order, repeated clauses and the initial variable tautologies are
preserved literally. This consumes physical fields; their whole producer
remains the next enclosing machine. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResume
open LocalBitMultitape RepairOrdinary RadixSemantics SourceInterfaces
open CanonicalRecoveryLanguage CircuitInputCNF CanonicalBinary BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowWords {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) : List (List Bool) :=
  (pcp.decision x randomness).clauses.map (RecoverySourceClauseCode.word pcp x randomness)

def randomWords {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) : List (List Bool) :=
  (allBitInputs (pcp.nativeWidth n)).flatMap (rowWords pcp x)

def words {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) : List (List Bool) :=
  RecoveryFormulaPayload.fields (circuitInputTautologies (2^pcp.nativeWidth n))++randomWords pcp x

theorem row_values {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    (rowWords pcp x randomness).map value=(outerProofRowFormula pcp x randomness).map Encodable.encode := by
  simp only [rowWords,outerProofRowFormula,List.map_map,Function.comp_def,
    RecoverySourceClauseCode.word_value]

theorem random_values {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) :
    (randomWords pcp x).map value=
      ((allBitInputs (pcp.nativeWidth n)).flatMap (outerProofRowFormula pcp x)).map Encodable.encode := by
  simp only [randomWords,List.map_flatMap]
  exact congrArg (fun f=>(allBitInputs (pcp.nativeWidth n)).flatMap f)
    (funext (fun randomness=>row_values pcp x randomness))

theorem values {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) :
    (words pcp x).map value=(outerProofRecoveryFormula pcp x).map Encodable.encode := by
  rw [words,outerProofRecoveryFormula,List.map_append,List.map_append,random_values]
  congr 1
  simp only [RecoveryFormulaPayload.fields,List.map_map]
  congr 1
  funext clause
  exact CanonicalPositiveOutput.nat_bits_value _

theorem serialize_runs (oracle : Nat→Bool) {M : TimedDecisionMachine} {T : Nat→Nat}
    (pcp : ProjectionPCP M T) {n : Nat} (x : BitInput n) :
    OrdinaryOracleRuns oracle RecoveryFormulaPayload.program
      (ProjectionNormalization.FieldList.stream (words pcp x))
      (balancedCNFPayload (outerProofRecoveryFormula pcp x)).bits
      (RecoveryFormulaFrame.budget (words pcp x)) :=
  RecoveryFormulaPayload.value_field_runs oracle _ _ (values pcp x)

theorem word_count {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) : (words pcp x).length=(outerProofRecoveryFormula pcp x).length := by
  have h:=congrArg List.length (values pcp x)
  simpa only [List.length_map] using h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResume
