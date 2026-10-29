import SourceAdapters.Compile.BoundedVerifierCircuit
import SourceAdapters.Compile.BoundedRank

/-!
proof of `lem:multitape-refuter`, Step 3: concrete half-open interval SAT queries.
This module gives the actual formula and its exact semantics. The actual
ordinary request-to-native-word program remains a distinct required conjunct
of ComputationToCNF, and is not supplied by value-level definability.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
  NearCubicWires.CircuitInputCNF NearCubicWires.TseitinCNF
set_option autoImplicit false

def requestVerdictWire (r : CNFCompilationRequest) :=
  let verdict := verifierVerdictWire r.verifier r.input r.witnessLength r.fuel
  verdict.andThen (compileExpr verdict.final (rankLessExpression r.witnessLength r.high))

def requestCircuit (r : CNFCompilationRequest) : BooleanCircuit r.witnessLength :=
  let verdict := requestVerdictWire r
  verdict.final.finish verdict.output

/-- Every circuit input is exactly one witness of the requested length. -/
theorem requestCircuit_correct (r : CNFCompilationRequest) (witness : BitInput r.witnessLength) :
    (requestCircuit r).eval witness = true ↔
      witnessRank witness < r.high ∧ r.verifier.acceptsAt r.fuel r.input (List.ofFn witness) := by
  have hv := verifierCircuit_correct r.verifier r.input witness r.fuel
  rw [verifierCircuit, BooleanDAGBuilder.finish_eval,
    (verifierVerdictWire r.verifier r.input r.witnessLength r.fuel).correct] at hv
  rw [requestCircuit, BooleanDAGBuilder.finish_eval, (requestVerdictWire r).correct]
  change (_ && (rankLessExpression r.witnessLength r.high).eval witness) = true ↔ _
  rw [Bool.and_eq_true, rankLessExpression_correct]
  exact (and_congr hv Iff.rfl).trans and_comm

/-- Appending the strict comparator costs at most 5*n+2 nodes. -/
theorem requestCircuit_size (r : CNFCompilationRequest) :
    (requestCircuit r).size ≤
      (verifierCircuit r.verifier r.input r.witnessLength r.fuel).size + 5*r.witnessLength+2 := by
  let verdict := verifierVerdictWire r.verifier r.input r.witnessLength r.fuel
  let rank := compileExpr verdict.final (rankLessExpression r.witnessLength r.high)
  have hsize := rank.extension.length_eq
  have hadded : rank.extension.suffix.length =
      (rankLessExpression r.witnessLength r.high).nodeCount := compileExpr_addedNodes _ _
  have hrank := rankLessExpression_nodes r.witnessLength r.high
  change (verdict.andThen rank).final.nodes.length ≤ verdict.final.nodes.length + 5*r.witnessLength+2
  simp only [CompiledWire.andThen, combineSequential, BooleanDAGBuilder.appendNode_length]
  omega

/-- The produced CNF is the native free-input Tseitin formula of the real circuit. -/
def requestFormula (r : CNFCompilationRequest) : EncodedCNF := circuitInputFormula (requestCircuit r)

theorem requestFormula_three (r : CNFCompilationRequest) :
    ∀ clause ∈ requestFormula r, clause.length = 3 := circuitCNF_three _

theorem requestFormula_correct (r : CNFCompilationRequest) :
    (∃ assignment, formulaEval assignment (requestFormula r) = true) ↔ r.accepts := by
  rw [requestFormula, circuitInputFormula_satisfiable_iff]
  exact exists_congr (fun witness => requestCircuit_correct r witness)

theorem requestFormula_decode (r : CNFCompilationRequest) :
    RecoveryOracle.decodeSourceSAT (RecoveryOracle.sourceSATCode (requestFormula r)) =
      some (requestFormula r) := RecoveryOracle.decodeSourceSAT_encode _

theorem requestFormula_sourceSAT (r : CNFCompilationRequest) :
    RecoveryOracle.sourceSAT (RecoveryOracle.sourceSATCode (requestFormula r)) = true ↔ r.accepts :=
  (RecoveryOracle.sourceSAT_encode_iff _ (requestFormula_three r)).trans (requestFormula_correct r)

end NearCubicGates.Adapters.Compile
