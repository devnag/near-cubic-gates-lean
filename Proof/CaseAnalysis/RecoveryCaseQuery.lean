import Proof.Amplification.RecoveryFormulaPrefix

/-! The case decision is the existing compact SAT query with no committed
description bits. It uses the SAME balanced payload as canonical recovery;
the query code is built by the already checked physical kernel. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
open SourceInterfaces OuterPCPRecovery CanonicalSATSelfReduction
open BoundedOracleStructuralCircuit RecoveryScheduleEnvelope
open RecoveryChoice RecoveryQuery RecoveryFormulaPrefix RecoveryOracle TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem uncommitted_query (formula : EncodedCNF)
    (hw : wellSizedCNFEncoding (Encodable.encode formula) formula=true) :
    correctedSat (code true (payload formula) 0 0)=true ↔
      ∃ assignment : Nat→Bool, formulaEval assignment formula=true := by
  rw [query_meaning true (payload formula) 0 0 formula (payload_decodes formula)]
  have hthree : formula.all (fun clause => clause.length=3)=true := by
    simp only [wellSizedCNFEncoding, Bool.and_eq_true, List.all_eq_true] at hw ⊢
    intro clause hc
    exact (hw.2 clause hc).1
  simp [compactMeaning,hthree]

theorem case_query {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (degree : Nat) {n : Nat}
    (input : BitInput n) :
    correctedSat (code true (payload (boundedOracleRecoveryFormula pcp input
      (oracleSizeBound degree (pcp.nativeWidth n)))) 0 0)=caseTwo pcp degree input := by
  apply Bool.eq_iff_iff.mpr
  exact (uncommitted_query _ (boundedOracleRecoveryFormula_wellSized pcp input _)).trans
    (case_formula_iff pcp degree input)

end NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
