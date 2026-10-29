import SourceAdapters.Compile.OraclePolynomial
import SourceAdapters.Compile.OraclePrintAssembly

/-!
The proof of `thm:short-pcp-ours`, Step 4: the concrete circuit's global native
encoding bound and the interface used by its physical printing program.
The conditional assembly theorem takes the explicit cell-program contract;
`OraclePrintMain` supplies the complete ordinary implementation.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.MW20
  NearCubicGates.Close.Cells OracleExecution
set_option autoImplicit false

theorem requestCircuit_word_length (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (OracleOutput.word ⟨r.ell,requestCircuit p r⟩).length ≤
      64*(circuitCoefficient p.base.tapeCount p.base.stateCount+2)^3*r.measure^18 := by
  exact OraclePrint.word_length_le_measure (requestCircuit p r) r.measure
    (circuitCoefficient p.base.tapeCount p.base.stateCount) 5 (OraclePrint.measure_positive r)
    (by unfold OracleCompilationRequest.measure; omega) (requestCircuit_size_polynomial p r)

/-- The program premise is a concrete paid cell program for this circuit family. -/
theorem computationToCircuit_of_native_programs
    (h : ∀ p : OrdinaryOracleProgram, ∃ (main : St VV MM) (a c K e : ℕ)
      (N : OracleCompilationRequest → ℕ), 1≤a ∧
      OraclePrint.OracleProgramRuns (requestCircuit p) main a c N ∧ (∀ r, N r≤K*r.measure^e)) :
    ComputationToCircuit := by
  intro p
  obtain ⟨main,a,c,K,e,N,ha,hrun,hN⟩ := h p
  exact OraclePrint.computationToCircuit_at_of_program p (requestCircuit p)
    (circuitCoefficient p.base.tapeCount p.base.stateCount) 5
    (requestCircuit_false_iff p) (requestCircuit_size_polynomial p) main a c K e N ha hrun hN

end NearCubicGates.Adapters.Compile.OracleExpressions
