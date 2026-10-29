import SourceAdapters.Compile.OracleNodeStream
import SourceAdapters.Compile.OracleNative

/-!
proof of `thm:short-pcp-ours`: the exact plain stream inherits the concrete DAG's valid
references, polynomial node count and native word bound. These are facts
about the physical printer, not a replacement for its actual run theorem.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairSource NearCubicWires.Bindings.MW20 OracleExecution
set_option autoImplicit false

theorem requestStream_size (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestStream p r).1.length ≤ circuitCoefficient p.base.tapeCount p.base.stateCount*r.measure^5 := by
  rw [←(requestCircuit_stream p r).1]
  exact requestCircuit_size_polynomial p r

theorem requestStream_output_lt (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestStream p r).2<(requestStream p r).1.length := by
  rw [←(requestCircuit_stream p r).1,←(requestCircuit_stream p r).2]
  exact (requestCircuit p r).output.isLt

theorem requestStream_wellFormed (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (index : ℕ) (hi : index<(requestStream p r).1.length) :
    ((requestStream p r).1[index]).WellFormedAt index := by
  have hc : index<(requestCircuit p r).nodes.length := by
    rw [(requestCircuit_stream p r).1]
    exact hi
  have h := (requestCircuit p r).wellFormed ⟨index,hc⟩
  simpa only [List.get_eq_getElem,(requestCircuit_stream p r).1] using h

/-- The actual native word to be printed, including its header and final reference. -/
def requestStreamWord (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) : List Bool :=
  natWord r.ell++natWord (requestStream p r).1.length++
    (requestStream p r).1.flatMap oracleNodeWord++natWord (requestStream p r).2

theorem requestCircuit_word_eq_stream (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    OracleOutput.word ⟨r.ell,requestCircuit p r⟩=requestStreamWord p r := by
  simp only [OracleOutput.word,requestStreamWord,(requestCircuit_stream p r).1,(requestCircuit_stream p r).2]

theorem requestStreamWord_length (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestStreamWord p r).length ≤
      64*(circuitCoefficient p.base.tapeCount p.base.stateCount+2)^3*r.measure^18 := by
  rw [←requestCircuit_word_eq_stream]
  exact requestCircuit_word_length p r

end NearCubicGates.Adapters.Compile.OracleExpressions
