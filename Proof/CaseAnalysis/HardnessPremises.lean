import Proof.CaseAnalysis.HardnessCaps
import Proof.CaseAnalysis.CaseOneEventual
import Proof.CaseAnalysis.WitnessAritySeam

/-! Exact remaining producer interfaces for the joint hardness binding.
Completeness is needed only at dyadic source lengths, matching the checked
N/16 family bound. Halting and little-o still quantify every input length. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary SelectedRecoveryIntegration RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def ClauseReady (sources : EightSources) (degree clauseDegree : Nat) : Prop :=
  ∃ onset, ∀ (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    (N : Nat) (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)),
    oracle.size ≤ oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth N) →
    onset ≤ (outer sources k clock).result.pcp.nativeWidth N →
    ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle)).clauseBits ≤
      clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth N)

theorem exists_clauseReady (sources : EightSources) (degree : Nat) :
    ∃ clauseDegree, 1 ≤ clauseDegree ∧ ClauseReady sources degree clauseDegree := by
  obtain ⟨d,onset,hd,h⟩ := selected_clause_degree sources degree
  exact ⟨d,hd,onset,fun k clock N input oracle ho hq => (h k clock N input oracle ho hq).2⟩

def SampledCompleteness (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (M : OrdinaryWeakMachine)
    (degree copies clauseDegree : Nat) (delta : ℚ)
    (family : SizedFunctionFamily) (logExponent : Nat) (cap : ℝ) : Prop :=
  ∃ onset, ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
    ∀ hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input,
    let oracle := (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
    let request := CloseoutWitnessPolicy.request sources k clock input oracle
    let pcpp := (selectedPCPP sources).output request
    let cb := clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s))
    ∀ hc : pcpp.clauseBits ≤ cb,
    SampledXorSum family delta (request.arity+cb+1) copies
      ⌊wireScale cap logExponent ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
      (paddedUnsigned pcpp hc) → M.accepts (2^s) input

end
end NearCubicWires.RepairSource.CloseoutLanguage
