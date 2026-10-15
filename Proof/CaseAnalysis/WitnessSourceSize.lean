import Proof.CaseAnalysis.WitnessPolicy
import Proof.CaseAnalysis.NativeWidthPolynomial
import Proof.CaseAnalysis.SelectedClauses
import Proof.CaseAnalysis.FamilyCodeEnvelope

/-! Uniform N/16 bound for the full actual oracle-dependent witness family.
The onset is chosen before input, oracle and witness; the source's actual
clause count controls the guard, while its fixed polynomial bounds code size. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary CanonicalWitnessCodec
open CloseoutWitness RecoveryWitnessPolicy RecoveryScheduleEnvelope
open SelectedRecoveryIntegration CloseoutLanguage PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def request (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    {N : Nat} (input : BitInput N) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)) :=
  PCPPSubstitution.sourceRequest (selectedPCPP sources) oracle
    ((outer sources k clock).result.pcp.queryAddressBits input)
    ((outer sources k clock).result.pcp.decision input (fun _=>false))

def variableCount (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    {N : Nat} (input : BitInput N) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)) :=
  let pcpp:=(selectedPCPP sources).output (request sources k clock input oracle)
  pcpp.systematicBits+pcpp.auxiliaryBits

def actual (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (oracleDegree degree copies : Nat) (W : Nat→Nat) (delta : ℚ)
    {N : Nat} (input : BitInput N) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)) :=
  let q:=(outer sources k clock).result.pcp.nativeWidth N
  let req:=request sources k clock input oracle
  limits q (oracleSizeBound oracleDegree q) req.arity
    (2^((selectedPCPP sources).output req).clauseBits)
    (clauseWidth degree q) copies (W q) delta

theorem actual_count_bound (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (oracleDegree : Nat)
    {N : Nat} (input : BitInput N) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N))
    (ho : oracle.size ≤ oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth N)) :
    variableCount sources k clock input oracle ≤ CloseoutSourceCounts.shortBound (selectedPCPP sources)
      (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
      ((outer sources k clock).result.pcp.nativeWidth N) :=
  (CloseoutSourceCounts.short_counts (selectedPCPP sources) oracle
    ((outer sources k clock).result.pcp.queryAddressBits input)
    ((outer sources k clock).result.pcp.decision input (fun _=>false))
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
    (selected_query_bound sources k clock N) ho).1

theorem actual_parameter_bound (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (oracleDegree degree copies : Nat)
    (W : Nat→Nat) (delta : ℚ) {N : Nat} (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N))
    (ho : oracle.size ≤ oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth N)) :
    recoveryWitnessCodeParameter (actual sources k clock oracleDegree degree copies W delta input oracle) ≤
      recoveryWitnessCodeParameter (envelope (selectedPCPP sources) (fixedProjection sources).coefficient
        (fixedProjection sources).degrees.queries oracleDegree degree copies W delta
        ((outer sources k clock).result.pcp.nativeWidth N)) := by
  have hm:=(CloseoutSourceCounts.short_counts (selectedPCPP sources) oracle
    ((outer sources k clock).result.pcp.queryAddressBits input)
    ((outer sources k clock).result.pcp.decision input (fun _=>false))
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
    (selected_query_bound sources k clock N) ho).2
  exact parameter_mono_count _ _ _ _ _ _ delta hm

theorem actual_family_sixteenth (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (oracleDegree degree copies : Nat)
    (W : Nat→Nat) (delta : ℚ) (hW : PolynomiallyBounded W) :
    ∃ onset, ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size ≤ oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
      ∀ w : FamilyWitness (actual sources k clock oracleDegree degree copies W delta input oracle)
        (variableCount sources k clock input), natBitLength w.code ≤ 2^s/16 := by
  let P (q : Nat):=recoveryWitnessCodeParameter (envelope (selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries
    oracleDegree degree copies W delta q)
  let V:=CloseoutSourceCounts.shortBound (selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
  have hP : PolynomiallyBounded P := envelope_polynomial _ _ _ _ _ _ W delta hW
  have hV : PolynomiallyBounded V := CloseoutSourceCounts.shortBound_polynomial _ _ _ _
  obtain ⟨C,e,_hC,he⟩:=CloseoutFamilyCode.uniform_envelope
  have hpoly:=CloseoutFamilyCode.envelope_polynomial C e P V hP hV
  obtain ⟨onset,honset⟩:=CloseoutFamilyCode.eventual_sixteenth
    (polynomiallyBounded_comp hpoly (native_dyadic_polynomial sources k clock))
  refine ⟨onset,?_⟩
  intro s hs input oracle ho w
  let q:=(outer sources k clock).result.pcp.nativeWidth (2^s)
  have hw : w.oracle.size ≤ oracleSizeBound oracleDegree q := by
    cases w with
    | symmetric _ h _=>exact h
    | threshold _ h _=>exact h
  have hcount : variableCount sources k clock input w.oracle ≤ V q :=
    actual_count_bound sources k clock oracleDegree input w.oracle hw
  have hp : recoveryWitnessCodeParameter
      (actual sources k clock oracleDegree degree copies W delta input oracle) ≤ P q :=
    actual_parameter_bound sources k clock oracleDegree degree copies W delta input oracle ho
  exact (CloseoutFamilyCode.code_bound w (V q) hcount).trans
    ((he _ (V q) (P q) hp).trans (honset s hs))

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
