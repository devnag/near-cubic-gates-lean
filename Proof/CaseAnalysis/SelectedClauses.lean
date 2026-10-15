import Proof.CaseAnalysis.ClauseWidth
import Proof.CaseAnalysis.Language

/-! Apply the short source bounds to the exact selected normalized PCP.
The common clause exponent and q-onset precede every hierarchy-clock choice. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary
open RecoveryScheduleEnvelope SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_query_bound (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (n : Nat) :
    (outer sources k clock).result.pcp.queryCount n ≤
      (fixedProjection sources).coefficient*
        ((outer sources k clock).result.pcp.nativeWidth n+1)^
          (fixedProjection sources).degrees.queries := Nat.le_refl _

theorem selected_clause_degree (sources : EightSources) (oracleDegree : Nat) :
    ∃ degree onset : Nat, 1 ≤ degree ∧
      ∀ (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (n : Nat) (input : BitInput n),
        let pcp:=(outer sources k clock).result.pcp
        let q:=pcp.nativeWidth n
        ∀ oracle : BooleanCircuit q, oracle.size ≤ oracleSizeBound oracleDegree q → onset ≤ q →
          let pcpp:=(selectedPCPP sources).output
            (PCPPSubstitution.sourceRequest (selectedPCPP sources) oracle (pcp.queryAddressBits input)
              (pcp.decision input (fun _=>false)))
          pcpp.systematicBits+pcpp.auxiliaryBits ≤ (q+2)^degree ∧
            pcpp.clauseBits ≤ clauseWidth degree q := by
  obtain ⟨degree,onset,hd,hbound⟩ := CloseoutSourceCounts.clause_degree (selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
  refine ⟨degree,onset,hd,?_⟩
  intro k clock n input pcp q oracle ho hq
  obtain ⟨hv,hc⟩ := CloseoutSourceCounts.short_counts (selectedPCPP sources) oracle
    ((outer sources k clock).result.pcp.queryAddressBits input)
    ((outer sources k clock).result.pcp.decision input (fun _=>false))
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries oracleDegree
    (selected_query_bound sources k clock n) ho
  obtain ⟨hp,hbits⟩ := hbound _ hq
  exact ⟨hv.trans hp,hbits _ hc⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
