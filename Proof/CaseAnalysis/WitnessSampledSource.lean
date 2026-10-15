import Proof.CaseAnalysis.WitnessDyadicEncoding
import Proof.Hierarchy.CompetitorSourceCompleteness

/-! The canonical accepting oracle makes every padded source request
assignment a YES input. The actual integer wire cap has a fixed polynomial
bound, as required by the eventual honest-witness encoding theorem. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open SourceInterfaces RepairSource RepairRepresentation SelectedRecoveryIntegration PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem accepting_request {T : ℕ→ℕ} {H : OrdinaryHierarchy T} {degrees : PCPDegrees}
    (P : OrdinaryPCPResult H degrees) (a : PointwisePCPPAlgorithm) {N : ℕ} (x : BitInput N)
    (oracle : BooleanCircuit (P.pcp.nativeWidth N))
    (accepts:∀ u,OuterPCPRecovery.acceptsOracleCircuit P.pcp x oracle u) :
    ∀ u,(PCPPSubstitution.sourceRequest a oracle (P.pcp.queryAddressBits x)
      (P.pcp.decision x (fun _=>false))).circuit.eval u=true := by
  intro u
  rw [PCPPSubstitution.sourceRequest_eval]
  rw [P.decisionIndependent N x (fun _=>false)
    (ProjectionPCPPadding.prefixBits (Nat.le_max_left (P.pcp.nativeWidth N) a.minimumArity) u)]
  exact accepts _

theorem selected_request_true (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (degree : ℕ) {N : ℕ} (x : BitInput N)
    (small : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree x) :
    ∀ u,(CloseoutWitnessPolicy.request sources k clock x
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree x small).circuit).circuit.eval u=true :=
  accepting_request (outer sources k clock).result (CloseoutLanguage.selectedPCPP sources) x _
    (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree x small).accepts

theorem wire_polynomial (e den : ℕ) : PolynomiallyBounded (LegalPolicy.W e den) :=
  polynomiallyBounded_mono (fun _=>Nat.div_le_self _ _)
    (polynomiallyBounded_pow polynomiallyBounded_id 3)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness
