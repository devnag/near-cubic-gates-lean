import Proof.Hierarchy.CompetitorSourceValidity

/-! All three accurate aggregate estimates now imply rejection on ordinary
hierarchy-NO inputs. In particular the witness value family is unrestricted;
the second-moment test pays for its rounding in the same joint distribution. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces CompetitorRationalGap
open ComponentwiseBranchExtraction AggregateSemanticStage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ordinary_estimate_below {T : ℕ → ℕ} {H : OrdinaryHierarchy T}
    {degrees : PCPDegrees} (P : OrdinaryPCPResult H degrees)
    (source : PointwisePCPPAlgorithm) (constants : Constants source) :
    ∃ onset : ℕ,1 ≤ onset ∧ ∀ n,onset ≤ n → ∀ (x : BitInput n)
      (oracle : BooleanCircuit (P.pcp.nativeWidth n)),H.timedView.accepts n x=false →
      let pcpp := source.output (PCPPSubstitution.sourceRequest source oracle
        (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))
      ∀ (value : BitInput (PCPPRequestBoundary.domain source (P.pcp.nativeWidth n)) →
        Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ)
        (penaltyEstimate momentEstimate estimate : ℝ),
      penaltyEstimate ≤ 2*(zeta constants : ℝ) →
      momentEstimate ≤ 1+(zeta constants : ℝ) →
      |penaltyEstimate-aggregateClausePenaltyMean pcpp value/2| ≤
        estimationTolerance constants (zeta constants) →
      |momentEstimate-leftSecondMoment pcpp value| ≤
        estimationTolerance constants (zeta constants) →
      |estimate-aggregateClauseMean pcpp value| ≤
        estimationTolerance constants (zeta constants) →
      estimate < (midpoint constants : ℝ) := by
  obtain ⟨onset,honset,hbelow⟩ := ordinary_no_below_midpoint P source constants
  refine ⟨onset,honset,?_⟩
  intro n hn x oracle hno
  dsimp only
  intro value penaltyEstimate momentEstimate estimate hp hm hpa hma hea
  let pcpp := source.output (PCPPSubstitution.sourceRequest source oracle
    (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))
  have hround := tests_rounding_bound constants pcpp value penaltyEstimate momentEstimate hp hm hpa hma
  have hr := (abs_le.mp hround).2
  rw [aggregateRoundedMean_eq_expect_satisfiedFraction] at hr
  have he := (abs_le.mp hea).2
  apply hbelow n hn x oracle hno (fun u => roundedAuxiliary pcpp (value u)) estimate
  unfold satisfiedMean
  linarith

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
