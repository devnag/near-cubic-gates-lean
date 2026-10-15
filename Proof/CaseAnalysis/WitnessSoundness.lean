import Proof.Hierarchy.CompetitorSourceTests

/-! The weak verifier's rejection cutoff is fixed from the PCPP reserve
before any hierarchy or refuter is selected. The value family is unrestricted. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Soundness
open RepairSource RepairRepresentation SourceInterfaces CompetitorRationalGap
open CompetitorSourceAverage ComponentwiseBranchExtraction AggregateSemanticStage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def cutoff {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℕ:=
  (outer_error_onset constants).choose

theorem cutoff_positive {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    1 ≤ cutoff constants:=(outer_error_onset constants).choose_spec.1

theorem below {source : PointwisePCPPAlgorithm} (constants : Constants source)
    {T : ℕ→ℕ} {H : OrdinaryHierarchy T} {degrees : PCPDegrees} (P : OrdinaryPCPResult H degrees)
    {n : ℕ} (hn:cutoff constants≤n) (x : BitInput n) (oracle : BooleanCircuit (P.pcp.nativeWidth n))
    (hno:H.timedView.accepts n x=false) :
    let r:=PCPPSubstitution.sourceRequest source oracle
      (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false))
    let pcpp:=source.output r
    ∀ (value : BitInput r.arity→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ)
      (penaltyEstimate momentEstimate estimate : ℝ),
      penaltyEstimate≤2*(zeta constants : ℝ) → momentEstimate≤1+(zeta constants : ℝ) →
      |penaltyEstimate-aggregateClausePenaltyMean pcpp value/2|≤estimationTolerance constants (zeta constants) →
      |momentEstimate-leftSecondMoment pcpp value|≤estimationTolerance constants (zeta constants) →
      |estimate-aggregateClauseMean pcpp value|≤estimationTolerance constants (zeta constants) →
      estimate<(midpoint constants : ℝ) := by
  dsimp only
  intro value penaltyEstimate momentEstimate estimate hp hm hpa hma hea
  let r:=PCPPSubstitution.sourceRequest source oracle
    (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false))
  let pcpp:=source.output r
  have hround:=tests_rounding_bound constants pcpp value penaltyEstimate momentEstimate hp hm hpa hma
  have hr:=(abs_le.mp hround).2
  rw [aggregateRoundedMean_eq_expect_satisfiedFraction] at hr
  have he:=(abs_le.mp hea).2
  have hs:=ordinary_no_average P source x oracle ((cutoff_positive constants).trans hn) hno
    (fun u=>roundedAuxiliary pcpp (value u))
  have reserve:source.soundness+1/(n : ℝ)^10≤(constants.soundness : ℝ):=
    (outer_error_onset constants).choose_spec.2 n hn
  apply no_branch_below_midpoint constants estimate
  unfold satisfiedMean at hs
  linarith

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.Soundness
