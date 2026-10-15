import Proof.Hierarchy.CompetitorSourceTests
import Proof.Hierarchy.CompetitorRecordScalarBounds

/-! The actual cold record-stream comparator rejects on hierarchy-NO inputs
once the two actual validity estimates pass and all three joint estimates
are accurate. No caller-supplied sum, product, width driver, or sentinel is
used by this ordinary execution. Record production/guarding remains upstream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces CompetitorRationalGap
open LocalBitMultitape ComponentwiseBranchExtraction AggregateSemanticStage
open CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ordinary_record_reject {T : ℕ → ℕ} {H : OrdinaryHierarchy T}
    {degrees : PCPDegrees} (P : OrdinaryPCPResult H degrees)
    (source : PointwisePCPPAlgorithm) (constants : Constants source)
    (l : ℕ) (hp : CompetitorThresholdDecision.numerator (midpoint constants) < 2^l)
    (hd : (midpoint constants).den < 2^l) :
    ∃ onset : ℕ,1 ≤ onset ∧ ∀ n,onset ≤ n → ∀ (x : BitInput n)
      (oracle : BooleanCircuit (P.pcp.nativeWidth n)),H.timedView.accepts n x=false →
      let pcpp := source.output (PCPPSubstitution.sourceRequest source oracle
        (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))
      ∀ (value : BitInput (PCPPRequestBoundary.domain source (P.pcp.nativeWidth n)) →
        Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ)
        (b : ℕ) (xs : List Entry), (∀ a∈xs,a.Valid b) →
      ∀ (penaltyEstimate momentEstimate : ℝ),
      penaltyEstimate ≤ 2*(zeta constants : ℝ) →
      momentEstimate ≤ 1+(zeta constants : ℝ) →
      |penaltyEstimate-aggregateClausePenaltyMean pcpp value/2| ≤
        estimationTolerance constants (zeta constants) →
      |momentEstimate-leftSecondMoment pcpp value| ≤
        estimationTolerance constants (zeta constants) →
      |(((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ)-
        aggregateClauseMean pcpp value| ≤ estimationTolerance constants (zeta constants) →
      ∃ actual,run (CompetitorRecordScalar.machine true l (midpoint constants))
        (CompetitorRecordScalar.budget b l xs.length) (CompetitorRecordScalar.input b xs)=some actual ∧
        actual.steps ≤ 3536000*(xs.length+1)^3*(b+l+1)^2 ∧ actual.final.heads 205=0 ∧
        readTapeBit (actual.final.tapes 205) 0=false := by
  obtain ⟨onset,honset,hbelow⟩ := ordinary_estimate_below P source constants
  refine ⟨onset,honset,?_⟩
  intro n hn x oracle hno
  dsimp only
  intro value b xs hv penaltyEstimate momentEstimate hpPass hmPass hpa hma hca
  have hmargin := hbelow n hn x oracle hno value penaltyEstimate momentEstimate
    (((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ) hpPass hmPass hpa hma hca
  obtain ⟨actual,hr,hs,hh,hflag⟩ := CompetitorRecordScalar.runtime_run true l (midpoint constants)
    b xs hv (CompetitorThresholdDecision.midpoint_positive constants).le hp hd
  refine ⟨actual,hr,hs.trans (CompetitorRecordScalar.polynomial_bound b l xs.length),hh,?_⟩
  cases he : readTapeBit (actual.final.tapes 205) 0 with
  | false => rfl
  | true =>
    have hq : midpoint constants ≤ ((contributions xs).map CompetitorValidity.Estimate.value).sum :=
      hflag.mp he
    have hreal : (midpoint constants : ℝ) ≤
        (((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ) := by exact_mod_cast hq
    exact False.elim ((not_le_of_gt hmargin) hreal)

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
