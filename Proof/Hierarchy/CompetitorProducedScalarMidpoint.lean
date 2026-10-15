import Proof.Hierarchy.CompetitorProducedScalarDecision

/-! The actual coefficient/count-stream midpoint consumer with the complete
componentwise validity and estimation error budget. The rational interior
gap narrows the same fixed PCPP witness before the weak machine is chosen. -/
namespace NearCubicWires.RepairOrdinary.CompetitorProducedScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound CompetitorMonomialStream
open RepairSource RepairRepresentation RepairSource.CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem produced_midpoint_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l b : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l) :
    ∃ r,run (machine true l (midpoint constants))
        (budget (commonWidth b l xs.length) l xs.length)
        (input b (commonWidth b l xs.length) xs)=some r ∧
      r.steps≤budget (commonWidth b l xs.length) l xs.length ∧ r.final.heads 155=0 ∧
      (readTapeBit (r.final.tapes 155) 0=true ↔ midpoint constants≤((contributions xs).map CompetitorValidity.Estimate.value).sum) :=
  runtime_run true l (midpoint constants) b xs hv
    (CompetitorThresholdDecision.midpoint_positive constants).le hp hd

theorem produced_midpoint_no {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l b : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l)
    (hestimate : (((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ)≤(constants.soundness : ℝ)+
      estimationTolerance constants (zeta constants)+6*Real.sqrt (12*(zeta constants : ℝ))) :
    ∃ r,run (machine true l (midpoint constants))
        (budget (commonWidth b l xs.length) l xs.length)
        (input b (commonWidth b l xs.length) xs)=some r ∧
      r.steps≤budget (commonWidth b l xs.length) l xs.length ∧ r.final.heads 155=0 ∧
      readTapeBit (r.final.tapes 155) 0=false := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := produced_midpoint_run constants l b xs hv hp hd
  have hmargin := no_branch_below_midpoint constants _ hestimate
  have hnot : ¬midpoint constants≤((contributions xs).map CompetitorValidity.Estimate.value).sum := by
    intro h
    have hreal : (midpoint constants : ℝ)≤(((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ) := by exact_mod_cast h
    exact (not_le_of_gt hmargin) hreal
  refine ⟨r,hr,hs,hh,?_⟩
  cases he : readTapeBit (r.final.tapes 155) 0 with
  | false => rfl
  | true => exact False.elim (hnot (hflag.mp he))

theorem produced_midpoint_yes {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l b : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l)
    (hestimate : (constants.completeness : ℝ)-estimationTolerance constants (zeta constants)-
      6*Real.sqrt (12*(zeta constants : ℝ))≤(((contributions xs).map CompetitorValidity.Estimate.value).sum : ℝ)) :
    ∃ r,run (machine true l (midpoint constants))
        (budget (commonWidth b l xs.length) l xs.length)
        (input b (commonWidth b l xs.length) xs)=some r ∧
      r.steps≤budget (commonWidth b l xs.length) l xs.length ∧ r.final.heads 155=0 ∧
      readTapeBit (r.final.tapes 155) 0=true := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := produced_midpoint_run constants l b xs hv hp hd
  have hmargin := yes_branch_above_midpoint constants _ hestimate
  have hlt : midpoint constants<((contributions xs).map CompetitorValidity.Estimate.value).sum := by exact_mod_cast hmargin
  exact ⟨r,hr,hs,hh,hflag.mpr hlt.le⟩

end NearCubicWires.RepairOrdinary.CompetitorProducedScalar
