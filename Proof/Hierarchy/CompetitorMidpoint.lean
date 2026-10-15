import Proof.Hierarchy.CompetitorColdThresholdDecision

/-! The actual cold scalar-stream midpoint consumer with the complete
componentwise validity and estimation error budget. The rational interior
gap narrows the same fixed PCPP witness before the weak machine is chosen. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource RepairRepresentation RepairSource.CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_midpoint_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (k : ℕ) (xs : List CompetitorValidity.Estimate) (hv : ∀ a∈xs,a.Valid k)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^k)
    (hd : (midpoint constants).den<2^k) :
    ∃ r,run (machine true k (midpoint constants))
        (budget (CompetitorSumWidth.width xs.length k) k xs.length)
        (input (CompetitorSumWidth.width xs.length k) xs)=some r ∧
      r.steps≤budget (CompetitorSumWidth.width xs.length k) k xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ midpoint constants≤(xs.map CompetitorValidity.Estimate.value).sum) :=
  uniform_cold_decision_run true k (midpoint constants) xs hv
    (CompetitorThresholdDecision.midpoint_positive constants).le hp hd

theorem cold_midpoint_no {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (k : ℕ) (xs : List CompetitorValidity.Estimate) (hv : ∀ a∈xs,a.Valid k)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^k)
    (hd : (midpoint constants).den<2^k)
    (hestimate : ((xs.map CompetitorValidity.Estimate.value).sum : ℝ)≤(constants.soundness : ℝ)+
      estimationTolerance constants (zeta constants)+6*Real.sqrt (12*(zeta constants : ℝ))) :
    ∃ r,run (machine true k (midpoint constants))
        (budget (CompetitorSumWidth.width xs.length k) k xs.length)
        (input (CompetitorSumWidth.width xs.length k) xs)=some r ∧
      r.steps≤budget (CompetitorSumWidth.width xs.length k) k xs.length ∧ r.final.heads 65=0 ∧
      readTapeBit (r.final.tapes 65) 0=false := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := cold_midpoint_run constants k xs hv hp hd
  have hmargin := no_branch_below_midpoint constants _ hestimate
  have hnot : ¬midpoint constants≤(xs.map CompetitorValidity.Estimate.value).sum := by
    intro h
    have hreal : (midpoint constants : ℝ)≤((xs.map CompetitorValidity.Estimate.value).sum : ℝ) := by exact_mod_cast h
    exact (not_le_of_gt hmargin) hreal
  refine ⟨r,hr,hs,hh,?_⟩
  cases he : readTapeBit (r.final.tapes 65) 0 with
  | false => rfl
  | true => exact False.elim (hnot (hflag.mp he))

theorem cold_midpoint_yes {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (k : ℕ) (xs : List CompetitorValidity.Estimate) (hv : ∀ a∈xs,a.Valid k)
    (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^k)
    (hd : (midpoint constants).den<2^k)
    (hestimate : (constants.completeness : ℝ)-estimationTolerance constants (zeta constants)-
      6*Real.sqrt (12*(zeta constants : ℝ))≤((xs.map CompetitorValidity.Estimate.value).sum : ℝ)) :
    ∃ r,run (machine true k (midpoint constants))
        (budget (CompetitorSumWidth.width xs.length k) k xs.length)
        (input (CompetitorSumWidth.width xs.length k) xs)=some r ∧
      r.steps≤budget (CompetitorSumWidth.width xs.length k) k xs.length ∧ r.final.heads 65=0 ∧
      readTapeBit (r.final.tapes 65) 0=true := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := cold_midpoint_run constants k xs hv hp hd
  have hmargin := yes_branch_above_midpoint constants _ hestimate
  have hlt : midpoint constants<(xs.map CompetitorValidity.Estimate.value).sum := by exact_mod_cast hmargin
  exact ⟨r,hr,hs,hh,hflag.mpr hlt.le⟩

end NearCubicWires.RepairOrdinary.CompetitorThresholdCold
