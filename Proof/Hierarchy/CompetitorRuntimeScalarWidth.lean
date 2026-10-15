import Proof.Hierarchy.CompetitorMonomialTermProducer

/-! Fixed threshold-print width and runtime scalar width are independent.
The one finite decision machine is chosen with the threshold; all later
input widths and term counts only affect the physical tapes and clock. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource RepairRepresentation RepairSource.CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def runtimeWidth (n k l : ℕ) := CompetitorSumWidth.width n (k+l)

theorem valid_widen (k l : ℕ) (a : CompetitorValidity.Estimate) (ha : a.Valid k) : a.Valid (k+l) := by
  have hpow : 2^k≤(2:ℕ)^(k+l) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨ha.positive.trans_le hpow,ha.negative.trans_le hpow,ha.denominator.trans_le hpow,ha.denominatorPositive⟩

theorem runtime_decision_run (lower : Bool) (l : ℕ) (q : ℚ) (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ r,run (machine lower l q) (budget (runtimeWidth xs.length k l) l xs.length)
        (input (runtimeWidth xs.length k l) xs)=some r ∧
      r.steps≤budget (runtimeWidth xs.length k l) l xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ passes lower q xs) := by
  have htrace := CompetitorSumWidth.uniform_trace (k+l) xs (fun a ha => valid_widen k l a (hv a ha))
  exact cold_decision_run lower (runtimeWidth xs.length k l) l q xs
    (by unfold runtimeWidth CompetitorSumWidth.width; nlinarith) htrace hq
    (by unfold runtimeWidth CompetitorSumWidth.width; nlinarith) hp hd

theorem runtime_midpoint_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l : ℕ) (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l) (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k) :
    ∃ r,run (machine true l (midpoint constants)) (budget (runtimeWidth xs.length k l) l xs.length)
        (input (runtimeWidth xs.length k l) xs)=some r ∧
      r.steps≤budget (runtimeWidth xs.length k l) l xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ midpoint constants≤(xs.map CompetitorValidity.Estimate.value).sum) :=
  runtime_decision_run true l (midpoint constants) k xs hv (CompetitorThresholdDecision.midpoint_positive constants).le hp hd

theorem runtime_midpoint_no {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l : ℕ) (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l) (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k)
    (hestimate : ((xs.map CompetitorValidity.Estimate.value).sum : ℝ)≤(constants.soundness : ℝ)+
      estimationTolerance constants (zeta constants)+6*Real.sqrt (12*(zeta constants : ℝ))) :
    ∃ r,run (machine true l (midpoint constants)) (budget (runtimeWidth xs.length k l) l xs.length)
        (input (runtimeWidth xs.length k l) xs)=some r ∧
      r.steps≤budget (runtimeWidth xs.length k l) l xs.length ∧ r.final.heads 65=0 ∧
      readTapeBit (r.final.tapes 65) 0=false := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := runtime_midpoint_run constants l hp hd k xs hv
  have hmargin := no_branch_below_midpoint constants _ hestimate
  have hnot : ¬midpoint constants≤(xs.map CompetitorValidity.Estimate.value).sum := by
    intro h
    have hreal : (midpoint constants : ℝ)≤((xs.map CompetitorValidity.Estimate.value).sum : ℝ) := by exact_mod_cast h
    exact (not_le_of_gt hmargin) hreal
  refine ⟨r,hr,hs,hh,?_⟩
  cases he : readTapeBit (r.final.tapes 65) 0 with
  | false => rfl
  | true => exact False.elim (hnot (hflag.mp he))

theorem runtime_midpoint_yes {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (l : ℕ) (hp : CompetitorThresholdDecision.numerator (midpoint constants)<2^l)
    (hd : (midpoint constants).den<2^l) (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k)
    (hestimate : (constants.completeness : ℝ)-estimationTolerance constants (zeta constants)-
      6*Real.sqrt (12*(zeta constants : ℝ))≤((xs.map CompetitorValidity.Estimate.value).sum : ℝ)) :
    ∃ r,run (machine true l (midpoint constants)) (budget (runtimeWidth xs.length k l) l xs.length)
        (input (runtimeWidth xs.length k l) xs)=some r ∧
      r.steps≤budget (runtimeWidth xs.length k l) l xs.length ∧ r.final.heads 65=0 ∧
      readTapeBit (r.final.tapes 65) 0=true := by
  obtain ⟨r,hr,hs,hh,hflag⟩ := runtime_midpoint_run constants l hp hd k xs hv
  have hmargin := yes_branch_above_midpoint constants _ hestimate
  have hlt : midpoint constants<(xs.map CompetitorValidity.Estimate.value).sum := by exact_mod_cast hmargin
  exact ⟨r,hr,hs,hh,hflag.mpr hlt.le⟩

end NearCubicWires.RepairOrdinary.CompetitorThresholdCold
