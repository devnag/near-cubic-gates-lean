import Proof.Hierarchy.CompetitorRationalDecision
import Proof.Hierarchy.CompetitorRationalTolerance

/-! The actual scalar machine at the literal validity and midpoint tests.
Input fields are the already produced estimate numerator, its exact positive
denominator, the fixed rational threshold, and their paid width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdDecision
open LocalBitMultitape RepairSource RepairRepresentation
open RepairSource.CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def numerator (q : ℚ) : ℕ := q.num.natAbs
theorem threshold_fraction (q : ℚ) (hq : 0≤q) : (numerator q : ℚ)/q.den=q := by
  have hn : 0≤q.num := Rat.num_nonneg.mpr hq
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  have hcast : (numerator q : ℚ)=(q.num : ℚ) := by
    change (q.num.natAbs : ℚ)=(q.num : ℚ)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  rw [hcast]
  exact Rat.num_div_den q

def numbers (lower : Bool) (p n : ℕ) (q : ℚ) : Fin 4 → ℕ :=
  if lower then ![p,n,numerator q,0] else ![numerator q,0,p,n]
def leftDenominator (lower : Bool) (d : ℕ) (q : ℚ) : ℕ := if lower then d else q.den
def rightDenominator (lower : Bool) (d : ℕ) (q : ℚ) : ℕ := if lower then q.den else d
def input (lower : Bool) (b p n d : ℕ) (q : ℚ) : Fin 67 → List Bool :=
  CompetitorRationalProducts.input (CompetitorRationalDecision.width b) b (numbers lower p n q)
    (leftDenominator lower d q) (rightDenominator lower d q)
def estimate (p n d : ℕ) : ℚ := ((p : ℚ)-n)/d
def passes (lower : Bool) (p n d : ℕ) (q : ℚ) : Prop :=
  if lower then q≤estimate p n d else estimate p n d≤q

theorem threshold_run (lower : Bool) (b p n d : ℕ) (q : ℚ)
    (hp : p<2^b) (hn : n<2^b) (hd : d<2^b) (hdpos : 0<d)
    (hq : 0≤q) (hqnum : numerator q<2^b) (hqden : q.den<2^b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalDecision.machine (2000*(b+1)^2)
      (input lower b p n d q) out ∧
      (readTapeBit (out 65) 0=true ↔ passes lower p n d q) := by
  have hnums : ∀ i,numbers lower p n q i<2^b := by
    intro i
    cases lower <;> fin_cases i <;> simp only [numbers,Bool.false_eq_true,if_false,if_true]
    all_goals first | exact hp | exact hn | exact hqnum | positivity
  have hl : leftDenominator lower d q<2^b := by cases lower <;> assumption
  have hr : rightDenominator lower d q<2^b := by cases lower <;> assumption
  have hlpos : 0<leftDenominator lower d q := by
    cases lower
    · exact q.pos
    · exact hdpos
  have hrpos : 0<rightDenominator lower d q := by
    cases lower
    · exact hdpos
    · exact q.pos
  obtain ⟨out,hrun,_,hresult⟩ := CompetitorRationalDecision.rational_decision_run b
    (numbers lower p n q) (leftDenominator lower d q) (rightDenominator lower d q)
    hnums hl hr hlpos hrpos
  refine ⟨out,hrun,?_⟩
  cases lower <;> simpa [numbers,leftDenominator,rightDenominator,passes,estimate,
    threshold_fraction q hq] using hresult

abbrev acceptanceThreshold := @CompetitorRationalGap.midpoint

theorem midpoint_positive {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    0 < acceptanceThreshold constants := by
  have hs : 0<(constants.soundness : ℝ) := source.soundnessPositive.trans constants.lower
  have hs' : 0<constants.soundness := by exact_mod_cast hs
  have hc := constants.separation
  unfold acceptanceThreshold CompetitorRationalGap.midpoint
  linarith

theorem midpoint_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (b p n d : ℕ) (hp : p<2^b) (hn : n<2^b) (hd : d<2^b) (hdpos : 0<d)
    (hqnum : numerator (acceptanceThreshold constants)<2^b) (hqden : (acceptanceThreshold constants).den<2^b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalDecision.machine (2000*(b+1)^2)
      (input true b p n d (acceptanceThreshold constants)) out ∧
      (readTapeBit (out 65) 0=true ↔ acceptanceThreshold constants≤estimate p n d) :=
  threshold_run true b p n d (acceptanceThreshold constants) hp hn hd hdpos
    (midpoint_positive constants).le hqnum hqden

theorem validity_mean_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (b p n d : ℕ) (hp : p<2^b) (hn : n<2^b) (hd : d<2^b) (hdpos : 0<d)
    (hqnum : numerator (meanThreshold constants)<2^b) (hqden : (meanThreshold constants).den<2^b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalDecision.machine (2000*(b+1)^2)
      (input false b p n d (meanThreshold constants)) out ∧
      (readTapeBit (out 65) 0=true ↔ estimate p n d≤2*zeta constants) := by
  exact threshold_run false b p n d (meanThreshold constants) hp hn hd hdpos
    (by unfold meanThreshold; exact mul_nonneg (by norm_num) (zeta_positive constants).le)
    hqnum hqden

theorem validity_moment_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (b p n d : ℕ) (hp : p<2^b) (hn : n<2^b) (hd : d<2^b) (hdpos : 0<d)
    (hqnum : numerator (momentThreshold constants)<2^b) (hqden : (momentThreshold constants).den<2^b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalDecision.machine (2000*(b+1)^2)
      (input false b p n d (momentThreshold constants)) out ∧
      (readTapeBit (out 65) 0=true ↔ estimate p n d≤1+zeta constants) := by
  exact threshold_run false b p n d (momentThreshold constants) hp hn hd hdpos
    (by unfold momentThreshold; linarith [zeta_positive constants]) hqnum hqden

end NearCubicWires.RepairOrdinary.CompetitorThresholdDecision
