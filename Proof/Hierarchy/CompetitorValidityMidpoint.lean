import Proof.Hierarchy.CompetitorValidityEntry

/-! Literal C.10 decision parent: the mean test, every second-moment test,
and the acceptance midpoint are one executed ordinary list computation.
Its input records contain the actually produced exact signed fractions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RepairRepresentation RepairSource
open RepairSource.CompetitorRationalGap CompetitorThresholdDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Estimate where
  positive : ℕ
  negative : ℕ
  denominator : ℕ
def Estimate.value (a : Estimate) : ℚ := ((a.positive : ℚ)-a.negative)/a.denominator
structure Estimate.Valid (a : Estimate) (b : ℕ) : Prop where
  positive : a.positive<2^b
  negative : a.negative<2^b
  denominator : a.denominator<2^b
  denominatorPositive : 0<a.denominator
def thresholdRecord (lower : Bool) (a : Estimate) (q : ℚ) : Comparison :=
  ⟨numbers lower a.positive a.negative q,leftDenominator lower a.denominator q,
    rightDenominator lower a.denominator q⟩

theorem thresholdRecord_passes (lower : Bool) (a : Estimate) (q : ℚ) (hq : 0≤q) :
    (thresholdRecord lower a q).passes ↔ if lower then q≤a.value else a.value≤q := by
  cases lower <;> simp [thresholdRecord,Comparison.passes,numbers,leftDenominator,rightDenominator,
    Estimate.value,threshold_fraction q hq]

theorem thresholdRecord_valid (lower : Bool) (a : Estimate) (q : ℚ) (b : ℕ)
    (ha : a.Valid b) (hn : numerator q<2^b) (hd : q.den<2^b) :
    (thresholdRecord lower a q).Valid b := by
  constructor
  · intro i
    cases lower <;> fin_cases i <;> simp only [thresholdRecord,numbers,Bool.false_eq_true,if_false,if_true]
    all_goals first | exact ha.positive | exact ha.negative | exact hn | positivity
  · cases lower
    · exact hd
    · exact ha.denominator
  · cases lower
    · exact ha.denominator
    · exact hd
  · cases lower
    · exact q.pos
    · exact ha.denominatorPositive
  · cases lower
    · exact ha.denominatorPositive
    · exact q.pos

def tests {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (mean : Estimate) (moments : List Estimate) (clauses : Estimate) : List Comparison :=
  thresholdRecord false mean (meanThreshold constants) ::
    moments.map (fun a => thresholdRecord false a (momentThreshold constants)) ++
      [thresholdRecord true clauses (acceptanceThreshold constants)]

theorem tests_passes {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (mean : Estimate) (moments : List Estimate) (clauses : Estimate) :
    (∀ a∈tests constants mean moments clauses,a.passes) ↔
      mean.value≤2*zeta constants ∧ (∀ a∈moments,a.value≤1+zeta constants) ∧
        acceptanceThreshold constants≤clauses.value := by
  have hmean : 0 ≤ meanThreshold constants := by
    unfold meanThreshold
    exact mul_nonneg (by norm_num) (zeta_positive constants).le
  have hmoment : 0 ≤ momentThreshold constants := by
    unfold momentThreshold
    linarith [zeta_positive constants]
  have hm : (thresholdRecord false mean (meanThreshold constants)).passes ↔ mean.value≤2*zeta constants :=
    thresholdRecord_passes false mean _ hmean
  have hq (a : Estimate) : (thresholdRecord false a (momentThreshold constants)).passes ↔
      a.value≤1+zeta constants := thresholdRecord_passes false a _ hmoment
  have hc : (thresholdRecord true clauses (acceptanceThreshold constants)).passes ↔
      acceptanceThreshold constants≤clauses.value :=
    thresholdRecord_passes true clauses _ (midpoint_positive constants).le
  constructor
  · intro h
    refine ⟨hm.mp (h _ (by simp [tests])),?_,hc.mp (h _ (by simp [tests]))⟩
    intro a ha
    apply (hq a).mp
    apply h
    have hmem : thresholdRecord false a (momentThreshold constants)∈
        moments.map (fun a => thresholdRecord false a (momentThreshold constants)) :=
      List.mem_map.mpr ⟨a,ha,rfl⟩
    simp [tests,hmem]
  · rintro ⟨hmean',hmoments,hclauses⟩ a ha
    have ha' : a=thresholdRecord false mean (meanThreshold constants) ∨
        (∃ x∈moments,thresholdRecord false x (momentThreshold constants)=a) ∨
        a=thresholdRecord true clauses (acceptanceThreshold constants) := by
      simpa [tests,List.mem_append,List.mem_map,or_assoc] using ha
    rcases ha' with ha|⟨x,hx,ha⟩|ha
    · subst a
      exact hm.mpr hmean'
    · subst a
      exact (hq x).mpr (hmoments x hx)
    · subst a
      exact hc.mpr hclauses

structure ThresholdWidths {source : PointwisePCPPAlgorithm} (constants : Constants source) (b : ℕ) : Prop where
  meanNumerator : numerator (meanThreshold constants)<2^b
  meanDenominator : (meanThreshold constants).den<2^b
  momentNumerator : numerator (momentThreshold constants)<2^b
  momentDenominator : (momentThreshold constants).den<2^b
  midpointNumerator : numerator (acceptanceThreshold constants)<2^b
  midpointDenominator : (acceptanceThreshold constants).den<2^b

theorem tests_valid {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (mean : Estimate) (moments : List Estimate) (clauses : Estimate) (b : ℕ)
    (hw : ThresholdWidths constants b) (hmean : mean.Valid b)
    (hmoments : ∀ a∈moments,a.Valid b) (hclauses : clauses.Valid b) :
    ∀ a∈tests constants mean moments clauses,a.Valid b := by
  intro a ha
  have ha' : a=thresholdRecord false mean (meanThreshold constants) ∨
      (∃ x∈moments,thresholdRecord false x (momentThreshold constants)=a) ∨
      a=thresholdRecord true clauses (acceptanceThreshold constants) := by
    simpa [tests,List.mem_append,List.mem_map,or_assoc] using ha
  rcases ha' with ha|⟨x,hx,ha⟩|ha
  · subst a
    exact thresholdRecord_valid false mean _ b hmean hw.meanNumerator hw.meanDenominator
  · subst a
    exact thresholdRecord_valid false x _ b (hmoments x hx) hw.momentNumerator hw.momentDenominator
  · subst a
    exact thresholdRecord_valid true clauses _ b hclauses hw.midpointNumerator hw.midpointDenominator

theorem validity_midpoint_run {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (mean : Estimate) (moments : List Estimate) (clauses : Estimate) (b : ℕ)
    (hw : ThresholdWidths constants b) (hmean : mean.Valid b)
    (hmoments : ∀ a∈moments,a.Valid b) (hclauses : clauses.Valid b) :
    ∃ r,run CompetitorValidityEntry.machine
        ((moments.length+2)*(11000*(b+1)^2+3)+5)
        (CompetitorValidityEntry.input b (tests constants mean moments clauses))=some r ∧
      r.steps≤(moments.length+2)*(11000*(b+1)^2+3)+5 ∧
      (r.final.control=CompetitorValidityEntry.success ↔
        mean.value≤2*zeta constants ∧ (∀ a∈moments,a.value≤1+zeta constants) ∧
          acceptanceThreshold constants≤clauses.value) := by
  obtain ⟨r,hr,hs,haccept⟩ := CompetitorValidityEntry.validity_entry_run b
    (tests constants mean moments clauses) (tests_valid constants mean moments clauses b hw hmean hmoments hclauses)
  refine ⟨r,?_,?_,haccept.trans (tests_passes constants mean moments clauses)⟩
  · simpa [CompetitorValidityEntry.budget,recordBudget,tests,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
  · simpa [CompetitorValidityEntry.budget,recordBudget,tests,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

end NearCubicWires.RepairOrdinary.CompetitorValidity
