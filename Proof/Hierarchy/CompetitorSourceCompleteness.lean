import Proof.Hierarchy.CompetitorSourceRecord

/-! Completeness uses the same faithful source's honest auxiliary proof and
the whole joint occurrence mean. A radius zeta pays the actual validity,
second-moment, and midpoint comparisons without a good-input density step. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces CompetitorRationalGap
open ComponentwiseBranchExtraction AggregateSemanticStage VerifierThresholdSeam
open Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def honestError (source : PointwisePCPPAlgorithm) (r : PCPPRequest source.minimumArity)
    (value : BitInput r.arity → Fin ((source.output r).systematicBits+(source.output r).auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput r.arity,clauseOccurrenceErrorMean (source.output r) (value input)
    (fun j => bitAsReal ((source.output r).assignment input ((source.output r).honestAuxiliary input) j))

theorem honest_total_error (source : PointwisePCPPAlgorithm) (r : PCPPRequest source.minimumArity)
    (value : BitInput r.arity → Fin ((source.output r).systematicBits+(source.output r).auxiliaryBits) → ℝ) :
    (𝔼 input : BitInput r.arity,totalClauseErrorMean (source.output r) (value input)
      (fun j => bitAsReal ((source.output r).assignment input ((source.output r).honestAuxiliary input) j)))=
      2*honestError source r value := by
  simp only [totalClauseErrorMean_eq_two_mul_occurrence,honestError,Finset.mul_expect]

theorem honest_estimates_pass (source : PointwisePCPPAlgorithm) (constants : Constants source)
    (r : PCPPRequest source.minimumArity) (hyes : ∀ input,r.circuit.eval input=true)
    (value : BitInput r.arity → Fin ((source.output r).systematicBits+(source.output r).auxiliaryBits) → ℝ)
    (hzero : ∀ input j,0 ≤ value input j) (hone : ∀ input j,value input j ≤ 1)
    (herror : honestError source r value ≤ (zeta constants : ℝ))
    (penaltyEstimate momentEstimate estimate : ℝ)
    (hpenaltyAccurate : |penaltyEstimate-aggregateClausePenaltyMean (source.output r) value/2| ≤
      estimationTolerance constants (zeta constants))
    (hmomentAccurate : |momentEstimate-leftSecondMoment (source.output r) value| ≤
      estimationTolerance constants (zeta constants))
    (hclauseAccurate : |estimate-aggregateClauseMean (source.output r) value| ≤
      estimationTolerance constants (zeta constants)) :
    penaltyEstimate ≤ 2*(zeta constants : ℝ) ∧ momentEstimate ≤ 1+(zeta constants : ℝ) ∧
      (midpoint constants : ℝ) < estimate := by
  have ht : (estimationTolerance constants (zeta constants) : ℝ) ≤ zeta constants := by
    exact_mod_cast (full_error_budget constants).2.1
  have hz : 0 ≤ (zeta constants : ℝ) := by exact_mod_cast (zeta_positive constants).le
  have hp : aggregateClausePenaltyMean (source.output r) value ≤ 2*honestError source r value := by
    rw [←honest_total_error]
    exact Finset.expect_le_expect (fun input _ => totalClausePenaltyMean_le_totalClauseErrorMean
      (source.output r) input ((source.output r).honestAuxiliary input) (value input) (hzero input) (hone input))
  have hm : leftSecondMoment (source.output r) value ≤ 1 := by
    calc
      _ ≤ 𝔼 _slot : BitInput r.arity × Fin (2^(source.output r).clauseBits),(1 : ℝ) := by
        apply Finset.expect_le_expect
        intro slot _
        have h0 := hzero slot.1 (literalIndex ((source.output r).clauses slot.2).left)
        have h1 := hone slot.1 (literalIndex ((source.output r).clauses slot.2).left)
        nlinarith
      _ = 1 := Fintype.expect_const _
  have hmove : satisfiedMean source r (source.output r).honestAuxiliary-
      aggregateClauseMean (source.output r) value ≤ 2*honestError source r value := by
    rw [←honest_total_error]
    have hpoint (input : BitInput r.arity) :
        (source.output r).satisfiedFraction input ((source.output r).honestAuxiliary input)-
          clauseMean (source.output r) (value input) ≤
        totalClauseErrorMean (source.output r) (value input)
          (fun j => bitAsReal ((source.output r).assignment input ((source.output r).honestAuxiliary input) j)) := by
      have hbound := abs_clauseMean_sub_le_totalClauseErrorMean (source.output r) (value input)
        (fun j => bitAsReal ((source.output r).assignment input ((source.output r).honestAuxiliary input) j))
        (hzero input) (hone input)
        (fun j => by cases (source.output r).assignment input ((source.output r).honestAuxiliary input) j <;> norm_num [bitAsReal])
        (fun j => by cases (source.output r).assignment input ((source.output r).honestAuxiliary input) j <;> norm_num [bitAsReal])
      rw [clauseMean_bitAsReal_eq_satisfiedFraction] at hbound
      have h := (abs_le.mp hbound).1
      linarith
    have h := Finset.expect_le_expect (fun input (_ : input∈(univ : Finset (BitInput r.arity))) => hpoint input)
    simpa only [Finset.expect_sub_distrib,satisfiedMean,aggregateClauseMean] using h
  have hpa := (abs_le.mp hpenaltyAccurate).2
  have hma := (abs_le.mp hmomentAccurate).2
  have hca := (abs_le.mp hclauseAccurate).1
  refine ⟨by linarith,by linarith,?_⟩
  apply yes_branch_above_midpoint constants estimate
  have hcomplete := source_complete_average source r hyes
  have hupper := constants.upper
  have hs := Real.sq_sqrt (show 0 ≤ 12*(zeta constants : ℝ) by positivity)
  have hsn := Real.sqrt_nonneg (12*(zeta constants : ℝ))
  have hz1 := zeta_lt_one constants
  have hsmall : (zeta constants : ℝ) ≤ Real.sqrt (12*(zeta constants : ℝ)) := by nlinarith
  linarith

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
