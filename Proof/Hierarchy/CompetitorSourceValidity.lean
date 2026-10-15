import Proof.Hierarchy.CompetitorSourceMidpoint
import Proof.Circuits.AggregateSemanticStage

/-! The guessed real proof need not lie pointwise in [0,1]. Its actual
aggregate penalty and second-moment tests suffice for prescribed rounding.
These are the joint PCPP-input/clause means used by the scalar records. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces CompetitorRationalGap
open ComponentwiseValidity ComponentwiseBranchExtraction AggregateSemanticStage
open Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def leftSecondMoment {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : BitInput n → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 slot : BitInput n × Fin (2^pcpp.clauseBits),
    value slot.1 (literalIndex (pcpp.clauses slot.2).left)^2

theorem aggregate_close_of_second_moment {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : BitInput n → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ)
    (z : ℝ) (hz : 0 ≤ z) (hsecond : leftSecondMoment pcpp value ≤ 4)
    (hpenalty : aggregateClausePenaltyMean pcpp value ≤ 6*z) :
    |aggregateClauseMean pcpp value-aggregateRoundedMean pcpp value| ≤ 6*Real.sqrt (12*z) := by
  classical
  let index := (univ : Finset (BitInput n × Fin (2^pcpp.clauseBits)))
  have hne : index.Nonempty := ⟨((fun _=>false),⟨0,by positivity⟩),mem_univ _⟩
  let left := fun slot : BitInput n × Fin (2^pcpp.clauseBits) =>
    value slot.1 (literalIndex (pcpp.clauses slot.2).left)
  let right := fun slot : BitInput n × Fin (2^pcpp.clauseBits) =>
    value slot.1 (literalIndex (pcpp.clauses slot.2).right)
  let lc := fun slot : BitInput n × Fin (2^pcpp.clauseBits) =>
    systematicConstraint pcpp slot.1 (literalIndex (pcpp.clauses slot.2).left)
  let rc := fun slot : BitInput n × Fin (2^pcpp.clauseBits) =>
    systematicConstraint pcpp slot.1 (literalIndex (pcpp.clauses slot.2).right)
  have hp : (𝔼 slot ∈ index,validityPenalty (lc slot) (left slot))+
      (𝔼 slot ∈ index,validityPenalty (rc slot) (right slot))=
      aggregateClausePenaltyMean pcpp value := by
    dsimp [index,left,right,lc,rc]
    rw [←Finset.expect_add_distrib,←Finset.univ_product_univ,Finset.expect_product]
    unfold aggregateClausePenaltyMean totalClausePenaltyMean clausePenaltyMean
    simp only [Finset.expect_add_distrib]
  have hl := validityRound_meanSquare_le index lc left
  have hr := validityRound_meanSquare_le index rc right
  have hsqrt : (Real.sqrt (12*z))^2=12*z := Real.sq_sqrt (by positivity)
  have hcombined :
      (𝔼 slot ∈ index,(left slot-bitAsReal (validityRound (lc slot) (left slot)))^2)+
      (𝔼 slot ∈ index,(right slot-bitAsReal (validityRound (rc slot) (right slot)))^2) ≤
      2*(Real.sqrt (12*z))^2 := by
    rw [hsqrt]
    linarith
  have hbound := clauseMean_distance_le_six_of_combined index hne
    (fun slot => literalNegated (pcpp.clauses slot.2).left)
    (fun slot => literalNegated (pcpp.clauses slot.2).right) left right
    (fun slot => validityRound (lc slot) (left slot))
    (fun slot => validityRound (rc slot) (right slot))
    (Real.sqrt (12*z)) (Real.sqrt_nonneg _) hsecond hcombined
  rw [aggregateClauseMean_eq_joint,aggregateRoundedMean_eq_joint,←Finset.expect_sub_distrib]
  exact (Finset.abs_expect_le _ _).trans hbound

theorem zeta_lt_one {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    (zeta constants : ℝ) < 1 := by
  have hs : 0 < (constants.soundness : ℝ) := source.soundnessPositive.trans constants.lower
  have hc : (constants.completeness : ℝ) < 1 := constants.upper.trans source.completenessBelowOne
  have hg : (constants.soundness : ℝ) < constants.completeness := by exact_mod_cast constants.separation
  have hsquare : ((constants.completeness : ℝ)-constants.soundness)^2 < 1 := by nlinarith
  simp only [zeta,gap,Rat.cast_div,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat]
  linarith

theorem tests_rounding_bound {source : PointwisePCPPAlgorithm} (constants : Constants source)
    {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value : BitInput n → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ)
    (penaltyEstimate momentEstimate : ℝ)
    (hpenaltyPass : penaltyEstimate ≤ 2*(zeta constants : ℝ))
    (hmomentPass : momentEstimate ≤ 1+(zeta constants : ℝ))
    (hpenaltyAccurate : |penaltyEstimate-aggregateClausePenaltyMean pcpp value/2| ≤
      estimationTolerance constants (zeta constants))
    (hmomentAccurate : |momentEstimate-leftSecondMoment pcpp value| ≤
      estimationTolerance constants (zeta constants)) :
    |aggregateClauseMean pcpp value-aggregateRoundedMean pcpp value| ≤
      6*Real.sqrt (12*(zeta constants : ℝ)) := by
  have hz : 0 ≤ (zeta constants : ℝ) := by exact_mod_cast (zeta_positive constants).le
  have ht : (estimationTolerance constants (zeta constants) : ℝ) ≤ zeta constants := by
    exact_mod_cast (full_error_budget constants).2.1
  have hp := (abs_le.mp hpenaltyAccurate).1
  have hm := (abs_le.mp hmomentAccurate).1
  apply aggregate_close_of_second_moment pcpp value _ hz
  · have hz1 := zeta_lt_one constants
    linarith
  · linarith

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
