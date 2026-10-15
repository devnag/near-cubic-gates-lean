import Proof.Circuits.OccurrenceSliceTransport

namespace NearCubicWires.AggregateSemanticStage

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OccurrenceSliceTransport
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifierThresholdSeam

/-! ## §1 The aggregate quantities -/

/-- **The verifier's estimated quantity.**  The uniform mean, over the PCPP
input cube, of the arithmetized clause mean of the proof vector decoded at that
input.  This is the manuscript's `mu = E_{i,u} F_i(u)`. -/
noncomputable def aggregateClauseMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n, clauseMean pcpp (value input)

/-- **The verifier's charged validity quantity.**  The uniform mean, over the
PCPP input cube, of the per-input joint clause penalty.  This is the
manuscript's `E_{i,j,u} P_{ij}`, charged on both clause sides. -/
noncomputable def aggregateClausePenaltyMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n, totalClausePenaltyMean pcpp input (value input)

/-- The aggregate clause mean of the prescribed rounding of the same family. -/
noncomputable def aggregateRoundedMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n,
    clauseMean pcpp
      (fun j => bitAsReal (roundedProof pcpp input (value input) j))

/-- The joint cube is the product of the PCPP input cube with the clause
address space.  Every aggregate quantity above is one expectation over it. -/
private theorem expect_prod_eq {n bits : ℕ} (value : BitInput n → Fin bits → ℝ) :
    (𝔼 slot ∈ (univ : Finset (BitInput n × Fin bits)), value slot.1 slot.2) =
      𝔼 input : BitInput n,
        𝔼 index ∈ (univ : Finset (Fin bits)), value input index := by
  rw [← Finset.univ_product_univ, Finset.expect_product']

private theorem jointIndex_nonempty {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) :
    (univ :
        Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))).Nonempty :=
  ⟨((fun _ => false), ⟨0, by positivity⟩), Finset.mem_univ _⟩

theorem aggregateClauseMean_eq_joint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateClauseMean pcpp value =
      𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        clauseRealValue (pcpp.clauses slot.2) (value slot.1) :=
  (expect_prod_eq
    (fun input index => clauseRealValue (pcpp.clauses index) (value input))).symm

theorem aggregateRoundedMean_eq_joint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateRoundedMean pcpp value =
      𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        clauseRealValue (pcpp.clauses slot.2)
          (fun j =>
            bitAsReal (roundedProof pcpp slot.1 (value slot.1) j)) :=
  (expect_prod_eq
    (fun input index =>
      clauseRealValue (pcpp.clauses index)
        (fun j => bitAsReal (roundedProof pcpp input (value input) j)))).symm

/-- The aggregate validity charge, resolved on one clause side over the joint
cube. -/
private theorem aggregatePenaltySide_eq_joint {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (𝔼 input : BitInput n,
        clausePenaltyMean pcpp input (value input) side) =
      𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        validityPenalty
          (systematicConstraint pcpp slot.1
            (literalIndex (side (pcpp.clauses slot.2))))
          (value slot.1 (literalIndex (side (pcpp.clauses slot.2)))) :=
  (expect_prod_eq
    (fun input index =>
      validityPenalty
        (systematicConstraint pcpp input
          (literalIndex (side (pcpp.clauses index))))
        (value input (literalIndex (side (pcpp.clauses index)))))).symm

/-! ## §2 The aggregate validity movement bound

The manuscript's rounding lemma C.10.1(2) is exactly
`ComponentwiseValidity.clauseMean_distance_le_six_of_combined`, whose index set
is an abstract `Finset`.  Instantiating it at the joint cube is the whole
proof: no new Jensen step and no new constant. -/

private theorem aggregate_roundingSquare_le {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        (value slot.1 (literalIndex (side (pcpp.clauses slot.2))) -
          bitAsReal
            (roundedProof pcpp slot.1 (value slot.1)
              (literalIndex (side (pcpp.clauses slot.2))))) ^ 2) ≤
      4 *
        𝔼 input : BitInput n,
          clausePenaltyMean pcpp input (value input) side := by
  rw [aggregatePenaltySide_eq_joint pcpp value side]
  exact
    validityRound_meanSquare_le
      (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits)))
      (fun slot =>
        systematicConstraint pcpp slot.1
          (literalIndex (side (pcpp.clauses slot.2))))
      (fun slot =>
        value slot.1 (literalIndex (side (pcpp.clauses slot.2))))

private theorem aggregate_sq_le_four {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits))
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1) :
    (𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
      value slot.1 (literalIndex (side (pcpp.clauses slot.2))) ^ 2) ≤ 4 := by
  calc
    (𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        value slot.1 (literalIndex (side (pcpp.clauses slot.2))) ^ 2) ≤
        𝔼 _slot ∈
          (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))), (4 : ℝ) :=
      Finset.expect_le_expect fun slot _ => by
        have hzero :=
          hnonneg slot.1 (literalIndex (side (pcpp.clauses slot.2)))
        have hone :=
          hleOne slot.1 (literalIndex (side (pcpp.clauses slot.2)))
        nlinarith
    _ = 4 := Finset.expect_const (jointIndex_nonempty pcpp) 4

/-- **Aggregate validity.**  A verifier that charges the *aggregate* clause
penalty at most `6 * zeta` cannot move the *aggregate* clause mean by more than
the manuscript's `6 * sqrt (12 * zeta)`.  Every constant is the published one:
this is `clauseMean_close_of_penalty` with the joint cube in place of the
clause space. -/
theorem aggregateClauseMean_close_of_penalty {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (zeta : ℝ) (hzeta : 0 ≤ zeta)
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1)
    (hpenalty : aggregateClausePenaltyMean pcpp value ≤ 6 * zeta) :
    |aggregateClauseMean pcpp value - aggregateRoundedMean pcpp value| ≤
      6 * Real.sqrt (12 * zeta) := by
  classical
  set delta : ℝ := Real.sqrt (12 * zeta) with hdeltaDef
  have hdelta : 0 ≤ delta := Real.sqrt_nonneg _
  have hdeltaSquare : delta ^ 2 = 12 * zeta := by
    rw [hdeltaDef]
    exact Real.sq_sqrt (by linarith)
  have hsplit :
      aggregateClausePenaltyMean pcpp value =
        (𝔼 input : BitInput n,
            clausePenaltyMean pcpp input (value input)
              TwoLiteralClause.left) +
          𝔼 input : BitInput n,
            clausePenaltyMean pcpp input (value input)
              TwoLiteralClause.right := by
    rw [aggregateClausePenaltyMean, ← Finset.expect_add_distrib]
    rfl
  have hleftPenalty :=
    aggregate_roundingSquare_le pcpp value TwoLiteralClause.left
  have hrightPenalty :=
    aggregate_roundingSquare_le pcpp value TwoLiteralClause.right
  have hpenaltySplit :
      (𝔼 input : BitInput n,
            clausePenaltyMean pcpp input (value input)
              TwoLiteralClause.left) +
          (𝔼 input : BitInput n,
            clausePenaltyMean pcpp input (value input)
              TwoLiteralClause.right) ≤
        6 * zeta := by
    rw [← hsplit]
    exact hpenalty
  have hcombined :
      (𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
          (value slot.1 (literalIndex (pcpp.clauses slot.2).left) -
            bitAsReal
              (roundedProof pcpp slot.1 (value slot.1)
                (literalIndex (pcpp.clauses slot.2).left))) ^ 2) +
        (𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
          (value slot.1 (literalIndex (pcpp.clauses slot.2).right) -
            bitAsReal
              (roundedProof pcpp slot.1 (value slot.1)
                (literalIndex (pcpp.clauses slot.2).right))) ^ 2) ≤
        2 * delta ^ 2 := by
    rw [hdeltaSquare]
    linarith
  have hbound :=
    clauseMean_distance_le_six_of_combined
      (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits)))
      (jointIndex_nonempty pcpp)
      (fun slot => literalNegated (pcpp.clauses slot.2).left)
      (fun slot => literalNegated (pcpp.clauses slot.2).right)
      (fun slot => value slot.1 (literalIndex (pcpp.clauses slot.2).left))
      (fun slot => value slot.1 (literalIndex (pcpp.clauses slot.2).right))
      (fun slot =>
        roundedProof pcpp slot.1 (value slot.1)
          (literalIndex (pcpp.clauses slot.2).left))
      (fun slot =>
        roundedProof pcpp slot.1 (value slot.1)
          (literalIndex (pcpp.clauses slot.2).right))
      delta hdelta
      (aggregate_sq_le_four pcpp value TwoLiteralClause.left hnonneg hleOne)
      hcombined
  calc
    |aggregateClauseMean pcpp value - aggregateRoundedMean pcpp value| =
        |𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
          (clauseRealValue (pcpp.clauses slot.2) (value slot.1) -
            clauseRealValue (pcpp.clauses slot.2)
              (fun j =>
                bitAsReal (roundedProof pcpp slot.1 (value slot.1) j)))| := by
      rw [aggregateClauseMean_eq_joint, aggregateRoundedMean_eq_joint,
        Finset.expect_sub_distrib]
    _ ≤ 𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
          |clauseRealValue (pcpp.clauses slot.2) (value slot.1) -
            clauseRealValue (pcpp.clauses slot.2)
              (fun j =>
                bitAsReal (roundedProof pcpp slot.1 (value slot.1) j))| :=
      Finset.abs_expect_le _ _
    _ ≤ 6 * delta := hbound

/-! ## §3 The aggregate soundness bound

The manuscript's soundness sentence is a convexity split, not a Markov
argument: the outer PCP accepts on at most an `outerError` fraction of PCPP
inputs, every other input is bounded by pointwise PCPP soundness, and the mean
inherits the sum of the two. -/

/-- A `[0, 1]`-valued quantity that stays below `level` outside an exceptional
set of relative size `density` has mean at most `level + density`. -/
theorem expect_le_of_exceptionalSet {index : Type} [Fintype index]
    [Nonempty index] (value : index → ℝ) (exceptional : Finset index)
    (level density : ℝ) (hlevel : 0 ≤ level)
    (hleOne : ∀ i, value i ≤ 1)
    (hgood : ∀ i, i ∉ exceptional → value i ≤ level)
    (hdensity :
      (exceptional.card : ℝ) ≤ density * (Fintype.card index : ℝ)) :
    (𝔼 i, value i) ≤ level + density := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card index : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty index›
  have hsubset : exceptional ⊆ (univ : Finset index) := Finset.subset_univ _
  have hsum :
      (∑ i ∈ (univ : Finset index) \ exceptional, value i) +
          ∑ i ∈ exceptional, value i =
        ∑ i, value i :=
    Finset.sum_sdiff hsubset
  have houter :
      (∑ i ∈ exceptional, value i) ≤ (exceptional.card : ℝ) := by
    calc
      (∑ i ∈ exceptional, value i) ≤ ∑ _i ∈ exceptional, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hleOne i
      _ = (exceptional.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hinner :
      (∑ i ∈ (univ : Finset index) \ exceptional, value i) ≤
        level * (Fintype.card index : ℝ) := by
    calc
      (∑ i ∈ (univ : Finset index) \ exceptional, value i) ≤
          ∑ _i ∈ (univ : Finset index) \ exceptional, level :=
        Finset.sum_le_sum fun i hi =>
          hgood i (Finset.mem_sdiff.mp hi).2
      _ = (((univ : Finset index) \ exceptional).card : ℝ) * level := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card index : ℝ) * level := by
        refine mul_le_mul_of_nonneg_right ?_ hlevel
        exact_mod_cast
          (Finset.card_le_card (Finset.sdiff_subset)).trans_eq
            Finset.card_univ
      _ = level * (Fintype.card index : ℝ) := by ring
  have htotal :
      (∑ i, value i) ≤
        level * (Fintype.card index : ℝ) + density * (Fintype.card index : ℝ) := by
    rw [← hsum]
    linarith [houter.trans hdensity]
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ,
    div_le_iff₀ hcard]
  linarith

/-- The aggregate rounded mean is the aggregate satisfied fraction of the
prescribed rounding, which is a genuine PCPP assignment at every input. -/
theorem aggregateRoundedMean_eq_expect_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateRoundedMean pcpp value =
      𝔼 input : BitInput n,
        pcpp.satisfiedFraction input
          (roundedAuxiliary pcpp (value input)) := by
  refine Finset.expect_congr rfl fun input _ => ?_
  rw [roundedProof_eq_assignment pcpp input (value input),
    clauseMean_bitAsReal_eq_satisfiedFraction]

/-- **Aggregate soundness.**  On a hierarchy-NO word the substituted outer
circuit accepts on at most an `outerError` fraction of PCPP inputs; pointwise
PCPP soundness bounds every other input by `soundness`; the aggregate rounded
mean is therefore at most `soundness + outerError`.  This is the exact premise
`ExecutableNoInstanceBranchLedger.roundedSound` asks for, and it is derived by
a convexity split, with no Markov inequality. -/
theorem aggregateRoundedMean_le_of_exceptionalSet {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (outerAccepting : Finset (BitInput n)) (soundness density : ℝ)
    (hsoundness : 0 ≤ soundness)
    (hsound :
      ∀ input, input ∉ outerAccepting →
        ∀ auxiliary : BitInput pcpp.auxiliaryBits,
          pcpp.satisfiedFraction input auxiliary ≤ soundness)
    (hdensity :
      (outerAccepting.card : ℝ) ≤
        density * (Fintype.card (BitInput n) : ℝ)) :
    aggregateRoundedMean pcpp value ≤ soundness + density := by
  rw [aggregateRoundedMean_eq_expect_satisfiedFraction]
  exact
    expect_le_of_exceptionalSet
      (fun input =>
        pcpp.satisfiedFraction input (roundedAuxiliary pcpp (value input)))
      outerAccepting soundness density hsoundness
      (fun input =>
        pointwiseSatisfiedFraction_le_one pcpp input
          (roundedAuxiliary pcpp (value input)))
      (fun input hinput =>
        hsound input hinput (roundedAuxiliary pcpp (value input)))
      hdensity

/-! ## §4 The aggregate ledger and the one-sided closure

`ExecutableNoInstanceBranchLedger` stores three reals and four inequalities and
mentions no PCPP, no input and no clause index.  The aggregate quantities
instantiate it verbatim, so `executableNoInstanceBranchLedger_empty` — the
published numeric ladder — is reused with nothing changed. -/

/-- **The aggregate ledger.**  An accepting aggregate stage on a hierarchy-NO
word decodes to the published ledger. -/
noncomputable def aggregateNoInstanceBranchLedger {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1)
    (hvalidity :
      aggregateClausePenaltyMean pcpp value ≤ 6 * (parameters.zeta : ℝ))
    (hrounded :
      aggregateRoundedMean pcpp value ≤
        soundness + (parameters.outerError : ℝ))
    (haccurate :
      |estimate - aggregateClauseMean pcpp value| ≤
        (parameters.estimationError : ℝ))
    (haccepted : (parameters.threshold : ℝ) ≤ estimate) :
    ExecutableNoInstanceBranchLedger parameters where
  roundedMean := aggregateRoundedMean pcpp value
  realMean := aggregateClauseMean pcpp value
  estimate := estimate
  roundedSound := hrounded
  validityClose :=
    aggregateClauseMean_close_of_penalty pcpp value (parameters.zeta : ℝ)
      (by exact_mod_cast le_of_lt parameters.zetaPositive) hnonneg hleOne
      hvalidity
  estimateClose := haccurate
  accepted := haccepted

/-- **The semantic composition theorem.**  An aggregate stage that accepts on a
hierarchy-NO word is contradictory at the published constants. -/
theorem aggregateStage_rejects {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1)
    (hvalidity :
      aggregateClausePenaltyMean pcpp value ≤ 6 * (parameters.zeta : ℝ))
    (hrounded :
      aggregateRoundedMean pcpp value ≤
        soundness + (parameters.outerError : ℝ))
    (haccurate :
      |estimate - aggregateClauseMean pcpp value| ≤
        (parameters.estimationError : ℝ))
    (haccepted : (parameters.threshold : ℝ) ≤ estimate) : False :=
  (executableNoInstanceBranchLedger_empty parameters).false
    (aggregateNoInstanceBranchLedger pcpp parameters value estimate hnonneg
      hleOne hvalidity hrounded haccurate haccepted)

theorem aggregateStage_rejects_of_outerDensity {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ) (outerAccepting : Finset (BitInput n))
    (hsoundnessNonneg : 0 ≤ soundness)
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1)
    (hvalidity :
      aggregateClausePenaltyMean pcpp value ≤ 6 * (parameters.zeta : ℝ))
    (hsound :
      ∀ input, input ∉ outerAccepting →
        ∀ auxiliary : BitInput pcpp.auxiliaryBits,
          pcpp.satisfiedFraction input auxiliary ≤ soundness)
    (hdensity :
      (outerAccepting.card : ℝ) ≤
        (parameters.outerError : ℝ) * (Fintype.card (BitInput n) : ℝ))
    (haccurate :
      |estimate - aggregateClauseMean pcpp value| ≤
        (parameters.estimationError : ℝ))
    (haccepted : (parameters.threshold : ℝ) ≤ estimate) : False :=
  aggregateStage_rejects pcpp parameters value estimate hnonneg hleOne
    hvalidity
    (aggregateRoundedMean_le_of_exceptionalSet pcpp value outerAccepting
      soundness (parameters.outerError : ℝ) hsoundnessNonneg hsound hdensity)
    haccurate haccepted

theorem eventuallyOneSided_of_aggregateLedger {hierarchy : Language}
    {completeness soundness : ℝ}
    (machine : ExecutableWeakNondeterministicMachine)
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (onset : ℕ)
    (ledgerOfAcceptedBranch :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          machine.run n input witness →
            Nonempty (ExecutableNoInstanceBranchLedger parameters)) :
    EventuallyOneSided hierarchy machine :=
  eventuallyOneSided_of_executableBranchLedger machine parameters onset
    ledgerOfAcceptedBranch

/-! ## §5 Completeness from the whole-cube `ell^1` premise

The seam's movement bound `abs_clauseMean_sub_le_totalClauseErrorMean` is
linear in the error, so it averages over the PCPP input cube with no loss.  The
whole-cube radius the XOR contract publishes *is* the aggregate slice error
(`l1DistanceFromBoolean_eq_expect_slice`), so completeness closes directly. -/

private theorem zeta_le_sqrt_twelveZeta
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    (parameters.zeta : ℝ) ≤ Real.sqrt (12 * (parameters.zeta : ℝ)) := by
  have hzeta : (0 : ℝ) < (parameters.zeta : ℝ) := by
    exact_mod_cast parameters.zetaPositive
  have hsmall := parameters.zetaBelowThreeHalves
  have hsquare : (parameters.zeta : ℝ) ^ 2 ≤ 12 * (parameters.zeta : ℝ) := by
    nlinarith
  calc
    (parameters.zeta : ℝ) = Real.sqrt ((parameters.zeta : ℝ) ^ 2) :=
      (Real.sqrt_sq (le_of_lt hzeta)).symm
    _ ≤ Real.sqrt (12 * (parameters.zeta : ℝ)) :=
      Real.sqrt_le_sqrt hsquare

/-- **Aggregate completeness seam.**  A guessed proof family whose *aggregate*
clause-marginal `ell^1` budget against the honest assignments is at most
`6 * zeta` forces the verifier's final comparison at the published constants.
This is `VerifierThresholdSeam.threshold_le_estimate_of_clauseErrorBudget`
averaged over the PCPP input cube. -/
theorem threshold_le_estimate_of_aggregateErrorBudget {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (auxiliary : BitInput n → BitInput pcpp.auxiliaryBits)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ input j, 0 ≤ value input j)
    (hleOne : ∀ input j, value input j ≤ 1)
    (hhonest :
      ∀ input : BitInput n,
        completeness ≤
          clauseMean pcpp
            (fun j =>
              bitAsReal (pcpp.assignment input (auxiliary input) j)))
    (hbudget :
      (𝔼 input : BitInput n,
          totalClauseErrorMean pcpp (value input)
            (fun j =>
              bitAsReal (pcpp.assignment input (auxiliary input) j))) ≤
        6 * (parameters.zeta : ℝ))
    (haccurate :
      |estimate - aggregateClauseMean pcpp value| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate := by
  have hhonestMean :
      completeness ≤
        𝔼 input : BitInput n,
          clauseMean pcpp
            (fun j =>
              bitAsReal (pcpp.assignment input (auxiliary input) j)) := by
    calc
      completeness =
          𝔼 _input ∈ (univ : Finset (BitInput n)), completeness :=
        (Finset.expect_const Finset.univ_nonempty completeness).symm
      _ ≤ _ := Finset.expect_le_expect fun input _ => hhonest input
  have hmove :
      (𝔼 input : BitInput n,
          clauseMean pcpp
            (fun j =>
              bitAsReal (pcpp.assignment input (auxiliary input) j))) -
          aggregateClauseMean pcpp value ≤
        6 * (parameters.zeta : ℝ) := by
    have hpointwise :
        ∀ input ∈ (univ : Finset (BitInput n)),
          clauseMean pcpp
              (fun j =>
                bitAsReal (pcpp.assignment input (auxiliary input) j)) -
              clauseMean pcpp (value input) ≤
            totalClauseErrorMean pcpp (value input)
              (fun j =>
                bitAsReal (pcpp.assignment input (auxiliary input) j)) := by
      intro input _
      have hbound :=
        abs_clauseMean_sub_le_totalClauseErrorMean pcpp (value input)
          (fun j => bitAsReal (pcpp.assignment input (auxiliary input) j))
          (hnonneg input) (hleOne input)
          (fun j => by cases pcpp.assignment input (auxiliary input) j <;>
            norm_num [bitAsReal])
          (fun j => by cases pcpp.assignment input (auxiliary input) j <;>
            norm_num [bitAsReal])
      have := (abs_le.mp hbound).1
      linarith
    calc
      (𝔼 input : BitInput n,
            clauseMean pcpp
              (fun j =>
                bitAsReal (pcpp.assignment input (auxiliary input) j))) -
            aggregateClauseMean pcpp value =
          𝔼 input : BitInput n,
            (clauseMean pcpp
                (fun j =>
                  bitAsReal (pcpp.assignment input (auxiliary input) j)) -
              clauseMean pcpp (value input)) := by
        rw [aggregateClauseMean, Finset.expect_sub_distrib]
      _ ≤ 𝔼 input : BitInput n,
            totalClauseErrorMean pcpp (value input)
              (fun j =>
                bitAsReal (pcpp.assignment input (auxiliary input) j)) :=
        Finset.expect_le_expect hpointwise
      _ ≤ 6 * (parameters.zeta : ℝ) := hbudget
  have hestimateLower :
      aggregateClauseMean pcpp value - (parameters.estimationError : ℝ) ≤
        estimate := by
    have := (abs_le.mp haccurate).1
    linarith
  have hrounding :
      6 * (parameters.zeta : ℝ) ≤
        6 * Real.sqrt (12 * (parameters.zeta : ℝ)) := by
    have := zeta_le_sqrt_twelveZeta parameters
    linarith
  have hreserve := parameters.completenessReserve
  linarith

/-- **Aggregate completeness from the published radius.**  The XOR contract's
whole-cube `ell^1` premise is consumed *directly*: it is the aggregate slice
error, and the aggregate error budget is twice it.  No Markov inequality, no
density of admissible inputs and no majority is used, and the seam's
`delta <= 3 * zeta` budget is spent exactly once. -/
theorem threshold_le_estimate_of_aggregateL1Distance {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (delta estimate : ℝ)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hhonest :
      ∀ input : BitInput n,
        completeness ≤
          clauseMean pcpp
            (fun j =>
              bitAsReal
                (pcpp.assignment input (pcpp.honestAuxiliary input) j)))
    (hdelta : delta ≤ 3 * (parameters.zeta : ℝ))
    (hdistance :
      l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess ≤ delta)
    (haccurate :
      |estimate -
          aggregateClauseMean pcpp
            (fun input => recoveredProofValue pcpp guess input)| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate := by
  refine
    threshold_le_estimate_of_aggregateErrorBudget pcpp
      (fun input => pcpp.honestAuxiliary input) parameters
      (fun input => recoveredProofValue pcpp guess input) estimate
      (fun input j =>
        (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
          j).1)
      (fun input j =>
        (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
          j).2)
      hhonest ?_ haccurate
  have hslice :
      ∀ input ∈ (univ : Finset (BitInput n)),
        totalClauseErrorMean pcpp (recoveredProofValue pcpp guess input)
            (fun j =>
              bitAsReal
                (pcpp.assignment input (pcpp.honestAuxiliary input) j)) =
          2 *
            occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess
              input := by
    intro input _
    rw [totalClauseErrorMean_eq_two_mul_occurrence,
      clauseOccurrenceErrorMean_recoveredProofValue pcpp guess input hnonneg
        hleOne]
  calc
    (𝔼 input : BitInput n,
        totalClauseErrorMean pcpp (recoveredProofValue pcpp guess input)
          (fun j =>
            bitAsReal
              (pcpp.assignment input (pcpp.honestAuxiliary input) j))) =
        𝔼 input : BitInput n,
          2 *
            occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess
              input :=
      Finset.expect_congr rfl hslice
    _ = 2 * l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess := by
      rw [l1DistanceFromBoolean_eq_expect_slice, Finset.mul_expect]
    _ ≤ 6 * (parameters.zeta : ℝ) := by linarith

/-! ## §6 What the estimator must supply

The ledger's `estimateClose` field is an accuracy statement about **one**
number.  `AggregateEstimateAccurate` names it at the published
`estimationError`, and `estimateAccurate_of_aggregateSupplierFailure` is the
seam a supplier guarantee plugs into — the aggregate analogue of
`ComponentwiseBranchExtraction.estimateAccurate_of_supplierFailure`. -/

/-- **The estimator obligation, in the exact shape the ledger consumes.** -/
def AggregateEstimateAccurate {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ) : Prop :=
  |estimate - aggregateClauseMean pcpp value| ≤
    (parameters.estimationError : ℝ)

/-- A supplier guarantee at a failure parameter below the published budget
discharges the aggregate estimator obligation. -/
theorem estimateAccurate_of_aggregateSupplierFailure {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate failure : ℝ)
    (haccurate : |estimate - aggregateClauseMean pcpp value| ≤ failure)
    (hbudget : failure ≤ (parameters.estimationError : ℝ)) :
    AggregateEstimateAccurate pcpp parameters value estimate :=
  haccurate.trans hbudget

/-- An exactly computed aggregate clause mean discharges the obligation at
error zero, since the published `estimationError` is positive. -/
theorem aggregateEstimateAccurate_of_exact {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ) (hexact : estimate = aggregateClauseMean pcpp value) :
    AggregateEstimateAccurate pcpp parameters value estimate := by
  have hpositive : (0 : ℝ) < (parameters.estimationError : ℝ) := by
    exact_mod_cast parameters.estimationErrorPositive
  rw [AggregateEstimateAccurate, hexact, sub_self, abs_zero]
  exact le_of_lt hpositive

/-! ## §7 The majority is not merely avoidable, it is unnecessary

The two facts below record what the aggregate design costs relative to the
majority design of `SemanticStageProgram`.  The completeness side spends the
published radius once and leaves the seam's factor-three reserve untouched
(`aggregateBudget_within_seamReserve`), whereas the majority design had to
spend that reserve on Markov to manufacture a two-thirds density.  The
soundness side needs only the outer accepting-set density and never selects an
individual PCPP input, so the enumerated cube never appears. -/

/-- At the published radius the aggregate error budget is strictly inside the
seam's `6 * zeta` validity budget, with the whole `delta <= 3 * zeta` reserve
unspent. -/
theorem aggregateBudget_within_seamReserve
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) :
    2 * (repairedRecoveryDelta parameters : ℝ) < 6 * (parameters.zeta : ℝ) := by
  have hzeta : (0 : ℝ) < (parameters.zeta : ℝ) := by
    exact_mod_cast parameters.zetaPositive
  rw [repairedRecoveryDelta]
  linarith

end NearCubicWires.AggregateSemanticStage
