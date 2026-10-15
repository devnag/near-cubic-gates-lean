import Proof.MachineModel.ComponentwiseWeakMachine

/-!
# Accepting-branch extraction for the componentwise weak machine

`eventuallyOneSided_of_executableBranchLedger` closes the one-sided
obligation as soon as every accepting branch on a hierarchy-NO input yields
an `ExecutableNoInstanceBranchLedger`.  This module supplies exactly that
extraction step for the fixed componentwise verifier ABI.

The verifier reads one guessed real-valued PCPP proof, rounds it against the
prescribed systematic coordinates, checks componentwise validity, estimates
the arithmetized clause mean with the shared supplier estimator, and compares
that estimate with a stored rational threshold.  The trace below records the
decoded data and the exact rational comparisons it performs; it never records
a semantic acceptance callback.  Two of the ledger's four inequalities are
then proved here rather than assumed:

* the rounded clause mean equals the imported PCPP satisfied fraction, so its
  soundness bound is the published source guarantee;
* the real clause mean stays within `6 * sqrt (12 * zeta)` of the rounded one,
  by the componentwise validity ledger of `ComponentwiseValidity`.

The remaining two are the supplier estimator's own error guarantee and the
verifier's exact rational threshold comparison.
-/

namespace NearCubicWires.ComponentwiseBranchExtraction

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

/-! ## Signed decomposition of a PCPP literal -/

/-- The coordinate queried by a literal, ignoring its sign. -/
def literalIndex {arity : ℕ} : Literal arity → Fin arity
  | .positive index => index
  | .negative index => index

/-- The sign carried by a literal, in the form used by the arithmetized
clause polynomial `clauseValue`. -/
def literalNegated {arity : ℕ} : Literal arity → Bool
  | .positive _ => false
  | .negative _ => true

@[simp] theorem literal_eval_eq_xor {arity : ℕ} (literal : Literal arity)
    (assignment : BitInput arity) :
    literal.eval assignment =
      xor (literalNegated literal) (assignment (literalIndex literal)) := by
  cases literal <;> simp [Literal.eval, literalNegated, literalIndex]

/-! ## The arithmetized two-literal clause -/

/-- One clause of the imported PCPP evaluated on a real proof vector. -/
def clauseRealValue {arity : ℕ} (clause : TwoLiteralClause arity)
    (value : Fin arity → ℝ) : ℝ :=
  clauseValue (literalNegated clause.left) (literalNegated clause.right)
    (value (literalIndex clause.left)) (value (literalIndex clause.right))

theorem clauseValue_bitAsReal (leftNegative rightNegative left right : Bool) :
    clauseValue leftNegative rightNegative (bitAsReal left)
        (bitAsReal right) =
      bitAsReal (xor leftNegative left || xor rightNegative right) := by
  cases leftNegative <;> cases rightNegative <;> cases left <;>
    cases right <;> norm_num [clauseValue, literalValue, bitAsReal]

/-- On a Boolean proof the arithmetization is exactly the clause's Boolean
value.  This is the only place where the polynomial representation and the
imported combinatorial semantics meet. -/
theorem clauseRealValue_bitAsReal {arity : ℕ}
    (clause : TwoLiteralClause arity) (assignment : BitInput arity) :
    clauseRealValue clause (fun j => bitAsReal (assignment j)) =
      bitAsReal (clause.eval assignment) := by
  rw [clauseRealValue, clauseValue_bitAsReal]
  simp [TwoLiteralClause.eval]

/-! ## The clause mean of a real proof -/

/-- Uniform mean of the arithmetized clauses over the imported clause index
space.  This is the quantity the verifier estimates. -/
noncomputable def clauseMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    clauseRealValue (pcpp.clauses i) value

theorem clauseIndex_nonempty {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) :
    (univ : Finset (Fin (2 ^ pcpp.clauseBits))).Nonempty :=
  ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩

theorem expect_bitAsReal_eq_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        bitAsReal
          ((pcpp.clauses i).eval (pcpp.assignment input auxiliary))) =
      pcpp.satisfiedFraction input auxiliary := by
  rw [PointwisePCPP.satisfiedFraction, Finset.expect_eq_sum_div_card]
  congr 1
  · simp [bitAsReal]
  · simp

/-- The rounded clause mean is exactly the imported PCPP satisfied fraction of
the Boolean proof it rounds to. -/
theorem clauseMean_bitAsReal_eq_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    clauseMean pcpp
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) =
      pcpp.satisfiedFraction input auxiliary := by
  rw [clauseMean,
    ← expect_bitAsReal_eq_satisfiedFraction pcpp input auxiliary]
  exact Finset.expect_congr rfl fun i _ =>
    clauseRealValue_bitAsReal (pcpp.clauses i)
      (pcpp.assignment input auxiliary)

/-! ## Prescribed rounding of a guessed real proof -/

/-- The rounding constraint the verifier imposes coordinatewise: systematic
coordinates must round to their prescribed parity, auxiliary coordinates are
free and round at one half. -/
noncomputable def systematicConstraint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → Option Bool :=
  Fin.addCases
    (fun i => some (parityOn (pcpp.systematicSupport i) input))
    (fun _ => none)

/-- The Boolean proof obtained by the prescribed rounding. -/
noncomputable def roundedProof {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    BitInput (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  fun j => validityRound (systematicConstraint pcpp input j) (value j)

/-- The free half of the rounded proof, in the shape the imported PCPP
soundness statement quantifies over. -/
noncomputable def roundedAuxiliary {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    BitInput pcpp.auxiliaryBits :=
  fun j => roundBit (value (Fin.natAdd pcpp.systematicBits j))

/-- The prescribed rounding always lands on a genuine PCPP assignment: the
systematic block is forced, so only the auxiliary block is guessed.  Nothing
else is needed to invoke the imported soundness guarantee. -/
theorem roundedProof_eq_assignment {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    roundedProof pcpp input value =
      pcpp.assignment input (roundedAuxiliary pcpp value) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [roundedProof, systematicConstraint, validityRound,
      PointwisePCPP.assignment]
  · intro i
    simp [roundedProof, systematicConstraint, validityRound,
      PointwisePCPP.assignment, roundedAuxiliary]

/-! ## The componentwise validity ledger under the clause marginals -/

/-- Mean validity penalty over one selected side of the clause distribution.
The verifier checks the two sides jointly, which is what the aggregated
`clauseMean_distance_le_six_of_combined` consumes. -/
noncomputable def clausePenaltyMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    validityPenalty
      (systematicConstraint pcpp input (literalIndex (side (pcpp.clauses i))))
      (value (literalIndex (side (pcpp.clauses i))))

/-- Total validity penalty charged by the verifier's componentwise test. -/
noncomputable def totalClausePenaltyMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  clausePenaltyMean pcpp input value TwoLiteralClause.left +
    clausePenaltyMean pcpp input value TwoLiteralClause.right

private theorem expect_sq_le_four {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits))
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1) :
    (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
      value (literalIndex (side (pcpp.clauses i))) ^ 2) ≤ 4 := by
  calc
    (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        value (literalIndex (side (pcpp.clauses i))) ^ 2) ≤
        𝔼 _i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))), (4 : ℝ) :=
      Finset.expect_le_expect fun i _ => by
        have hzero := hnonneg (literalIndex (side (pcpp.clauses i)))
        have hone := hleOne (literalIndex (side (pcpp.clauses i)))
        nlinarith
    _ = 4 := Finset.expect_const (clauseIndex_nonempty pcpp) 4

private theorem expect_roundingSquare_le {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        (value (literalIndex (side (pcpp.clauses i))) -
          bitAsReal
            (roundedProof pcpp input value
              (literalIndex (side (pcpp.clauses i))))) ^ 2) ≤
      4 * clausePenaltyMean pcpp input value side :=
  validityRound_meanSquare_le
    (univ : Finset (Fin (2 ^ pcpp.clauseBits)))
    (fun i =>
      systematicConstraint pcpp input (literalIndex (side (pcpp.clauses i))))
    (fun i => value (literalIndex (side (pcpp.clauses i))))

/-- Componentwise validity error bound.  A verifier that charges total clause
penalty at most `6 * zeta` cannot move the arithmetized clause mean by more
than the manuscript's `6 * sqrt (12 * zeta)`. -/
theorem clauseMean_close_of_penalty {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (zeta : ℝ) (hzeta : 0 ≤ zeta)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hpenalty : totalClausePenaltyMean pcpp input value ≤ 6 * zeta) :
    |clauseMean pcpp value -
        clauseMean pcpp
          (fun j => bitAsReal (roundedProof pcpp input value j))| ≤
      6 * Real.sqrt (12 * zeta) := by
  set index : Finset (Fin (2 ^ pcpp.clauseBits)) := univ with hindex
  set delta : ℝ := Real.sqrt (12 * zeta) with hdeltaDef
  have hdelta : 0 ≤ delta := Real.sqrt_nonneg _
  have hdeltaSquare : delta ^ 2 = 12 * zeta := by
    rw [hdeltaDef]
    exact Real.sq_sqrt (by linarith)
  have hleftPenalty :=
    expect_roundingSquare_le pcpp input value TwoLiteralClause.left
  have hrightPenalty :=
    expect_roundingSquare_le pcpp input value TwoLiteralClause.right
  have hcombined :
      (𝔼 i ∈ index,
          (value (literalIndex (pcpp.clauses i).left) -
            bitAsReal
              (roundedProof pcpp input value
                (literalIndex (pcpp.clauses i).left))) ^ 2) +
        (𝔼 i ∈ index,
          (value (literalIndex (pcpp.clauses i).right) -
            bitAsReal
              (roundedProof pcpp input value
                (literalIndex (pcpp.clauses i).right))) ^ 2) ≤
        2 * delta ^ 2 := by
    rw [hdeltaSquare]
    unfold totalClausePenaltyMean at hpenalty
    linarith
  have hbound :=
    clauseMean_distance_le_six_of_combined index (clauseIndex_nonempty pcpp)
      (fun i => literalNegated (pcpp.clauses i).left)
      (fun i => literalNegated (pcpp.clauses i).right)
      (fun i => value (literalIndex (pcpp.clauses i).left))
      (fun i => value (literalIndex (pcpp.clauses i).right))
      (fun i =>
        roundedProof pcpp input value (literalIndex (pcpp.clauses i).left))
      (fun i =>
        roundedProof pcpp input value (literalIndex (pcpp.clauses i).right))
      delta hdelta
      (expect_sq_le_four pcpp value TwoLiteralClause.left hnonneg hleOne)
      hcombined
  calc
    |clauseMean pcpp value -
        clauseMean pcpp
          (fun j => bitAsReal (roundedProof pcpp input value j))| =
        |𝔼 i ∈ index,
          (clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i)
              (fun j => bitAsReal (roundedProof pcpp input value j)))| := by
      rw [Finset.expect_sub_distrib]
      rfl
    _ ≤ 𝔼 i ∈ index,
          |clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i)
              (fun j => bitAsReal (roundedProof pcpp input value j))| :=
      Finset.abs_expect_le _ _
    _ ≤ 6 * delta := hbound

/-! ## The accepting verifier trace -/

/-- Data exposed by one successful run of the fixed componentwise verifier on
a guessed proof.  Every field is either decoded data or an inequality the
register program establishes by exact rational arithmetic; no field is a
semantic acceptance callback, and no field is a terminal obligation. -/
structure ComponentwiseVerifierTrace {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) where
  /-- Real coordinates of the guessed proof, one per PCPP coordinate. -/
  proofValue : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ
  /-- Range check on the decoded proof: the verifier rejects out-of-range
  coordinates before any averaging. -/
  proofValueNonneg : ∀ j, 0 ≤ proofValue j
  proofValueLeOne : ∀ j, proofValue j ≤ 1
  /-- Componentwise validity test, charged jointly on both clause sides. -/
  validityChecked :
    totalClausePenaltyMean pcpp input proofValue ≤
      6 * (parameters.zeta : ℝ)
  /-- The rational estimate register the verifier finally compares. -/
  estimateCode : ℚ
  /-- Supplier estimator error guarantee at the checked accuracy. -/
  estimateAccurate :
    |(estimateCode : ℝ) - clauseMean pcpp proofValue| ≤
      (parameters.estimationError : ℝ)
  /-- The exact final threshold comparison performed by the verifier. -/
  thresholdReached : parameters.threshold ≤ estimateCode

/-! ## Exact rational front end for the checked fields

The register program stores the decoded proof and its validity charge as
exact rationals.  The lemmas below are the only permitted bridge between that
arithmetic and the real-valued ledger, so no second decoder or floating
surrogate is introduced. -/

/-- Exact rational form of `validityPenalty`. -/
def rationalValidityPenalty (constraint : Option Bool) (value : ℚ) : ℚ :=
  match constraint with
  | none => value ^ 2 * (1 - value) ^ 2
  | some expected => ((if expected then 1 else 0) - value) ^ 2

theorem validityPenalty_ratCast (constraint : Option Bool) (value : ℚ) :
    validityPenalty constraint (value : ℝ) =
      ((rationalValidityPenalty constraint value : ℚ) : ℝ) := by
  cases constraint with
  | none =>
      simp only [validityPenalty, booleanityPenalty, rationalValidityPenalty]
      push_cast
      ring
  | some expected =>
      cases expected <;>
        · simp only [validityPenalty, systematicPenalty,
            rationalValidityPenalty, bitAsReal]
          push_cast
          ring

/-- Exact rational validity charge accumulated over one clause side.  The
register program accumulates this sum and divides once. -/
noncomputable def rationalClausePenaltySum {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℚ :=
  ∑ i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    rationalValidityPenalty
      (systematicConstraint pcpp input (literalIndex (side (pcpp.clauses i))))
      (value (literalIndex (side (pcpp.clauses i))))

/-- Exact rational form of the verifier's total validity charge. -/
noncomputable def rationalTotalClausePenaltyCharge {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ) : ℚ :=
  (rationalClausePenaltySum pcpp input value TwoLiteralClause.left +
      rationalClausePenaltySum pcpp input value TwoLiteralClause.right) /
    (2 ^ pcpp.clauseBits : ℚ)

private theorem clausePenaltyMean_eq_ratCast_div {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    clausePenaltyMean pcpp input (fun j => (value j : ℝ)) side =
      ((rationalClausePenaltySum pcpp input value side : ℚ) : ℝ) /
        (2 ^ pcpp.clauseBits : ℝ) := by
  rw [clausePenaltyMean, Finset.expect_eq_sum_div_card,
    rationalClausePenaltySum]
  push_cast
  congr 1
  · exact Finset.sum_congr rfl fun i _ => validityPenalty_ratCast _ _
  · simp

theorem totalClausePenaltyMean_eq_ratCast {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ) :
    totalClausePenaltyMean pcpp input (fun j => (value j : ℝ)) =
      ((rationalTotalClausePenaltyCharge pcpp input value : ℚ) : ℝ) := by
  rw [totalClausePenaltyMean, clausePenaltyMean_eq_ratCast_div,
    clausePenaltyMean_eq_ratCast_div, rationalTotalClausePenaltyCharge]
  push_cast
  ring

/-- Build the accepting trace entirely from exact rational register data.
Range checks and the validity charge are decidable rational comparisons; only
the supplier error guarantee remains real-valued, because the estimated
quantity is the real clause mean itself. -/
noncomputable def ComponentwiseVerifierTrace.ofRationalChecks {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (proofValue : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℚ)
    (hnonneg : ∀ j, 0 ≤ proofValue j) (hleOne : ∀ j, proofValue j ≤ 1)
    (hvalidity :
      rationalTotalClausePenaltyCharge pcpp input proofValue ≤
        6 * parameters.zeta)
    (estimateCode : ℚ)
    (haccurate :
      |(estimateCode : ℝ) -
          clauseMean pcpp (fun j => (proofValue j : ℝ))| ≤
        (parameters.estimationError : ℝ))
    (hthreshold : parameters.threshold ≤ estimateCode) :
    ComponentwiseVerifierTrace pcpp input parameters where
  proofValue := fun j => (proofValue j : ℝ)
  proofValueNonneg := fun j => by exact_mod_cast hnonneg j
  proofValueLeOne := fun j => by exact_mod_cast hleOne j
  validityChecked := by
    rw [totalClausePenaltyMean_eq_ratCast]
    exact_mod_cast hvalidity
  estimateCode := estimateCode
  estimateAccurate := haccurate
  thresholdReached := hthreshold

/-- Assemble the estimator field from the supplier's own accuracy ledger: an
error bound at the supplier's failure parameter plus the verifier's stored
accuracy budget.  Downstream code never re-derives the estimator constant. -/
theorem estimateAccurate_of_supplierFailure {n : ℕ}
    {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit}
    {value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {estimate failure budget : ℝ}
    (haccurate : |estimate - clauseMean pcpp value| ≤ failure)
    (hbudget : failure ≤ budget) :
    |estimate - clauseMean pcpp value| ≤ budget :=
  haccurate.trans hbudget

/-! ## Ledger extraction -/

/-- The extraction theorem.  A successful componentwise verifier trace on a
PCPP whose satisfied fraction is bounded on the NO side decodes to the exact
`ExecutableNoInstanceBranchLedger` consumed by
`eventuallyOneSided_of_executableBranchLedger`. -/
noncomputable def executableNoInstanceBranchLedger_of_trace {n : ℕ}
    {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit}
    {input : BitInput n} {completeness soundness : ℝ}
    {parameters : ExecutableSoundnessParameters completeness soundness}
    (roundedSoundness :
      ∀ auxiliary : BitInput pcpp.auxiliaryBits,
        pcpp.satisfiedFraction input auxiliary ≤
          soundness + (parameters.outerError : ℝ))
    (trace : ComponentwiseVerifierTrace pcpp input parameters) :
    ExecutableNoInstanceBranchLedger parameters := by
  have hzeta : (0 : ℝ) ≤ (parameters.zeta : ℝ) := by
    exact_mod_cast le_of_lt parameters.zetaPositive
  refine
    { roundedMean :=
        clauseMean pcpp
          (fun j =>
            bitAsReal (roundedProof pcpp input trace.proofValue j))
      realMean := clauseMean pcpp trace.proofValue
      estimate := (trace.estimateCode : ℝ)
      roundedSound := ?_
      validityClose := ?_
      estimateClose := trace.estimateAccurate
      accepted := ?_ }
  · rw [roundedProof_eq_assignment pcpp input trace.proofValue,
      clauseMean_bitAsReal_eq_satisfiedFraction]
    exact roundedSoundness _
  · exact clauseMean_close_of_penalty pcpp input trace.proofValue
      (parameters.zeta : ℝ) hzeta trace.proofValueNonneg
      trace.proofValueLeOne trace.validityChecked
  · exact_mod_cast trace.thresholdReached

/-! ## The published PCPP soundness owner -/

/-- The only permitted route to the rounded-mean bound: the selected
`UniformPointwisePCPPSource` guarantee at a circuit the branch rejects.  No
downstream module reinterprets or re-proves the imported soundness. -/
theorem uniformPointwisePCPPSource_roundedSoundness
    (source : UniformPointwisePCPPSource) {n : ℕ}
    (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size)
    (input : BitInput n) (hreject : ¬circuit.eval input)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (hsoundness : source.soundness ≤ soundness) :
    ∃ supportBound :
        ∀ i,
          ((source.factory.forCircuit circuit).systematicSupport i).card ≤
            n / 2,
      ∀ auxiliary :
          BitInput
            ((source.factory.forCircuit circuit).toSemantic
              supportBound).auxiliaryBits,
        ((source.factory.forCircuit circuit).toSemantic
            supportBound).satisfiedFraction input auxiliary ≤
          soundness + (parameters.outerError : ℝ) := by
  obtain ⟨supportBound, _, _, _, _, _, _, _, _, sound, _⟩ :=
    source.guarantee circuit hsize
  have houter : (0 : ℝ) < (parameters.outerError : ℝ) := by
    exact_mod_cast parameters.outerErrorPositive
  exact ⟨supportBound, fun auxiliary =>
    ((sound input hreject auxiliary).trans hsoundness).trans (by linarith)⟩

/-! ## Branch evidence and the one-sided closure -/

/-- The complete evidence one accepting branch must expose.  It selects the
PCPP instance the branch actually checked, carries the imported soundness
bound for that instance, and carries the checked trace.  It stores no
terminal obligation and no semantic acceptance callback. -/
structure AcceptingBranchEvidence {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness) where
  /-- Arity of the substituted circuit the branch's PCPP was built for. -/
  arity : ℕ
  circuit : BooleanCircuit arity
  pcpp : PointwisePCPP circuit
  pcppInput : BitInput arity
  /-- Imported PCP/PCPP soundness, charged together with the outer error. -/
  roundedSoundness :
    ∀ auxiliary : BitInput pcpp.auxiliaryBits,
      pcpp.satisfiedFraction pcppInput auxiliary ≤
        soundness + (parameters.outerError : ℝ)
  trace : ComponentwiseVerifierTrace pcpp pcppInput parameters

/-- Branch evidence built directly from the selected published PCPP source.
This is the intended constructor: the soundness field is discharged by the
source guarantee, not supplied by the caller. -/
noncomputable def AcceptingBranchEvidence.ofSource
    (source : UniformPointwisePCPPSource) {n : ℕ}
    (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size)
    (input : BitInput n) (hreject : ¬circuit.eval input)
    {completeness soundness : ℝ}
    {parameters : ExecutableSoundnessParameters completeness soundness}
    (hsoundness : source.soundness ≤ soundness)
    (supportBound :
      ∀ i,
        ((source.factory.forCircuit circuit).systematicSupport i).card ≤
          n / 2)
    (trace :
      ComponentwiseVerifierTrace
        ((source.factory.forCircuit circuit).toSemantic supportBound) input
        parameters) :
    AcceptingBranchEvidence parameters where
  arity := n
  circuit := circuit
  pcpp := (source.factory.forCircuit circuit).toSemantic supportBound
  pcppInput := input
  roundedSoundness := by
    obtain ⟨_, hbound⟩ :=
      uniformPointwisePCPPSource_roundedSoundness source circuit hsize input
        hreject parameters hsoundness
    exact hbound
  trace := trace

noncomputable def executableNoInstanceBranchLedger_of_evidence
    {completeness soundness : ℝ}
    {parameters : ExecutableSoundnessParameters completeness soundness}
    (evidence : AcceptingBranchEvidence parameters) :
    ExecutableNoInstanceBranchLedger parameters :=
  executableNoInstanceBranchLedger_of_trace evidence.roundedSoundness
    evidence.trace

/-- Final composition.  Together with
`eventuallyOneSided_of_executableBranchLedger` this closes the terminal
`honeSided` obligation for any machine whose accepting branches expose the
componentwise verifier trace. -/
theorem eventuallyOneSided_of_acceptingBranchEvidence {hierarchy : Language}
    {completeness soundness : ℝ}
    (machine : ExecutableWeakNondeterministicMachine)
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (onset : ℕ)
    (evidenceOfAcceptedBranch :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          machine.run n input witness →
            Nonempty (AcceptingBranchEvidence parameters)) :
    EventuallyOneSided hierarchy machine := by
  refine eventuallyOneSided_of_executableBranchLedger machine parameters
    onset ?_
  intro n hn input hno witness haccepts
  rcases evidenceOfAcceptedBranch n hn input hno witness haccepts with
    ⟨evidence⟩
  exact ⟨executableNoInstanceBranchLedger_of_evidence evidence⟩

/-! ## The canonically selected verifier constants -/

/-- Branch evidence at the one rational parameter package selected by
`executableParametersOfSource`.  This removes the caller's freedom to pick a
different completeness/soundness pair than the imported source. -/
noncomputable def AcceptingBranchEvidence.ofSelectedSource
    (source : UniformPointwisePCPPSource) {n : ℕ}
    (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size)
    (input : BitInput n) (hreject : ¬circuit.eval input)
    (supportBound :
      ∀ i,
        ((source.factory.forCircuit circuit).systematicSupport i).card ≤
          n / 2)
    (trace :
      ComponentwiseVerifierTrace
        ((source.factory.forCircuit circuit).toSemantic supportBound) input
        (executableParametersOfSource source)) :
    AcceptingBranchEvidence (executableParametersOfSource source) :=
  AcceptingBranchEvidence.ofSource source circuit hsize input hreject
    le_rfl supportBound trace

/-- Interface seam for the concrete verifier.  Once every accepting branch on
a hierarchy-NO input exposes the componentwise trace at the selected source
constants, one-sidedness holds for the machine with no further real-valued
reasoning. -/
theorem eventuallyOneSided_of_selectedSourceEvidence {hierarchy : Language}
    (source : UniformPointwisePCPPSource)
    (machine : ExecutableWeakNondeterministicMachine) (onset : ℕ)
    (evidenceOfAcceptedBranch :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          machine.run n input witness →
            Nonempty
              (AcceptingBranchEvidence
                (executableParametersOfSource source))) :
    EventuallyOneSided hierarchy machine :=
  eventuallyOneSided_of_acceptingBranchEvidence machine
    (executableParametersOfSource source) onset evidenceOfAcceptedBranch

/-! ## Non-vacuity regression

The extracted ledger is an empty type, so the trace ABI must be contradictory
only in the presence of the imported soundness bound.  The regression below
certifies that the ABI is satisfiable on its own: a mis-stated field cannot
make the extraction theorem silently vacuous. -/

/-- A single-clause PCPP with no systematic coordinate.  It exists only to
witness satisfiability of the trace ABI. -/
private noncomputable def regressionPCPP :
    PointwisePCPP (constantBooleanCircuit true) where
  systematicBits := 0
  auxiliaryBits := 1
  clauseBits := 0
  systematicSupport := fun i => i.elim0
  systematicSupportBound := fun i => i.elim0
  clauses := fun _ =>
    ⟨.positive ⟨0, by omega⟩, .positive ⟨0, by omega⟩⟩
  honestAuxiliary := fun _ _ => true
  constructionSteps := 0
  honestSteps := fun _ => 0

private noncomputable def regressionParameters :
    ExecutableSoundnessParameters (1 : ℝ) (0 : ℝ) :=
  Classical.choice (existsExecutableSoundnessParameters (by norm_num))

/-- The accepting-trace ABI is satisfiable in isolation, so the extraction
theorem is not vacuous: the contradiction really comes from the imported PCPP
soundness bound and not from an unsatisfiable checked field. -/
theorem componentwiseVerifierTrace_nonvacuous (input : BitInput 1) :
    Nonempty
      (ComponentwiseVerifierTrace regressionPCPP input
        regressionParameters) := by
  have hcharge :
      rationalTotalClausePenaltyCharge regressionPCPP input
        (fun _ => (1 : ℚ)) = 0 := by
    simp [rationalTotalClausePenaltyCharge, rationalClausePenaltySum,
      regressionPCPP, systematicConstraint, literalIndex,
      rationalValidityPenalty, Fin.addCases]
  have hmean :
      clauseMean regressionPCPP (fun _ => ((1 : ℚ) : ℝ)) = 1 := by
    simp [clauseMean, clauseRealValue, clauseValue, literalValue,
      literalNegated, regressionPCPP]
  refine ⟨ComponentwiseVerifierTrace.ofRationalChecks regressionPCPP input
    regressionParameters (fun _ => 1) (fun _ => by norm_num)
    (fun _ => le_rfl) ?_ 1 ?_ ?_⟩
  · rw [hcharge]
    have hzeta : (0 : ℚ) < regressionParameters.zeta :=
      regressionParameters.zetaPositive
    linarith
  · rw [hmean]
    have hestimation :
        (0 : ℝ) < (regressionParameters.estimationError : ℝ) := by
      exact_mod_cast regressionParameters.estimationErrorPositive
    simpa using le_of_lt hestimation
  · exact le_of_lt (regressionParameters.thresholdBelowOne le_rfl)

end NearCubicWires.ComponentwiseBranchExtraction
