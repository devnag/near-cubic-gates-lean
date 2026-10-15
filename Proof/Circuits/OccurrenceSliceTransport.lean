import Proof.CaseAnalysis.CaseTwoWitnessCompleteness

/-!
# The occurrence-slice transport of the Case-2 approximation radius

The Case-2 completeness chain of
[`CaseTwoWitnessCompleteness`](Proof/CaseAnalysis/CaseTwoWitnessCompleteness.lean)
delivers exactly one semantic fact about the guessed witness:

```lean
RecoveryWitnessApproximates seed (publishedRecoveryDelta contracts) witness
```

i.e. `l1DistanceFromBoolean seed value ≤ delta` for the scheduled Case-2 seed
`seed = caseTwoSeed …`, which is the honest *occurrence* table of the padded
pointwise PCPP.  The verifier seam of
[`VerifierThresholdSeam`](Proof/PCP/VerifierThresholdSeam.lean) consumes a
different quantity, `clauseOccurrenceErrorMean pcpp value reference`, and that
quantity is charged *at one fixed PCPP input*.

This module is the transport between the two.  It settles the question with an
exact identity and an exact obstruction.

## §0 The answer

The seed's cube is the product

```text
BitInput (inputArity + clauseBits + 1)  ≅
  (PCPP input) × (clause address) × (left/right position)
```

and `l1DistanceFromBoolean` is the uniform mean over *all three* blocks, while
`clauseOccurrenceErrorMean` is the uniform mean over the last two blocks only,
with the first block frozen at one input.  Consequently:

* **`§3` (positive, exact).**  For every fixed PCPP input the two quantities
  agree *exactly*, once the guessed occurrence values are read back to proof
  coordinates by the occurrence-fiber average of their sign-adjusted values:
  `clauseOccurrenceErrorMean_recoveredProofValue`.  Neither the two-occurrence
  aliasing of a shared coordinate nor the literal polarity costs anything —
  the identity is an equality, not an inequality.
* **`§2` (positive, exact).**  The whole-cube distance is the uniform mean of
  the per-input slice distances: `l1DistanceFromBoolean_eq_expect_slice`.
* **`§5` (negative).**  An average over the input block does not bound an
  individual slice: `slice_not_le_of_l1Distance` exhibits a PCPP at one and
  the same radius `1 / 2` for which the whole-cube premise holds and the
  per-input premise fails, and
  `exists_slice_gt_factor_mul_l1Distance` shows the loss factor is the whole
  size `2 ^ inputArity` of the PCPP input space, so no constant rescaling of
  the published radius repairs the transport.
* **`§4` (the repair).**  Markov's inequality on the slice distribution is
  free here, because the seam already runs at a factor-three reserve
  (`threshold_le_estimate_of_occurrenceDelta` closes at `delta ≤ 3 * zeta`
  while the published radius is `repairedRecoveryDelta parameters = zeta`).
  At least *two thirds* of all PCPP inputs satisfy the seam premise:
  `two_thirds_le_card_seamInputs`, and at the published radius
  `two_thirds_le_card_seamInputs_of_repairedDelta`.
* **`§6` (the consequence).**  `threshold_le_estimate_of_sliceInput` is the
  seam with its `hclose` premise discharged at one admissible PCPP input.
  Together with `§4` and `§5` it says what a *per-input* semantic test can and
  cannot be charged: not at every PCPP input (`§5`), and — if a per-input test
  is insisted on — only on a majority of them (`§4`).

  **That reading is superseded, and the reader should not follow it into a
  majority design.**  `§5` is a genuine obstruction to the `∀`-input test and
  stands.  The inference from it to a *majority* test does not: it silently
  assumes the stage must reach a per-input verdict at all.  The manuscript's
  componentwise verifier (Appendix C.10) reaches no per-input verdict.  It
  estimates the single global average `mu = E_{i,u} F_i(u)` over the joint
  cube and compares that one number against the one threshold.  The transport
  of `§2` is then not an obstruction but exactly the tool the aggregate
  design needs: `l1DistanceFromBoolean_eq_expect_slice` says the published
  whole-cube radius *is* the aggregate slice error, so the completeness
  premise transports with no loss and with no Markov step.
  `AggregateSemanticStage` builds that design; `§4` is retained as correct
  mathematics but is not on its critical path.

  The majority reading is also unaffordable, which is the practical reason it
  must not be followed: charging a per-input test at every enumerated PCPP
  input costs `2 ^ scheduledWidth`, a polynomial of degree
  `ProjectionWidthEnvelope.widthLinearCoefficient outer 1`, and that degree
  carries the factor `2 ^ clockDepth` while `PublishedRecoveryClosure` pins
  `clockDepth = machine.verifier.degree + 1`.  The resulting fixed-point
  demand `degree ≥ 2 ^ (degree + 2)` has no numeral solution.

* **`§7` (the scheduled seed).**  `caseTwoSeed` is
  `PCPPClausePadding.fullyPaddedHonestOccurrenceFunction`, the honest
  occurrence table of `padClauses` extended along two ignored axes.  The
  clause-address padding is already a genuine `PointwisePCPP`, and the
  input-axis padding moves through the slice by `prefixBits`, so the transport
  holds verbatim at the scheduled seed:
  `clauseOccurrenceErrorMean_recoveredProofValue_fullyPadded`.

Nothing in `§1`–`§5` mentions a schedule, a machine, or an executable
program: the whole transport is finite measure bookkeeping on the occurrence
cube.
-/

namespace NearCubicWires.OccurrenceSliceTransport

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifierThresholdSeam

/-! ## §1 Coordinates of the occurrence cube

`occurrenceInput`, `occurrenceClauseAddress` and `occurrencePosition` of
`OuterPCPRecovery` project an occurrence address onto its three blocks.  The
assembler below is their common section, so the three projections are jointly
an equivalence. -/

/-- Assemble one occurrence address from a PCPP input, a clause address and a
left/right position bit. -/
def occurrenceAddress {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) : BitInput (inputArity + clauseBits + 1) :=
  fun index =>
    if hinput : index.val < inputArity then input ⟨index.val, hinput⟩
    else if hclause : index.val < inputArity + clauseBits then
      clause ⟨index.val - inputArity, by omega⟩
    else position

@[simp] theorem occurrenceInput_occurrenceAddress {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrenceInput (occurrenceAddress input clause position) = input := by
  funext index
  simp [occurrenceInput, occurrenceAddress, index.isLt]

@[simp] theorem occurrenceClauseAddress_occurrenceAddress
    {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrenceClauseAddress (occurrenceAddress input clause position) =
      clause := by
  funext index
  have hbound := index.isLt
  have hlow : ¬inputArity + index.val < inputArity := by omega
  have hhigh : inputArity + index.val < inputArity + clauseBits := by omega
  have hval : inputArity + index.val - inputArity = index.val := by omega
  simp only [occurrenceClauseAddress, occurrenceAddress, hlow, hhigh, dif_pos]
  exact congrArg clause (Fin.ext hval)

@[simp] theorem occurrencePosition_occurrenceAddress
    {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrencePosition (occurrenceAddress input clause position) =
      position := by
  have hlow : ¬inputArity + clauseBits < inputArity := by omega
  simp [occurrencePosition, occurrenceAddress, hlow]

theorem occurrenceAddress_projections {inputArity clauseBits : ℕ}
    (address : BitInput (inputArity + clauseBits + 1)) :
    occurrenceAddress (occurrenceInput address)
        (occurrenceClauseAddress address) (occurrencePosition address) =
      address := by
  funext index
  have hbound := index.isLt
  unfold occurrenceAddress occurrenceInput occurrenceClauseAddress
    occurrencePosition
  by_cases hinput : index.val < inputArity
  · simp only [hinput, dif_pos]
  · by_cases hclause : index.val < inputArity + clauseBits
    · have hval : inputArity + (index.val - inputArity) = index.val := by omega
      simp only [hinput, hclause, dif_neg, dif_pos, not_false_iff]
      exact congrArg address (Fin.ext hval)
    · have hval : inputArity + clauseBits = index.val := by omega
      simp only [hinput, hclause, dif_neg, not_false_iff]
      exact congrArg address (Fin.ext hval)

/-- The three occurrence blocks are jointly an equivalence with the cube. -/
def occurrenceCubeEquiv (inputArity clauseBits : ℕ) :
    BitInput inputArity × BitInput clauseBits × Bool ≃
      BitInput (inputArity + clauseBits + 1) where
  toFun parts := occurrenceAddress parts.1 parts.2.1 parts.2.2
  invFun address :=
    (occurrenceInput address, occurrenceClauseAddress address,
      occurrencePosition address)
  left_inv := by
    rintro ⟨input, clause, position⟩
    simp
  right_inv := occurrenceAddress_projections

/-- Little-endian enumeration of the clause-address block.  This is the exact
bijection `honestOccurrenceFunction` uses to turn address bits into a clause
index, so no second addressing convention is introduced. -/
private def clauseAddressBits (bits : ℕ) : Fin (2 ^ bits) ≃ BitInput bits where
  toFun index := fun bit => index.val.testBit bit.val
  invFun := binaryAddress
  left_inv index := binaryAddress_testBit index.isLt
  right_inv input := by
    funext bit
    change (binaryAddress input).val.testBit bit.val = input bit
    rw [binaryAddress_val_eq_ofBits]
    exact Nat.testBit_ofBits_lt input bit.val bit.isLt

@[simp] private theorem binaryAddress_clauseAddressBits (bits : ℕ)
    (index : Fin (2 ^ bits)) :
    binaryAddress (clauseAddressBits bits index) = index :=
  (clauseAddressBits bits).left_inv index

private theorem card_bitInputCube (bits : ℕ) :
    Fintype.card (BitInput bits) = 2 ^ bits := by
  rw [Fintype.card_fun]
  simp

/-! ## §2 The whole-cube distance is the mean of the input slices

`l1DistanceFromBoolean` is the uniform mean over the *whole* occurrence cube.
Slicing the cube along its first block exhibits it as the uniform mean, over
PCPP inputs, of the per-input occurrence error.  This is the exact statement
of the average-versus-slice obstruction: nothing is lost, and nothing is
gained. -/

/-- Mean `ℓ¹` error of a guess against a Boolean occurrence table on the slice
above one fixed PCPP input. -/
noncomputable def occurrenceSliceDistance {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ)
    (input : BitInput inputArity) : ℝ :=
  𝔼 slot : BitInput clauseBits × Bool,
    |guess (occurrenceAddress input slot.1 slot.2) -
      bitAsReal (table (occurrenceAddress input slot.1 slot.2))|

theorem occurrenceSliceDistance_nonnegative {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ)
    (input : BitInput inputArity) :
    0 ≤ occurrenceSliceDistance table guess input :=
  Finset.expect_nonneg fun _ _ => abs_nonneg _

/-- **Cube slicing.**  The published approximation radius controls exactly the
*average* of the per-input occurrence errors. -/
theorem l1DistanceFromBoolean_eq_expect_slice {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ) :
    l1DistanceFromBoolean table guess =
      𝔼 input : BitInput inputArity,
        occurrenceSliceDistance table guess input := by
  classical
  have hsum :
      (∑ address : BitInput (inputArity + clauseBits + 1),
          |guess address - bitAsReal (table address)|) =
        ∑ input : BitInput inputArity,
          ∑ slot : BitInput clauseBits × Bool,
            |guess (occurrenceAddress input slot.1 slot.2) -
              bitAsReal (table (occurrenceAddress input slot.1 slot.2))| := by
    rw [← (occurrenceCubeEquiv inputArity clauseBits).sum_comp
      (fun address => |guess address - bitAsReal (table address)|)]
    exact Fintype.sum_prod_type _
  rw [l1DistanceFromBoolean, hsum, Finset.expect_eq_sum_div_card]
  simp only [occurrenceSliceDistance, Finset.expect_eq_sum_div_card,
    Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    card_bitInputCube, ← Finset.sum_div, div_div]
  congr 1
  push_cast
  ring

/-! ## §3 The exact per-input transport

At one fixed PCPP input the two averages agree *exactly*.  The two structural
worries are both discharged by an identity rather than an inequality:

* a proof coordinate named by several occurrences is read back by the
  occurrence-fiber average, and `occurrenceAveraging_preserves_distance` shows
  that averaging over a fiber whose Boolean target is constant costs nothing;
* the honest occurrence table stores the *signed* literal value, so a negative
  literal is read back complemented, and complementation is an isometry. -/

/-- The literal one clause occurrence names.  `position = true` selects the
right literal, matching `honestOccurrenceFunction`. -/
def occurrenceLiteral {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    Literal (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  if slot.2 then (pcpp.clauses slot.1).right else (pcpp.clauses slot.1).left

/-- The proof coordinate one clause occurrence reads. -/
def occurrenceVariable {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  literalIndex (occurrenceLiteral pcpp slot)

/-- Coordinate reading of one guessed occurrence value. -/
noncomputable def occurrenceCoordinateValue {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) : ℝ :=
  if literalNegated (occurrenceLiteral pcpp slot) then 1 - guess slot
  else guess slot

private theorem bitAsReal_not (bit : Bool) :
    bitAsReal (!bit) = 1 - bitAsReal bit := by
  cases bit <;> norm_num [bitAsReal]

private theorem abs_one_sub_sub_bitAsReal (value : ℝ) (bit : Bool) :
    |1 - value - bitAsReal bit| = |value - bitAsReal (!bit)| := by
  rw [bitAsReal_not,
    show (1 : ℝ) - value - bitAsReal bit =
      -(value - (1 - bitAsReal bit)) by ring, abs_neg]

/-- Complementing a negative literal is an isometry: the coordinate reading of
an occurrence value is exactly as far from the honest coordinate as the
occurrence value is from the honest occurrence bit. -/
theorem abs_occurrenceCoordinateValue_sub {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    |occurrenceCoordinateValue pcpp guess slot -
        bitAsReal (assignment (occurrenceVariable pcpp slot))| =
      |guess slot -
        bitAsReal ((occurrenceLiteral pcpp slot).eval assignment)| := by
  rw [literal_eval_eq_xor]
  unfold occurrenceCoordinateValue occurrenceVariable
  cases hnegated : literalNegated (occurrenceLiteral pcpp slot) with
  | false => simp
  | true =>
      simp only [if_true, Bool.true_xor]
      exact abs_one_sub_sub_bitAsReal _ _

theorem occurrenceCoordinateValue_mem_unitInterval {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (hnonneg : ∀ slot, 0 ≤ guess slot) (hleOne : ∀ slot, guess slot ≤ 1)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    0 ≤ occurrenceCoordinateValue pcpp guess slot ∧
      occurrenceCoordinateValue pcpp guess slot ≤ 1 := by
  unfold occurrenceCoordinateValue
  have hzero := hnonneg slot
  have hone := hleOne slot
  cases literalNegated (occurrenceLiteral pcpp slot) with
  | false => exact ⟨by simpa using hzero, by simpa using hone⟩
  | true => constructor <;> simp <;> linarith

/-- **The proof vector a guessed occurrence table induces.**  Each coordinate
is the average of the coordinate readings of every occurrence that names it;
coordinates named by no occurrence are irrelevant to every quantity the
verifier charges and are set to zero. -/
noncomputable def occurrenceProofValue {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ :=
  occurrenceAverage (occurrenceVariable pcpp)
    (occurrenceCoordinateValue pcpp guess)

theorem occurrenceProofValue_mem_unitInterval {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (hnonneg : ∀ slot, 0 ≤ guess slot) (hleOne : ∀ slot, guess slot ≤ 1)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    0 ≤ occurrenceProofValue pcpp guess coordinate ∧
      occurrenceProofValue pcpp guess coordinate ≤ 1 := by
  classical
  by_cases hfiber :
      (occurrenceFiber (occurrenceVariable pcpp) coordinate).Nonempty
  · exact occurrenceAverage_mem_unitInterval (occurrenceVariable pcpp)
      (occurrenceCoordinateValue pcpp guess) coordinate hfiber
      (occurrenceCoordinateValue_mem_unitInterval pcpp guess hnonneg hleOne)
  · have hempty :
        occurrenceFiber (occurrenceVariable pcpp) coordinate = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [occurrenceProofValue, occurrenceAverage, meanOn, hempty]

private theorem expect_slot_eq_sides {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ) :
    (𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool, value slot) =
      ((𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))), value (i, false)) +
          𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            value (i, true)) / 2 := by
  have hpositive : (0 : ℝ) < (2 ^ pcpp.clauseBits : ℕ) := by positivity
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  field_simp
  push_cast
  ring

/-- The verifier's occurrence-uniform error is the uniform mean over clause
occurrences, in the `(clause index, position)` presentation. -/
theorem clauseOccurrenceErrorMean_eq_expect_slot {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    clauseOccurrenceErrorMean pcpp value reference =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |value (occurrenceVariable pcpp slot) -
          reference (occurrenceVariable pcpp slot)| := by
  rw [expect_slot_eq_sides]
  rfl

/-- **The per-input transport, exactly.**  Reading a guessed occurrence table
back to proof coordinates by the occurrence-fiber average of its coordinate
readings turns the verifier's clause-occurrence error into the guess's own
occurrence error against the honest table, with no loss. -/
theorem clauseOccurrenceErrorMean_occurrenceProofValue {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits))
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (hnonneg : ∀ slot, 0 ≤ guess slot) (hleOne : ∀ slot, guess slot ≤ 1) :
    clauseOccurrenceErrorMean pcpp (occurrenceProofValue pcpp guess)
        (fun j => bitAsReal (assignment j)) =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |guess slot -
          bitAsReal ((occurrenceLiteral pcpp slot).eval assignment)| := by
  classical
  rw [clauseOccurrenceErrorMean_eq_expect_slot, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card]
  congr 1
  rw [show
    (∑ slot ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits) × Bool)),
        |occurrenceProofValue pcpp guess (occurrenceVariable pcpp slot) -
          bitAsReal (assignment (occurrenceVariable pcpp slot))|) =
      ∑ slot,
        |occurrenceAverage (occurrenceVariable pcpp)
            (occurrenceCoordinateValue pcpp guess)
            (occurrenceVariable pcpp slot) -
          bitAsReal (assignment (occurrenceVariable pcpp slot))| from rfl,
    occurrenceAveraging_preserves_distance (occurrenceVariable pcpp)
      (occurrenceCoordinateValue pcpp guess) assignment
      (occurrenceCoordinateValue_mem_unitInterval pcpp guess hnonneg hleOne)]
  exact Finset.sum_congr rfl fun slot _ =>
    abs_occurrenceCoordinateValue_sub pcpp guess slot assignment

/-! ### The transport at the honest occurrence table -/

@[simp] theorem honestOccurrenceFunction_occurrenceAddress {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (clause : BitInput pcpp.clauseBits)
    (position : Bool) :
    honestOccurrenceFunction pcpp
        (occurrenceAddress input clause position) =
      (occurrenceLiteral pcpp (binaryAddress clause, position)).eval
        (pcpp.assignment input (pcpp.honestAuxiliary input)) := by
  simp [honestOccurrenceFunction, occurrenceLiteral]

/-- The restriction of a guessed occurrence table to the slice above one PCPP
input, in the `(clause index, position)` presentation. -/
noncomputable def sliceGuess {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) : ℝ :=
  guess (occurrenceAddress input
    (clauseAddressBits pcpp.clauseBits slot.1) slot.2)

/-- **The proof vector the verifier recovers at one PCPP input.** -/
noncomputable def recoveredProofValue {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ :=
  occurrenceProofValue pcpp (sliceGuess pcpp guess input)

theorem recoveredProofValue_mem_unitInterval {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    0 ≤ recoveredProofValue pcpp guess input coordinate ∧
      recoveredProofValue pcpp guess input coordinate ≤ 1 :=
  occurrenceProofValue_mem_unitInterval pcpp (sliceGuess pcpp guess input)
    (fun _ => hnonneg _) (fun _ => hleOne _) coordinate

private theorem occurrenceSliceDistance_eq_expect_slot {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n) :
    occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess input =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |sliceGuess pcpp guess input slot -
          bitAsReal ((occurrenceLiteral pcpp slot).eval
            (pcpp.assignment input (pcpp.honestAuxiliary input)))| := by
  classical
  have hcards :
      Fintype.card (BitInput pcpp.clauseBits × Bool) =
        Fintype.card (Fin (2 ^ pcpp.clauseBits) × Bool) := by
    simp [Fintype.card_prod]
  rw [occurrenceSliceDistance, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    ← (Equiv.prodCongr (clauseAddressBits pcpp.clauseBits)
        (Equiv.refl Bool)).sum_comp
      (fun slot : BitInput pcpp.clauseBits × Bool =>
        |guess (occurrenceAddress input slot.1 slot.2) -
          bitAsReal (honestOccurrenceFunction pcpp
            (occurrenceAddress input slot.1 slot.2))|)]
  simp only [Finset.card_univ, hcards]
  congr 1
  exact Finset.sum_congr rfl fun slot _ => by
    simp [sliceGuess]

/-- **The transport at the honest table.**  The verifier's clause-occurrence
error against the honest PCPP assignment, on the proof vector recovered from a
guessed occurrence table at one PCPP input, *equals* that input's slice of the
whole-cube `ℓ¹` distance to the honest occurrence table. -/
theorem clauseOccurrenceErrorMean_recoveredProofValue {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1) :
    clauseOccurrenceErrorMean pcpp (recoveredProofValue pcpp guess input)
        (fun j =>
          bitAsReal
            (pcpp.assignment input (pcpp.honestAuxiliary input) j)) =
      occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess input := by
  rw [recoveredProofValue,
    clauseOccurrenceErrorMean_occurrenceProofValue pcpp
      (pcpp.assignment input (pcpp.honestAuxiliary input))
      (sliceGuess pcpp guess input) (fun _ => hnonneg _)
      (fun _ => hleOne _),
    occurrenceSliceDistance_eq_expect_slot]

/-! ## §4 Markov: a two-thirds density of admissible PCPP inputs

The seam of `VerifierThresholdSeam` closes at `delta ≤ 3 * zeta`
(`threshold_le_estimate_of_occurrenceDelta`) while the published radius is
`repairedRecoveryDelta parameters = zeta`.  That factor-three reserve is
exactly what makes Markov's inequality usable: at radius `zeta` at most one
third of the PCPP inputs can carry a slice above `3 * zeta`. -/

private theorem bound_mul_card_filter_le_sum {index : Type} [Fintype index]
    (value : index → ℝ) (hnonneg : ∀ i, 0 ≤ value i) (bound : ℝ) :
    bound * ((univ.filter fun i => bound < value i).card : ℝ) ≤
      ∑ i, value i := by
  calc
    bound * ((univ.filter fun i => bound < value i).card : ℝ) =
        ∑ _i ∈ univ.filter fun i => bound < value i, bound := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ univ.filter fun i => bound < value i, value i :=
      Finset.sum_le_sum fun i hi =>
        le_of_lt (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, value i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => hnonneg i

/-- Markov's inequality in the `Finset.expect` form the slice distribution
uses. -/
theorem expect_markov {index : Type} [Fintype index] [Nonempty index]
    (value : index → ℝ) (hnonneg : ∀ i, 0 ≤ value i) (radius bound : ℝ)
    (hmean : (𝔼 i, value i) ≤ radius) :
    bound * ((univ.filter fun i => bound < value i).card : ℝ) ≤
      radius * (Fintype.card index : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card index : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty index›
  have hsum : (∑ i, value i) ≤ radius * (Fintype.card index : ℝ) := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ,
      div_le_iff₀ hcard] at hmean
    exact hmean
  exact (bound_mul_card_filter_le_sum value hnonneg bound).trans hsum

/-- **The two-thirds density.**  A nonnegative quantity whose mean is at most
`radius` stays below `3 * radius` on at least two thirds of the index set. -/
theorem two_thirds_le_card_within_threeRadius {index : Type} [Fintype index]
    [Nonempty index] (value : index → ℝ)
    (hnonneg : ∀ i, 0 ≤ value i) (radius : ℝ) (hradius : 0 < radius)
    (hmean : (𝔼 i, value i) ≤ radius) :
    (2 / 3 : ℝ) * (Fintype.card index : ℝ) ≤
      ((univ.filter fun i => value i ≤ 3 * radius).card : ℝ) := by
  have hsplit :
      (univ.filter fun i => value i ≤ 3 * radius).card +
          (univ.filter fun i => ¬value i ≤ 3 * radius).card =
        (univ : Finset index).card :=
    Finset.card_filter_add_card_filter_not _
  have hnegFilter :
      (univ.filter fun i => ¬value i ≤ 3 * radius) =
        univ.filter fun i => 3 * radius < value i := by
    apply Finset.filter_congr
    intro i _
    simp [not_le]
  have hmarkov :=
    expect_markov value hnonneg radius (3 * radius) hmean
  rw [← hnegFilter] at hmarkov
  have hcards :
      ((univ.filter fun i => value i ≤ 3 * radius).card : ℝ) +
          ((univ.filter fun i => ¬value i ≤ 3 * radius).card : ℝ) =
        (Fintype.card index : ℝ) := by
    rw [← Finset.card_univ]
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsplit
  nlinarith [hcards, hmarkov,
    (Nat.cast_nonneg (univ.filter fun i => ¬value i ≤ 3 * radius).card : (0:ℝ) ≤ _)]

/-- **The repaired transport.**  A guess inside the published whole-cube
radius satisfies the seam premise on at least two thirds of all PCPP
inputs. -/
theorem two_thirds_le_card_seamInputs {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hdistance : l1DistanceFromBoolean table guess ≤ radius) :
    (2 / 3 : ℝ) * ((2 ^ inputArity : ℕ) : ℝ) ≤
      ((univ.filter fun input : BitInput inputArity =>
          occurrenceSliceDistance table guess input ≤ 3 * radius).card : ℝ) := by
  have hmean :
      (𝔼 input : BitInput inputArity,
        occurrenceSliceDistance table guess input) ≤ radius := by
    rw [← l1DistanceFromBoolean_eq_expect_slice]
    exact hdistance
  have hbound :=
    two_thirds_le_card_within_threeRadius
      (fun input : BitInput inputArity =>
        occurrenceSliceDistance table guess input)
      (fun input => occurrenceSliceDistance_nonnegative table guess input)
      radius hradius hmean
  rwa [card_bitInputCube] at hbound

/-! ## §5 The per-input transport genuinely fails

The identity of `§2` is sharp, so an average over `2 ^ inputArity` inputs
cannot bound one slice.  The family below realizes the whole loss: its honest
occurrence table is supported on a single PCPP input, so the constant-zero
guess is at whole-cube distance `1 / 2 ^ inputArity` while its slice above
that one input equals `1`.  Consequently no constant rescaling of the
published radius turns the whole-cube premise into the per-input premise. -/

private def sliceRegressionCircuit (inputArity : ℕ) :
    BooleanCircuit inputArity where
  nodes := [.const true]
  output := ⟨0, by simp⟩
  wellFormed := by
    intro index
    simp [BooleanNode.WellFormedAt]

/-- A PCPP whose honest occurrence table is the indicator of one PCPP input. -/
private noncomputable def sliceRegressionPCPP (inputArity : ℕ) :
    PointwisePCPP (sliceRegressionCircuit inputArity) where
  systematicBits := 0
  auxiliaryBits := 1
  clauseBits := 0
  systematicSupport := fun i => i.elim0
  systematicSupportBound := fun i => i.elim0
  clauses := fun _ => ⟨.positive ⟨0, by omega⟩, .positive ⟨0, by omega⟩⟩
  honestAuxiliary := fun input _ => decide (input = fun _ => true)
  constructionSteps := 0
  honestSteps := fun _ => 0

private theorem sliceRegression_seed (inputArity : ℕ)
    (input : BitInput inputArity)
    (clause : BitInput (sliceRegressionPCPP inputArity).clauseBits)
    (position : Bool) :
    honestOccurrenceFunction (sliceRegressionPCPP inputArity)
        (occurrenceAddress input clause position) =
      decide (input = fun _ => true) := by
  rw [honestOccurrenceFunction_occurrenceAddress]
  simp [occurrenceLiteral, sliceRegressionPCPP, PointwisePCPP.assignment,
    Fin.addCases, literalNegated]

/-- The slice of the constant-zero guess is `1` exactly above the one
supported PCPP input. -/
theorem sliceRegression_slice (inputArity : ℕ) (input : BitInput inputArity) :
    occurrenceSliceDistance
        (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
        (fun _ => 0) input =
      if input = (fun _ => true) then 1 else 0 := by
  rw [occurrenceSliceDistance]
  have hterm :
      ∀ slot :
        BitInput (sliceRegressionPCPP inputArity).clauseBits × Bool,
        |(0 : ℝ) -
            bitAsReal
              (honestOccurrenceFunction (sliceRegressionPCPP inputArity)
                (occurrenceAddress input slot.1 slot.2))| =
          if input = (fun _ => true) then 1 else 0 := by
    intro slot
    rw [sliceRegression_seed]
    by_cases hinput : input = (fun _ => true) <;> simp [hinput, bitAsReal]
  rw [Finset.expect_congr rfl fun slot _ => hterm slot]
  exact Finset.expect_const Finset.univ_nonempty _

/-- The whole-cube distance of the same guess is `1 / 2 ^ inputArity`. -/
theorem sliceRegression_l1Distance (inputArity : ℕ) :
    l1DistanceFromBoolean
        (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
        (fun _ => 0) =
      1 / ((2 ^ inputArity : ℕ) : ℝ) := by
  rw [l1DistanceFromBoolean_eq_expect_slice,
    Finset.expect_congr rfl fun input _ => sliceRegression_slice inputArity input,
    Finset.expect_eq_sum_div_card, Finset.card_univ, card_bitInputCube,
    Finset.sum_ite_eq' Finset.univ (fun _ : Fin inputArity => true)
      (fun _ => (1 : ℝ))]
  simp

/-- **The negative result.**  At one and the same radius the whole-cube
premise holds and the per-input premise fails. -/
theorem slice_not_le_of_l1Distance (inputArity : ℕ)
    (hpositive : 0 < inputArity) :
    l1DistanceFromBoolean
        (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
        (fun _ => 0) ≤ 1 / 2 ∧
      ¬occurrenceSliceDistance
        (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
        (fun _ => 0) (fun _ => true) ≤ 1 / 2 := by
  have htwo : (2 : ℝ) ≤ ((2 ^ inputArity : ℕ) : ℝ) := by
    have hle : 2 ^ 1 ≤ 2 ^ inputArity := Nat.pow_le_pow_right (by omega) hpositive
    exact_mod_cast (by simpa using hle : (2 : ℕ) ≤ 2 ^ inputArity)
  have hslice :
      occurrenceSliceDistance
          (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
          (fun _ => 0) (fun _ => true) = 1 := by
    rw [sliceRegression_slice]
    simp
  constructor
  · rw [sliceRegression_l1Distance,
      div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · rw [hslice]
    norm_num

/-- **No constant rescaling repairs the transport.**  For every factor the
family above has a member whose slice exceeds that multiple of its whole-cube
distance; the loss factor is the size `2 ^ inputArity` of the PCPP input
space. -/
theorem exists_slice_gt_factor_mul_l1Distance (factor : ℝ) :
    ∃ inputArity : ℕ,
      factor *
          l1DistanceFromBoolean
            (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
            (fun _ => 0) <
        occurrenceSliceDistance
          (honestOccurrenceFunction (sliceRegressionPCPP inputArity))
          (fun _ => 0) (fun _ => true) := by
  refine ⟨⌈factor⌉₊, ?_⟩
  have hpower : (⌈factor⌉₊ : ℝ) < ((2 ^ ⌈factor⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_two_pow_self
  have hceil : factor ≤ (⌈factor⌉₊ : ℝ) := Nat.le_ceil factor
  have hpositive : (0 : ℝ) < ((2 ^ ⌈factor⌉₊ : ℕ) : ℝ) := by positivity
  have hslice :
      occurrenceSliceDistance
          (honestOccurrenceFunction (sliceRegressionPCPP ⌈factor⌉₊))
          (fun _ => 0) (fun _ => true) = 1 := by
    rw [sliceRegression_slice]
    simp
  rw [sliceRegression_l1Distance, hslice, mul_one_div, div_lt_one hpositive]
  linarith

/-! ## §6 What a *per-input* semantic test can charge

`§3` plus `§4` say what a per-input componentwise test can afford: the test at
*one* PCPP input is discharged by the transport whenever that input's slice is
inside the seam's `3 * zeta` budget, and at least two thirds of all PCPP inputs
are of that kind.  `§5` says such a test cannot be demanded at *every* PCPP
input.

**These are facts about per-input tests, not a specification of the verifier.**
The manuscript's componentwise verifier performs no per-input test: it
estimates one global average over the joint cube and compares it once.  See
`AggregateSemanticStage` for that design and for why the majority reading of
this section is both unnecessary and unaffordable.  The results below remain
correct and are kept because `threshold_le_estimate_of_sliceInput` is the
sharpest statement of the per-input seam, and because
`two_thirds_le_card_seamInputs_of_repairedDelta` records what the published
radius buys pointwise. -/

/-- **The seam fires at every admissible PCPP input.**  This is
`VerifierThresholdSeam.threshold_le_estimate_of_occurrenceDelta` with its
`hclose` premise supplied by the transport of `§3`. -/
theorem threshold_le_estimate_of_sliceInput {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (estimate : ℝ)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1)
    (hhonest :
      completeness ≤
        clauseMean pcpp
          (fun j =>
            bitAsReal (pcpp.assignment input (pcpp.honestAuxiliary input) j)))
    (hslice :
      occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess input ≤
        3 * (parameters.zeta : ℝ))
    (haccurate :
      |estimate - clauseMean pcpp (recoveredProofValue pcpp guess input)| ≤
        (parameters.estimationError : ℝ)) :
    (parameters.threshold : ℝ) ≤ estimate :=
  threshold_le_estimate_of_occurrenceDelta pcpp input
    (pcpp.honestAuxiliary input) parameters
    (recoveredProofValue pcpp guess input) (3 * (parameters.zeta : ℝ))
    estimate
    (fun j =>
      (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
        j).1)
    (fun j =>
      (recoveredProofValue_mem_unitInterval pcpp guess input hnonneg hleOne
        j).2)
    hhonest le_rfl
    (by
      rw [clauseOccurrenceErrorMean_recoveredProofValue pcpp guess input
        hnonneg hleOne]
      exact hslice)
    haccurate

/-- **The density at the published radius.**  A witness inside
`repairedRecoveryDelta parameters = parameters.zeta` puts at least two thirds
of all PCPP inputs inside the seam's `3 * zeta` budget. -/
theorem two_thirds_le_card_seamInputs_of_repairedDelta {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    {completeness soundness : ℝ}
    (parameters : ExecutableSoundnessParameters completeness soundness)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (hdistance :
      l1DistanceFromBoolean (honestOccurrenceFunction pcpp) guess ≤
        (repairedRecoveryDelta parameters : ℝ)) :
    (2 / 3 : ℝ) * ((2 ^ n : ℕ) : ℝ) ≤
      ((univ.filter fun input : BitInput n =>
          occurrenceSliceDistance (honestOccurrenceFunction pcpp) guess
              input ≤
            3 * (parameters.zeta : ℝ)).card : ℝ) := by
  have hpositive : (0 : ℝ) < (repairedRecoveryDelta parameters : ℝ) := by
    exact_mod_cast repairedRecoveryDelta_positive parameters
  have hbound :=
    two_thirds_le_card_seamInputs (honestOccurrenceFunction pcpp) guess
      (repairedRecoveryDelta parameters : ℝ) hpositive hdistance
  simpa only [repairedRecoveryDelta] using hbound

/-! ## §7 The transport at the scheduled Case-2 seed

`caseTwoSeed` is `fullyPaddedHonestOccurrenceFunction`, i.e. the honest
occurrence table of `padClauses` extended along the two ignored axes.  The
clause-address padding is already the honest occurrence table of a genuine
`PointwisePCPP` (`PCPPClausePadding.honestOccurrenceFunction_padClauses`), so
only the input-axis padding has to be moved through the slice, and it moves by
`prefixBits`.  Nothing in `§2`–`§4` changes. -/

/-- The restriction of a padded-cube guess to the native occurrence cube above
one padded PCPP input. -/
noncomputable def paddedInputSliceGuess {paddedInputBits nativeInputBits
    clauseBits : ℕ}
    (guess : BitInput (paddedInputBits + clauseBits + 1) → ℝ)
    (input : BitInput paddedInputBits)
    (address : BitInput (nativeInputBits + clauseBits + 1)) : ℝ :=
  guess
    (occurrenceAddress input (occurrenceClauseAddress address)
      (occurrencePosition address))

theorem projectPaddedSystematicOccurrenceInput_occurrenceAddress
    {nativeInputBits paddedInputBits clauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (input : BitInput paddedInputBits) (clause : BitInput clauseBits)
    (position : Bool) :
    projectPaddedSystematicOccurrenceInput
        hinput (occurrenceAddress input clause position) =
      occurrenceAddress (prefixBits hinput input) clause position := by
  apply (occurrenceCubeEquiv nativeInputBits clauseBits).symm.injective
  simp [occurrenceCubeEquiv,
    occurrenceInput_projectPaddedSystematic,
    occurrenceClauseAddress_projectPaddedSystematic,
    occurrencePosition_projectPaddedSystematic]

private theorem fullyPaddedHonestOccurrenceFunction_occurrenceAddress {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (paddedInputBits paddedClauseBits : ℕ) (hinput : n ≤ paddedInputBits)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits)
    (input : BitInput paddedInputBits) (clause : BitInput paddedClauseBits)
    (position : Bool) :
    fullyPaddedHonestOccurrenceFunction pcpp paddedInputBits paddedClauseBits
        hinput hclause (occurrenceAddress input clause position) =
      honestOccurrenceFunction (padClauses pcpp paddedClauseBits hclause)
        (occurrenceAddress (prefixBits hinput input) clause position) :=
  congrArg
    (honestOccurrenceFunction (padClauses pcpp paddedClauseBits hclause))
    (projectPaddedSystematicOccurrenceInput_occurrenceAddress hinput input
      clause position)

/-- The slice of the fully padded seed above a padded PCPP input is the slice
of the clause-padded honest occurrence table above its native prefix. -/
theorem occurrenceSliceDistance_fullyPadded {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (paddedInputBits paddedClauseBits : ℕ) (hinput : n ≤ paddedInputBits)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits)
    (guess : BitInput (paddedInputBits + paddedClauseBits + 1) → ℝ)
    (input : BitInput paddedInputBits) :
    occurrenceSliceDistance
        (fullyPaddedHonestOccurrenceFunction
          pcpp paddedInputBits paddedClauseBits hinput hclause)
        guess input =
      occurrenceSliceDistance
        (honestOccurrenceFunction
          (padClauses pcpp paddedClauseBits
            hclause))
        (paddedInputSliceGuess guess input) (prefixBits hinput input) := by
  unfold occurrenceSliceDistance
  refine Finset.expect_congr rfl fun slot _ => ?_
  rw [fullyPaddedHonestOccurrenceFunction_occurrenceAddress pcpp
    paddedInputBits paddedClauseBits hinput hclause input slot.1 slot.2]
  simp only [paddedInputSliceGuess,
    occurrenceClauseAddress_occurrenceAddress,
    occurrencePosition_occurrenceAddress]
  rfl

/-- **The transport at the scheduled Case-2 seed.**  Reading the guessed
padded occurrence table back to proof coordinates at one padded PCPP input
turns the verifier's clause-occurrence error, for the clause-padded pointwise
PCPP at the native prefix of that input, into the seed's own slice. -/
theorem clauseOccurrenceErrorMean_recoveredProofValue_fullyPadded {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (paddedInputBits paddedClauseBits : ℕ) (hinput : n ≤ paddedInputBits)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits)
    (guess : BitInput (paddedInputBits + paddedClauseBits + 1) → ℝ)
    (input : BitInput paddedInputBits)
    (hnonneg : ∀ address, 0 ≤ guess address)
    (hleOne : ∀ address, guess address ≤ 1) :
    clauseOccurrenceErrorMean
        (padClauses pcpp paddedClauseBits
          hclause)
        (recoveredProofValue
          (padClauses pcpp paddedClauseBits
            hclause)
          (paddedInputSliceGuess guess input) (prefixBits hinput input))
        (fun j =>
          bitAsReal
            (pcpp.assignment (prefixBits hinput input)
              (pcpp.honestAuxiliary (prefixBits hinput input)) j)) =
      occurrenceSliceDistance
        (fullyPaddedHonestOccurrenceFunction
          pcpp paddedInputBits paddedClauseBits hinput hclause)
        guess input := by
  rw [occurrenceSliceDistance_fullyPadded pcpp paddedInputBits
      paddedClauseBits hinput hclause guess input,
    ← clauseOccurrenceErrorMean_recoveredProofValue
      (padClauses pcpp paddedClauseBits
        hclause)
      (paddedInputSliceGuess guess input) (prefixBits hinput input)
      (fun _ => hnonneg _) (fun _ => hleOne _)]
  rfl

end NearCubicWires.OccurrenceSliceTransport
