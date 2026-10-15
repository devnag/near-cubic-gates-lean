import Proof.Foundations.RecoveryPipeline
import Proof.Foundations.SupplierPipeline

/-!
# Componentwise validity and common-function transfer

This module owns the finite algebra between the A.1/A.2 estimators and the
recovery dichotomy.  It proves the occurrence-averaging identity, coefficient
mass conservation, exact padding decomposition, and the logical extraction of
one function hard for both modes.  It does not assume an eventual circuit
lower bound or either headline theorem.
-/

namespace NearCubicWires.ComponentwiseTransfer

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

noncomputable def meanOn {ι : Type} (index : Finset ι) (value : ι → ℝ) : ℝ :=
  (∑ i ∈ index, value i) / index.card

/-- Averaging values in `[0,1]` against one common Boolean target commutes
exactly with absolute distance.  This is the load-bearing identity in the
common-function occurrence argument. -/
theorem distance_mean_to_common_bool
    {ι : Type} (index : Finset ι) (hne : index.Nonempty)
    (value : ι → ℝ) (target : Bool)
    (hvalue : ∀ i ∈ index, 0 ≤ value i ∧ value i ≤ 1) :
    |meanOn index value - bitAsReal target| =
      meanOn index (fun i => |value i - bitAsReal target|) := by
  have hcard : (0 : ℝ) < index.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  cases target with
  | false =>
      have hsum : 0 ≤ ∑ i ∈ index, value i :=
        Finset.sum_nonneg fun i hi => (hvalue i hi).1
      rw [show bitAsReal false = 0 by rfl]
      simp only [sub_zero, meanOn]
      rw [abs_of_nonneg (div_nonneg hsum (le_of_lt hcard))]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (abs_of_nonneg (hvalue i hi).1).symm
  | true =>
      have hsum :
          (∑ i ∈ index, value i) ≤ (index.card : ℝ) := by
        calc
          (∑ i ∈ index, value i) ≤ ∑ _i ∈ index, (1 : ℝ) :=
            Finset.sum_le_sum fun i hi => (hvalue i hi).2
          _ = index.card := by simp
      have hmean : meanOn index value ≤ 1 := by
        rw [meanOn]
        exact (div_le_one hcard).2 hsum
      rw [show bitAsReal true = 1 by rfl]
      rw [abs_of_nonpos (sub_nonpos.mpr hmean)]
      have hpoint :
          ∀ i ∈ index, |value i - 1| = 1 - value i := by
        intro i hi
        rw [abs_of_nonpos (sub_nonpos.mpr (hvalue i hi).2)]
        ring
      have hsumAbs :
          (∑ i ∈ index, |value i - 1|) =
            ∑ i ∈ index, (1 - value i) := by
        apply Finset.sum_congr rfl
        exact hpoint
      unfold meanOn
      rw [hsumAbs]
      have hsumSub :
          (∑ i ∈ index, (1 - value i)) =
            (index.card : ℝ) - ∑ i ∈ index, value i := by
        rw [Finset.sum_sub_distrib]
        simp
      rw [hsumSub]
      field_simp
      ring

/-- Occurrences naming the same PCPP proof variable. -/
def occurrenceFiber
    {Occurrence Variable : Type} [Fintype Occurrence] [DecidableEq Variable]
    (variableOf : Occurrence → Variable) (variableIndex : Variable) :
    Finset Occurrence :=
  Finset.univ.filter fun occurrence =>
    variableOf occurrence = variableIndex

/-- Average one guessed occurrence function over all aliases of a proof
variable.  Empty fibers are harmless because they are never read back through
an occurrence. -/
noncomputable def occurrenceAverage
    {Occurrence Variable : Type} [Fintype Occurrence] [DecidableEq Variable]
    (variableOf : Occurrence → Variable)
    (value : Occurrence → ℝ) (variableIndex : Variable) : ℝ :=
  meanOn (occurrenceFiber variableOf variableIndex) value

theorem occurrenceAverage_mem_unitInterval
    {Occurrence Variable : Type} [Fintype Occurrence] [DecidableEq Variable]
    (variableOf : Occurrence → Variable)
    (value : Occurrence → ℝ) (variableIndex : Variable)
    (hfiber : (occurrenceFiber variableOf variableIndex).Nonempty)
    (hvalue : ∀ occurrence, 0 ≤ value occurrence ∧ value occurrence ≤ 1) :
    0 ≤ occurrenceAverage variableOf value variableIndex ∧
      occurrenceAverage variableOf value variableIndex ≤ 1 := by
  let fiber := occurrenceFiber variableOf variableIndex
  have hcard : (0 : ℝ) < fiber.card := by
    exact_mod_cast Finset.card_pos.mpr hfiber
  constructor
  · unfold occurrenceAverage meanOn
    exact div_nonneg
      (Finset.sum_nonneg fun occurrence _ => (hvalue occurrence).1)
      (le_of_lt hcard)
  · unfold occurrenceAverage meanOn
    apply (div_le_one hcard).2
    calc
      (∑ occurrence ∈ fiber, value occurrence) ≤
          ∑ _occurrence ∈ fiber, (1 : ℝ) :=
        Finset.sum_le_sum fun occurrence _ => (hvalue occurrence).2
      _ = fiber.card := by simp

/-- Replacing every occurrence by its variable-fiber average preserves the
total `ℓ₁` distance to a Boolean table that is common on each fiber.  This is
the exact finite identity used in C.10.2; it does not lose a factor equal to
the maximum occurrence multiplicity. -/
theorem occurrenceAveraging_preserves_distance
    {Occurrence Variable : Type}
    [Fintype Occurrence] [DecidableEq Variable]
    (variableOf : Occurrence → Variable)
    (value : Occurrence → ℝ) (target : Variable → Bool)
    (hvalue : ∀ occurrence, 0 ≤ value occurrence ∧ value occurrence ≤ 1) :
    (∑ occurrence,
      |occurrenceAverage variableOf value (variableOf occurrence) -
        bitAsReal (target (variableOf occurrence))|) =
    ∑ occurrence,
      |value occurrence - bitAsReal (target (variableOf occurrence))| := by
  classical
  let variableSet := Finset.univ.image variableOf
  have hmaps :
      ∀ occurrence ∈ (Finset.univ : Finset Occurrence),
        variableOf occurrence ∈ variableSet := by
    intro occurrence hoccurrence
    exact Finset.mem_image.mpr ⟨occurrence, hoccurrence, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to (t := variableSet) hmaps
      (fun occurrence =>
        |occurrenceAverage variableOf value (variableOf occurrence) -
          bitAsReal (target (variableOf occurrence))|)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := variableSet) hmaps
      (fun occurrence =>
        |value occurrence - bitAsReal (target (variableOf occurrence))|)]
  apply Finset.sum_congr rfl
  intro variableIndex _
  let fiber := occurrenceFiber variableOf variableIndex
  by_cases hfiber : fiber.Nonempty
  · have havg :=
      distance_mean_to_common_bool fiber hfiber value (target variableIndex)
        (fun occurrence _ => hvalue occurrence)
    have hpositive : (0 : ℝ) < fiber.card := by
      exact_mod_cast Finset.card_pos.mpr hfiber
    have hleft :
        (∑ occurrence ∈ fiber,
          |occurrenceAverage variableOf value variableIndex -
            bitAsReal (target variableIndex)|) =
          fiber.card *
            |occurrenceAverage variableOf value variableIndex -
              bitAsReal (target variableIndex)| := by
      simp [mul_comm]
    have hright :
        (∑ occurrence ∈ fiber,
          |value occurrence - bitAsReal (target variableIndex)|) =
          fiber.card *
            meanOn fiber
              (fun occurrence =>
                |value occurrence - bitAsReal (target variableIndex)|) := by
      unfold meanOn
      field_simp
    rw [show
      (Finset.univ.filter fun occurrence =>
        variableOf occurrence = variableIndex) = fiber by rfl]
    have haverage :
        occurrenceAverage variableOf value variableIndex =
          meanOn fiber value := by
      rfl
    have hnormalizeLeft :
        (∑ occurrence ∈ fiber,
          |occurrenceAverage variableOf value (variableOf occurrence) -
            bitAsReal (target (variableOf occurrence))|) =
        ∑ occurrence ∈ fiber,
          |occurrenceAverage variableOf value variableIndex -
            bitAsReal (target variableIndex)| := by
      apply Finset.sum_congr rfl
      intro occurrence hoccurrence
      have hvariable : variableOf occurrence = variableIndex := by
        simpa only [fiber, occurrenceFiber, Finset.mem_filter,
          Finset.mem_univ, true_and] using hoccurrence
      rw [hvariable]
    have hnormalizeRight :
        (∑ occurrence ∈ fiber,
          |value occurrence -
            bitAsReal (target (variableOf occurrence))|) =
        ∑ occurrence ∈ fiber,
          |value occurrence - bitAsReal (target variableIndex)| := by
      apply Finset.sum_congr rfl
      intro occurrence hoccurrence
      have hvariable : variableOf occurrence = variableIndex := by
        simpa only [fiber, occurrenceFiber, Finset.mem_filter,
          Finset.mem_univ, true_and] using hoccurrence
      rw [hvariable]
    rw [hnormalizeLeft, hnormalizeRight, hleft, hright, haverage, havg]
  · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
    rw [show
      (Finset.univ.filter fun occurrence =>
        variableOf occurrence = variableIndex) = fiber by rfl, hempty]
    simp

/-- Flattening occurrence-wise sums with the uniform averaging coefficient
does not increase coefficient mass. -/
theorem averaged_coefficient_mass_le
    {Occurrence Term : Type} [Fintype Term]
    (occurrences : Finset Occurrence) (hne : occurrences.Nonempty)
    (coefficient : Occurrence → Term → ℝ) (mass : ℝ)
    (hmass : ∀ occurrence ∈ occurrences,
      (∑ term, |coefficient occurrence term|) ≤ mass) :
    (∑ occurrence ∈ occurrences,
      ∑ term, |coefficient occurrence term|) / occurrences.card ≤ mass := by
  have hcard : (0 : ℝ) < occurrences.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  apply (div_le_iff₀ hcard).2
  calc
    (∑ occurrence ∈ occurrences,
        ∑ term, |coefficient occurrence term|)
        ≤ ∑ _occurrence ∈ occurrences, mass :=
      Finset.sum_le_sum fun occurrence hoccurrence =>
        hmass occurrence hoccurrence
    _ = mass * occurrences.card := by
      simp [mul_comm]

/-- Occurrence averaging concatenates, but never composes, the restricted
atom lists.  Consequently the only term-count loss is the explicit number of
occurrences in the fiber. -/
theorem averaged_term_count_le
    {Occurrence : Type}
    (occurrences : Finset Occurrence)
    (termCount : Occurrence → ℕ) (bound : ℕ)
    (hbound : ∀ occurrence ∈ occurrences,
      termCount occurrence ≤ bound) :
    (∑ occurrence ∈ occurrences, termCount occurrence) ≤
      occurrences.card * bound := by
  calc
    (∑ occurrence ∈ occurrences, termCount occurrence) ≤
        ∑ _occurrence ∈ occurrences, bound :=
      Finset.sum_le_sum fun occurrence hoccurrence =>
        hbound occurrence hoccurrence
    _ = occurrences.card * bound := by simp

/-- Real-valued counterpart of the rational componentwise error ledger. -/
theorem componentwise_real_error
    {ι : Type} (index : Finset ι)
    (coefficient exact estimate : ι → ℝ) (error mass : ℝ)
    (herror : 0 ≤ error)
    (hpoint : ∀ i ∈ index, |estimate i - exact i| ≤ error)
    (hmass : (∑ i ∈ index, |coefficient i|) ≤ mass) :
    |(∑ i ∈ index, coefficient i * estimate i) -
        (∑ i ∈ index, coefficient i * exact i)| ≤ error * mass := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ i ∈ index, coefficient i * (estimate i - exact i)|
        ≤ ∑ i ∈ index,
          |coefficient i * (estimate i - exact i)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ index,
        |coefficient i| * |estimate i - exact i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i ∈ index, |coefficient i| * error := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (abs_nonneg _)
    _ = error * (∑ i ∈ index, |coefficient i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ error * mass :=
      mul_le_mul_of_nonneg_left hmass herror

def RejectsEveryLegalSum (family : SizedFunctionFamily) {n : ℕ}
    (function : BoolFunction n) (size termBound coefficientBitBound : ℕ)
    (coefficientMass delta : ℝ) : Prop :=
  ∀ sum : UnitIntervalCircuitSum family n size,
    sum.terms.length ≤ termBound →
    sum.coefficientsWithinBitBound coefficientBitBound →
    sum.coefficientMass ≤ coefficientMass →
    ¬l1DistanceFromBoolean function sum.value ≤ delta

/-- The semantic accepting relation implemented by one class branch of the
weak union machine. -/
def HasLegalApproximation (family : SizedFunctionFamily) {n : ℕ}
    (function : BoolFunction n) (size termBound coefficientBitBound : ℕ)
    (coefficientMass delta : ℝ) : Prop :=
  ∃ sum : UnitIntervalCircuitSum family n size,
    sum.terms.length ≤ termBound ∧
      sum.coefficientsWithinBitBound coefficientBitBound ∧
      sum.coefficientMass ≤ coefficientMass ∧
      l1DistanceFromBoolean function sum.value ≤ delta

theorem rejectsEveryLegalSum_iff_not_hasLegalApproximation
    {family : SizedFunctionFamily} {n : ℕ}
    {function : BoolFunction n} {size termBound coefficientBitBound : ℕ}
    {coefficientMass delta : ℝ} :
    RejectsEveryLegalSum family function size termBound
        coefficientBitBound coefficientMass delta ↔
      ¬HasLegalApproximation family function size termBound
        coefficientBitBound coefficientMass delta := by
  constructor
  · intro rejects approximation
    rcases approximation with ⟨sum, hterms, hbits, hmass, hclose⟩
    exact rejects sum hterms hbits hmass hclose
  · intro rejects sum hterms hbits hmass hclose
    exact rejects ⟨sum, hterms, hbits, hmass, hclose⟩

/-- The fixed weak machine is a finite union over class tags.  At the semantic
level, rejecting that union means rejecting each componentwise approximation
search separately. -/
def HasEitherLegalApproximation
    (symmetricFamily thresholdFamily : SizedFunctionFamily) {n : ℕ}
    (function : BoolFunction n)
    (symmetricSize symmetricTerms symmetricCoefficientBits
      thresholdSize thresholdTerms thresholdCoefficientBits : ℕ)
    (symmetricMass thresholdMass delta : ℝ) : Prop :=
  HasLegalApproximation symmetricFamily function symmetricSize symmetricTerms
      symmetricCoefficientBits symmetricMass delta ∨
    HasLegalApproximation thresholdFamily function thresholdSize thresholdTerms
      thresholdCoefficientBits thresholdMass delta

/-- Rejection of every syntactically legal approximation is exactly the strict
distance statement required by the CLW XOR interface. -/
theorem farFromCircuitSums_of_rejection
    {family : SizedFunctionFamily} {n : ℕ}
    {function : BoolFunction n} {size termBound coefficientBitBound : ℕ}
    {coefficientMass delta : ℝ}
    (rejects : RejectsEveryLegalSum family function size termBound
      coefficientBitBound coefficientMass delta) :
    FarFromCircuitSums family function size termBound coefficientBitBound
      coefficientMass delta := by
  intro sum hterms hbits hmass
  exact lt_of_not_ge (rejects sum hterms hbits hmass)

/-- One canonical proof-table function may be rejected in both modes before
either mode-specific contradiction is opened. -/
theorem commonFunctionFarFromBothModes
    {symmetricFamily thresholdFamily : SizedFunctionFamily} {n : ℕ}
    {function : BoolFunction n}
    {symmetricSize symmetricTerms symmetricCoefficientBits
      thresholdSize thresholdTerms thresholdCoefficientBits : ℕ}
    {symmetricMass thresholdMass delta : ℝ}
    (symmetricRejects :
      RejectsEveryLegalSum symmetricFamily function symmetricSize
        symmetricTerms symmetricCoefficientBits symmetricMass delta)
    (thresholdRejects :
      RejectsEveryLegalSum thresholdFamily function thresholdSize
        thresholdTerms thresholdCoefficientBits thresholdMass delta) :
    FarFromCircuitSums symmetricFamily function symmetricSize
        symmetricTerms symmetricCoefficientBits symmetricMass delta ∧
      FarFromCircuitSums thresholdFamily function thresholdSize
        thresholdTerms thresholdCoefficientBits thresholdMass delta :=
  ⟨farFromCircuitSums_of_rejection symmetricRejects,
    farFromCircuitSums_of_rejection thresholdRejects⟩

/-- Rejection of the one finite-mode search produces both exact XOR premises
for the same function. -/
theorem commonFunctionFarFromEitherRejection
    {symmetricFamily thresholdFamily : SizedFunctionFamily} {n : ℕ}
    {function : BoolFunction n}
    {symmetricSize symmetricTerms symmetricCoefficientBits
      thresholdSize thresholdTerms thresholdCoefficientBits : ℕ}
    {symmetricMass thresholdMass delta : ℝ}
    (rejects :
      ¬HasEitherLegalApproximation symmetricFamily thresholdFamily function
        symmetricSize symmetricTerms symmetricCoefficientBits
        thresholdSize thresholdTerms thresholdCoefficientBits
        symmetricMass thresholdMass delta) :
    FarFromCircuitSums symmetricFamily function symmetricSize
        symmetricTerms symmetricCoefficientBits symmetricMass delta ∧
      FarFromCircuitSums thresholdFamily function thresholdSize
        thresholdTerms thresholdCoefficientBits thresholdMass delta := by
  apply commonFunctionFarFromBothModes
  · rw [rejectsEveryLegalSum_iff_not_hasLegalApproximation]
    intro approximation
    exact rejects (Or.inl approximation)
  · rw [rejectsEveryLegalSum_iff_not_hasLegalApproximation]
    intro approximation
    exact rejects (Or.inr approximation)

/-- Package the rejected finite-mode search directly as the two-family XOR
input.  The term and coefficient envelopes use the source theorem's literal
`epsilon_k`; no target-advantage substitution occurs here. -/
noncomputable def commonXorInputOfEitherRejection
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (witness : XorAmplificationWitness)
    {seedArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ) (delta : ℝ)
    (deltaNonnegative : 0 ≤ delta)
    (deltaBelowHalf : delta < 1 / 2)
    (copiesPositive : 1 ≤ copies)
    (rejects :
      ¬HasEitherLegalApproximation symmetricFamily thresholdFamily seed
        symmetricSize
          ⌈witness.termCoefficient delta * seedArity /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound witness.coefficientBitCoefficient
            witness.coefficientBitDegree delta seedArity)
        thresholdSize
          ⌈witness.termCoefficient delta * seedArity /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound witness.coefficientBitCoefficient
            witness.coefficientBitDegree delta seedArity)
        (witness.massCoefficient delta / xorEpsilon delta copies)
        (witness.massCoefficient delta / xorEpsilon delta copies)
        delta) :
    CommonXorInput witness symmetricFamily thresholdFamily := by
  have far := commonFunctionFarFromEitherRejection rejects
  exact
    { seedArity := seedArity
      seed := seed
      copies := copies
      symmetricSize := symmetricSize
      thresholdSize := thresholdSize
      delta := delta
      deltaNonnegative := deltaNonnegative
      deltaBelowHalf := deltaBelowHalf
      copiesPositive := copiesPositive
      symmetricFar := far.1
      thresholdFar := far.2 }

/-- Turn rejection by the fixed executable union machine into the exact
two-family XOR input.  The only algorithm-specific obligation is the forward
direction proved for that machine: every legal decoded approximation creates
an accepting branch.  The refuter supplies `rejects`; no semantic rejection
predicate is accepted by the final recovery constructor. -/
noncomputable def commonXorInputOfMachineRejection
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (witness : XorAmplificationWitness)
    {seedArity inputArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ) (delta : ℝ)
    (deltaNonnegative : 0 ≤ delta)
    (deltaBelowHalf : delta < 1 / 2)
    (copiesPositive : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    (input : BitInput inputArity)
    (acceptsOfApproximation :
      HasEitherLegalApproximation symmetricFamily thresholdFamily seed
        symmetricSize
          ⌈witness.termCoefficient delta * seedArity /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound witness.coefficientBitCoefficient
            witness.coefficientBitDegree delta seedArity)
        thresholdSize
          ⌈witness.termCoefficient delta * seedArity /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound witness.coefficientBitCoefficient
            witness.coefficientBitDegree delta seedArity)
        (witness.massCoefficient delta / xorEpsilon delta copies)
        (witness.massCoefficient delta / xorEpsilon delta copies)
        delta →
      machine.toSemantic.accepts input)
    (rejects : ¬machine.toSemantic.accepts input) :
    CommonXorInput witness symmetricFamily thresholdFamily :=
  commonXorInputOfEitherRejection witness seed copies
    symmetricSize thresholdSize delta deltaNonnegative deltaBelowHalf
    copiesPositive (fun approximation =>
      rejects (acceptsOfApproximation approximation))

/-- A semantic family adapter contains only the concrete one-length simulation
needed to reuse a general-circuit hard core. -/
structure FamilySimulation (family : SizedFunctionFamily) where
  simulate : ∀ {n : ℕ} {function : BoolFunction n} {size : ℕ},
    family n function size → booleanCircuitFamily n function size

def HardCore.mapFamily
    {family : SizedFunctionFamily}
    (core : HardCore booleanCircuitFamily)
    (simulation : FamilySimulation family) :
    HardCore family where
  arity := core.arity
  function := core.function
  size := core.size
  advantage := core.advantage
  hard := by
    intro candidate hcandidate
    exact core.hard candidate (simulation.simulate hcandidate)

def commonHardCoreFromCaseOne
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (core : HardCore booleanCircuitFamily)
    (symmetricSimulation : FamilySimulation symmetricFamily)
    (thresholdSimulation : FamilySimulation thresholdFamily) :
    CommonHardCore symmetricFamily thresholdFamily where
  arity := core.arity
  function := core.function
  symmetricSize := core.size
  thresholdSize := core.size
  advantage := core.advantage
  symmetricHard := (HardCore.mapFamily core symmetricSimulation).hard
  thresholdHard := (HardCore.mapFamily core thresholdSimulation).hard

/-! ## Exact real-valued padding transfer -/

/-- Indicator form of uniform Boolean agreement.  Writing agreement as an
expectation makes the restriction argument use the same averaging operator as
the componentwise supplier ledger. -/
noncomputable def agreementIndicator {n : ℕ}
    (left right : BoolFunction n) (input : BitInput n) : ℝ :=
  if left input = right input then 1 else 0

theorem agreement_eq_expect {n : ℕ}
    (left right : BoolFunction n) :
    agreement left right =
      𝔼 input, agreementIndicator left right input := by
  classical
  simp [agreement, Finset.expect, agreementIndicator, div_eq_inv_mul,
    NNRat.smul_def]

/-- Canonical decomposition of a target assignment into the scheduled core
coordinates and the padding coordinates. -/
def splitAssignmentEquiv {core target : ℕ} (hcore : core ≤ target) :
    BitInput target ≃ BitInput core × BitInput (target - core) where
  toFun input :=
    (fun index => input (finSplitEquiv hcore (.inl index)),
      fun index => input (finSplitEquiv hcore (.inr index)))
  invFun splitInput := fun index =>
    Sum.elim splitInput.1 splitInput.2 ((finSplitEquiv hcore).symm index)
  left_inv := by
    intro input
    funext index
    generalize hsplit :
      (finSplitEquiv hcore).symm index = splitInput
    cases splitInput with
    | inl coreIndex =>
        simp only [hsplit, Sum.elim_inl]
        have hindex := congrArg (finSplitEquiv hcore) hsplit
        simp only [Equiv.apply_symm_apply] at hindex
        rw [← hindex]
    | inr paddingIndex =>
        simp only [hsplit, Sum.elim_inr]
        have hindex := congrArg (finSplitEquiv hcore) hsplit
        simp only [Equiv.apply_symm_apply] at hindex
        rw [← hindex]
  right_inv := by
    rintro ⟨coreInput, padding⟩
    apply Prod.ext <;> funext index <;> simp

/-- Exact Fubini identity: agreement with an ignored-variable extension is
the average agreement of all canonical restrictions. -/
theorem agreement_padCore_eq_expect_restrictions
    {core target : ℕ} (candidate : BoolFunction target)
    (function : BoolFunction core) (hcore : core ≤ target) :
    agreement candidate (padCore function hcore) =
      𝔼 padding : BitInput (target - core),
        agreement (restrictTarget candidate hcore padding) function := by
  rw [agreement_eq_expect]
  calc
    (𝔼 input : BitInput target,
        agreementIndicator candidate (padCore function hcore) input) =
        𝔼 splitInput : BitInput core × BitInput (target - core),
          agreementIndicator candidate (padCore function hcore)
            ((splitAssignmentEquiv hcore).symm splitInput) := by
      apply Finset.expect_equiv (splitAssignmentEquiv hcore)
      · simp
      · intro input _
        simp
    _ = 𝔼 coreInput : BitInput core,
          𝔼 padding : BitInput (target - core),
            agreementIndicator
              (restrictTarget candidate hcore padding) function coreInput := by
      rw [← Finset.univ_product_univ]
      rw [Finset.expect_product]
      apply Finset.expect_congr rfl
      intro coreInput _
      apply Finset.expect_congr rfl
      intro padding _
      simp [agreementIndicator, splitAssignmentEquiv, restrictTarget,
        padCore]
    _ = 𝔼 padding : BitInput (target - core),
          𝔼 coreInput : BitInput core,
            agreementIndicator
              (restrictTarget candidate hcore padding) function coreInput := by
      exact Finset.expect_comm _ _ _
    _ = 𝔼 padding : BitInput (target - core),
        agreement (restrictTarget candidate hcore padding) function := by
      apply Finset.expect_congr rfl
      intro padding _
      rw [agreement_eq_expect]

/-- A size-indexed semantic family is restriction closed when fixing padding
coordinates never increases its charged size. -/
def RestrictionClosed (family : SizedFunctionFamily) : Prop :=
  ∀ {core target size : ℕ} (candidate : BoolFunction target)
    (hcore : core ≤ target),
    family target candidate size →
      ∀ padding : BitInput (target - core),
        family core (restrictTarget candidate hcore padding) size

/-- The local restriction-closure predicate *is* the closure hypothesis the XOR
source contract now carries.  Both sides unfold to the same statement:
`restrictTarget` and `SourceInterfaces.sourceFinSplitEquiv` are delta-equal to
the inlined body used upstream, so no transport is involved. -/
theorem RestrictionClosed.toSourceFamily {family : SizedFunctionFamily}
    (closed : RestrictionClosed family) :
    SourceInterfaces.RestrictionClosedFamily family :=
  closed

/-- Exact padding theorem for every restriction-closed family.  No asymptotic
or schedule premise is hidden here: the core size and advantage are preserved
literally. -/
theorem averageHard_padCore
    {family : SizedFunctionFamily} (closed : RestrictionClosed family)
    {core target size : ℕ} {function : BoolFunction core} {advantage : ℝ}
    (hard : AverageHardAt family function size advantage)
    (hcore : core ≤ target) :
    AverageHardAt family (padCore function hcore) size advantage := by
  intro candidate hcandidate
  rw [agreement_padCore_eq_expect_restrictions]
  apply Finset.expect_le Finset.univ_nonempty
  intro padding _
  exact hard (restrictTarget candidate hcore padding)
    (closed candidate hcore hcandidate padding)

/-- Pad both ledgers of one common hard core through the same coordinate
embedding.  The function is frozen once; only the two restriction-closure
proofs differ by family. -/
noncomputable def padCommonHardCore
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (symmetricClosed : RestrictionClosed symmetricFamily)
    (thresholdClosed : RestrictionClosed thresholdFamily)
    (core : CommonHardCore symmetricFamily thresholdFamily)
    (target : ℕ) (hcore : core.arity ≤ target) :
    CommonHardCore symmetricFamily thresholdFamily where
  arity := target
  function := padCore core.function hcore
  symmetricSize := core.symmetricSize
  thresholdSize := core.thresholdSize
  advantage := core.advantage
  symmetricHard :=
    averageHard_padCore
      (family := symmetricFamily) (core := core.arity) (target := target)
      (size := core.symmetricSize)
      symmetricClosed core.symmetricHard hcore
  thresholdHard :=
    averageHard_padCore
      (family := thresholdFamily) (core := core.arity) (target := target)
      (size := core.thresholdSize)
      thresholdClosed core.thresholdHard hcore

@[simp] theorem padCommonHardCore_arity
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (symmetricClosed : RestrictionClosed symmetricFamily)
    (thresholdClosed : RestrictionClosed thresholdFamily)
    (core : CommonHardCore symmetricFamily thresholdFamily)
    (target : ℕ) (hcore : core.arity ≤ target) :
    (padCommonHardCore
      (symmetricFamily := symmetricFamily)
      (thresholdFamily := thresholdFamily)
      symmetricClosed thresholdClosed core target hcore).arity = target :=
  rfl

end NearCubicWires.ComponentwiseTransfer
