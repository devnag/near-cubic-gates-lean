import Proof.Foundations.AppendixC
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.StrictLayerAdapters

/-!
# Executable Appendix-C recovery pipeline

This module isolates the reusable transfer objects between the published
source interfaces and the concrete headline circuit bounds.  Closed source
assembly lives downstream; this file does not export a caller-supplied
composition, branch-builder, or headline premise.

The machine lemmas are deliberately about `runNPOracleProgram` itself.  In
particular, a semantic language evaluator or a runtime number unattached to an
execution trace cannot be promoted to `InENP`.
-/

namespace NearCubicWires.RecoveryPipeline

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-! ## Exponential absorption -/

/-- Number of exponent bits needed to absorb a fixed multiplicative
coefficient into the canonical `2^(O(n))` machine budget. -/
def coefficientExponent (coefficient : ℕ) : ℕ :=
  Nat.log 2 coefficient + 1

theorem coefficientExponent_positive (coefficient : ℕ) :
    0 < coefficientExponent coefficient := by
  simp [coefficientExponent]

theorem coefficient_le_two_pow (coefficient : ℕ) :
    coefficient ≤ 2 ^ coefficientExponent coefficient := by
  exact Nat.le_of_lt (by
    simpa [coefficientExponent, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) coefficient))

/-- A fixed multiplicative runtime/register overhead costs one fixed additive
term in the exponent.  The target length is required to be positive because
the canonical certificate has no separate constant factor. -/
theorem scaledExponential_le (coefficient rate n : ℕ) (hn : 1 ≤ n) :
    coefficient * 2 ^ (rate * n) ≤
      2 ^ ((rate + coefficientExponent coefficient) * n) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hexponent :
      coefficientExponent coefficient ≤ coefficientExponent coefficient * n :=
    Nat.le_mul_of_pos_right _ hnpos
  have hcoefficient :
      coefficient ≤ 2 ^ (coefficientExponent coefficient * n) :=
    le_trans (coefficient_le_two_pow coefficient)
      (Nat.pow_le_pow_right (by omega) hexponent)
  calc
    coefficient * 2 ^ (rate * n) ≤
        2 ^ (coefficientExponent coefficient * n) * 2 ^ (rate * n) :=
      Nat.mul_le_mul_right _ hcoefficient
    _ = 2 ^ ((rate + coefficientExponent coefficient) * n) := by
      rw [← Nat.pow_add, Nat.add_mul, Nat.add_comm]

/-! ## Fixed refuter dichotomy -/

/-- An executable refuter chosen once for one time bound.  Its runner,
coefficient, degree, and hierarchy cannot depend on the subsequently supplied
machine or length. -/
structure FixedRefuterWitness (hierarchy : Language) (bound : ℕ → ℕ) where
  refuter : ExecutableSATOracleRefuter hierarchy bound
  sound : ∀ machine : ExecutableWeakNondeterministicMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine n) ↔
        hierarchy n (refuter.output machine n) = false)

theorem existsFixedRefuterWitness
    (contract : ExecutableRefuterContract) (bound : ℕ → ℕ)
    (admissible : RefuterClockAdmissible bound) :
    ∃ hierarchy, Nonempty (FixedRefuterWitness hierarchy bound) := by
  rcases contract bound admissible with ⟨source⟩
  exact
    ⟨source.hierarchyMachine.accepts,
      ⟨source.refuter, source.sound⟩⟩

theorem refuter_truth_dichotomy
    {hierarchy : Language} {machine : WeakNondeterministicMachine} {n : ℕ}
    (input : BitInput n)
    (hrefute : machine.accepts input ↔ hierarchy n input = false) :
    machine.accepts input ∨ hierarchy n input = true := by
  cases hvalue : hierarchy n input with
  | false =>
      exact Or.inl (hrefute.mpr hvalue)
  | true =>
      exact Or.inr rfl

theorem FixedRefuterWitness.eventualDichotomy
    {hierarchy : Language} {bound : ℕ → ℕ}
    (fixed : FixedRefuterWitness hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (hruntime : RunsInLittleO machine.toSemantic bound)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10) :
    ∃ onset, ∀ n, onset ≤ n →
      fixed.refuter.budget n ≤
          fixed.refuter.runner.coefficient *
            (bound n + 1) ^ fixed.refuter.runner.degree ∧
      (machine.toSemantic.accepts (fixed.refuter.output machine n) ∨
        hierarchy n (fixed.refuter.output machine n) = true) := by
  rcases fixed.sound machine hruntime hwitness with ⟨onset, hsound⟩
  refine ⟨onset, ?_⟩
  intro n hn
  exact ⟨le_rfl,
    refuter_truth_dichotomy (fixed.refuter.output machine n) (hsound n hn)⟩

/-- The fixed componentwise machine is one-sided for the hierarchy language:
on hierarchy NO instances every nondeterministic branch rejects. -/
def EventuallyOneSided (hierarchy : Language)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  ∃ onset, ∀ n, onset ≤ n → ∀ input : BitInput n,
    hierarchy n input = false → ¬machine.toSemantic.accepts input

/-- One-sidedness eliminates the accepting side of the raw refuter
dichotomy.  The later Case-1/Case-2 split therefore happens inside one
hierarchy-YES instance, as in Appendix C.10. -/
theorem FixedRefuterWitness.eventualHierarchyTruth
    {hierarchy : Language} {bound : ℕ → ℕ}
    (fixed : FixedRefuterWitness hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (hruntime : RunsInLittleO machine.toSemantic bound)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10)
    (honeSided : EventuallyOneSided hierarchy machine) :
    ∃ onset, ∀ n, onset ≤ n →
      fixed.refuter.budget n ≤
          fixed.refuter.runner.coefficient *
            (bound n + 1) ^ fixed.refuter.runner.degree ∧
      hierarchy n (fixed.refuter.output machine n) = true := by
  rcases fixed.sound machine hruntime hwitness with
    ⟨refuterOnset, hrefuter⟩
  rcases honeSided with ⟨oneSidedOnset, honeSided⟩
  refine ⟨max refuterOnset oneSidedOnset, ?_⟩
  intro n hn
  have hrefuterReady : refuterOnset ≤ n :=
    le_trans (le_max_left _ _) hn
  have honeSidedReady : oneSidedOnset ≤ n :=
    le_trans (le_max_right _ _) hn
  refine ⟨le_rfl, ?_⟩
  cases hvalue :
      hierarchy n (fixed.refuter.output machine n) with
  | false =>
      exfalso
      exact
        (honeSided n honeSidedReady
          (fixed.refuter.output machine n) hvalue)
          ((hrefuter n hrefuterReady).mpr hvalue)
  | true =>
      rfl

/-- The refuter word is the actual conflict consumed by Case 2: it is a
hierarchy-YES word and the fixed finite-mode machine rejects it.  Returning
both facts together avoids reconstructing rejection later from an unrelated
semantic language equality. -/
theorem FixedRefuterWitness.eventualConflict
    {hierarchy : Language} {bound : ℕ → ℕ}
    (fixed : FixedRefuterWitness hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (hruntime : RunsInLittleO machine.toSemantic bound)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10)
    (honeSided : EventuallyOneSided hierarchy machine) :
    ∃ onset, ∀ n, onset ≤ n →
      fixed.refuter.budget n ≤
          fixed.refuter.runner.coefficient *
            (bound n + 1) ^ fixed.refuter.runner.degree ∧
      hierarchy n (fixed.refuter.output machine n) = true ∧
      ¬machine.toSemantic.accepts (fixed.refuter.output machine n) := by
  rcases fixed.eventualHierarchyTruth machine hruntime hwitness honeSided with
    ⟨truthOnset, htruth⟩
  rcases fixed.sound machine hruntime hwitness with
    ⟨soundOnset, hsound⟩
  refine ⟨max truthOnset soundOnset, ?_⟩
  intro n hn
  have htruthReady : truthOnset ≤ n :=
    le_trans (le_max_left _ _) hn
  have hsoundReady : soundOnset ≤ n :=
    le_trans (le_max_right _ _) hn
  rcases htruth n htruthReady with ⟨hbudget, hyes⟩
  refine ⟨hbudget, hyes, ?_⟩
  intro haccepts
  have hno := (hsound n hsoundReady).mp haccepts
  rw [hyes] at hno
  contradiction

/-! ## XOR and Case-1 amplification into one per-core type -/

/-- Concrete average-case hardness at one arity and one size cap. -/
def AverageHardAt (family : SizedFunctionFamily) {n : ℕ}
    (function : BoolFunction n) (size : ℕ) (advantage : ℝ) : Prop :=
  ∀ candidate : BoolFunction n, family n candidate size →
    agreement candidate function ≤ 1 / 2 + advantage

/-- Ordinary fan-in-two circuits embedded into the common semantic family used
by the XOR source theorem. -/
def booleanCircuitFamily : SizedFunctionFamily :=
  fun n function size =>
    ∃ circuit : BooleanCircuit n,
      circuit.size ≤ size ∧ circuit.eval = function

/-- A per-core result records only one function, cap, and advantage.  It does
not quantify over all large lengths and is therefore strictly below either
headline theorem. -/
structure HardCore (family : SizedFunctionFamily) where
  arity : ℕ
  function : BoolFunction arity
  size : ℕ
  advantage : ℝ
  hard : AverageHardAt family function size advantage

/-- Explicit witness obtained by opening the existential in `XorContract`. -/
structure XorAmplificationWitness where
  termCoefficient : ℝ → ℝ
  massCoefficient : ℝ → ℝ
  coefficientBitCoefficient : ℝ → ℕ
  coefficientBitDegree : ℝ → ℕ
  sound : ∀ (delta : ℝ), 0 ≤ delta → delta < 1 / 2 →
    0 < termCoefficient delta ∧ 0 < massCoefficient delta ∧
    0 < coefficientBitCoefficient delta ∧
    ∀ (family : SizedFunctionFamily), RestrictionClosedFamily family →
      NegationClosedFamily family →
      ∀ {n : ℕ} (function : BoolFunction n) (k size : ℕ), 1 ≤ k →
      let epsilon := xorEpsilon delta k
      FarFromCircuitSums family function size
        ⌈termCoefficient delta * n / epsilon ^ 2⌉₊
        (xorCoefficientBitBound coefficientBitCoefficient
          coefficientBitDegree delta n)
        (massCoefficient delta / epsilon) delta →
      ∀ candidate : BoolFunction (k * n),
        family (k * n) candidate size →
        agreement candidate (xorPower function k) ≤ 1 / 2 + epsilon

theorem existsXorAmplificationWitness (contract : XorContract) :
    Nonempty XorAmplificationWitness := by
  rcases contract with
    ⟨termCoefficient, massCoefficient, coefficientBitCoefficient,
      coefficientBitDegree, hsound⟩
  exact
    ⟨termCoefficient, massCoefficient, coefficientBitCoefficient,
      coefficientBitDegree, hsound⟩

structure XorCaseInput (witness : XorAmplificationWitness)
    (family : SizedFunctionFamily) where
  seedArity : ℕ
  seed : BoolFunction seedArity
  copies : ℕ
  size : ℕ
  delta : ℝ
  deltaNonnegative : 0 ≤ delta
  deltaBelowHalf : delta < 1 / 2
  copiesPositive : 1 ≤ copies
  far : FarFromCircuitSums family seed size
    ⌈witness.termCoefficient delta * seedArity /
      xorEpsilon delta copies ^ 2⌉₊
    (xorCoefficientBitBound witness.coefficientBitCoefficient
      witness.coefficientBitDegree delta seedArity)
    (witness.massCoefficient delta / xorEpsilon delta copies) delta

noncomputable def hardCoreFromXor
    {witness : XorAmplificationWitness} {family : SizedFunctionFamily}
    (input : XorCaseInput witness family)
    (closed : RestrictionClosedFamily family)
    (negationClosed : NegationClosedFamily family) :
    HardCore family where
  arity := input.copies * input.seedArity
  function := xorPower input.seed input.copies
  size := input.size
  advantage := xorEpsilon input.delta input.copies
  hard := by
    rcases witness.sound input.delta input.deltaNonnegative
      input.deltaBelowHalf with ⟨_, _, _, hsound⟩
    exact hsound family closed negationClosed input.seed input.copies input.size
      input.copiesPositive input.far

/-- The Case-2 occurrence table is chosen before the class mode.  It is far
from legal sums in both families, with separate componentwise size caps. -/
structure CommonXorInput (witness : XorAmplificationWitness)
    (symmetricFamily thresholdFamily : SizedFunctionFamily) where
  seedArity : ℕ
  seed : BoolFunction seedArity
  copies : ℕ
  symmetricSize : ℕ
  thresholdSize : ℕ
  delta : ℝ
  deltaNonnegative : 0 ≤ delta
  deltaBelowHalf : delta < 1 / 2
  copiesPositive : 1 ≤ copies
  symmetricFar : FarFromCircuitSums symmetricFamily seed symmetricSize
    ⌈witness.termCoefficient delta * seedArity /
      xorEpsilon delta copies ^ 2⌉₊
    (xorCoefficientBitBound witness.coefficientBitCoefficient
      witness.coefficientBitDegree delta seedArity)
    (witness.massCoefficient delta / xorEpsilon delta copies) delta
  thresholdFar : FarFromCircuitSums thresholdFamily seed thresholdSize
    ⌈witness.termCoefficient delta * seedArity /
      xorEpsilon delta copies ^ 2⌉₊
    (xorCoefficientBitBound witness.coefficientBitCoefficient
      witness.coefficientBitDegree delta seedArity)
    (witness.massCoefficient delta / xorEpsilon delta copies) delta

/-- One truth table and advantage with distinct size ledgers for the two
physical circuit modes. -/
structure CommonHardCore
    (symmetricFamily thresholdFamily : SizedFunctionFamily) where
  arity : ℕ
  function : BoolFunction arity
  symmetricSize : ℕ
  thresholdSize : ℕ
  advantage : ℝ
  symmetricHard :
    AverageHardAt symmetricFamily function symmetricSize advantage
  thresholdHard :
    AverageHardAt thresholdFamily function thresholdSize advantage

/-- Apply the imported XOR theorem componentwise while retaining one common
truth table. -/
noncomputable def commonHardCoreFromXor
    {witness : XorAmplificationWitness}
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (input : CommonXorInput witness symmetricFamily thresholdFamily)
    (symmetricClosed : RestrictionClosedFamily symmetricFamily)
    (thresholdClosed : RestrictionClosedFamily thresholdFamily)
    (symmetricNegationClosed : NegationClosedFamily symmetricFamily)
    (thresholdNegationClosed : NegationClosedFamily thresholdFamily) :
    CommonHardCore symmetricFamily thresholdFamily where
  arity := input.copies * input.seedArity
  function := xorPower input.seed input.copies
  symmetricSize := input.symmetricSize
  thresholdSize := input.thresholdSize
  advantage := xorEpsilon input.delta input.copies
  symmetricHard := by
    rcases witness.sound input.delta input.deltaNonnegative
      input.deltaBelowHalf with ⟨_, _, _, hsound⟩
    exact
      hsound symmetricFamily symmetricClosed symmetricNegationClosed input.seed input.copies
        input.symmetricSize input.copiesPositive input.symmetricFar
  thresholdHard := by
    rcases witness.sound input.delta input.deltaNonnegative
      input.deltaBelowHalf with ⟨_, _, _, hsound⟩
    exact
      hsound thresholdFamily thresholdClosed thresholdNegationClosed input.seed input.copies
        input.thresholdSize input.copiesPositive input.thresholdFar

@[simp] theorem commonHardCoreFromXor_arity
    {witness : XorAmplificationWitness}
    {symmetricFamily thresholdFamily : SizedFunctionFamily}
    (input : CommonXorInput witness symmetricFamily thresholdFamily)
    (symmetricClosed : RestrictionClosedFamily symmetricFamily)
    (thresholdClosed : RestrictionClosedFamily thresholdFamily)
    (symmetricNegationClosed : NegationClosedFamily symmetricFamily)
    (thresholdNegationClosed : NegationClosedFamily thresholdFamily) :
    (commonHardCoreFromXor input symmetricClosed thresholdClosed
      symmetricNegationClosed thresholdNegationClosed).arity =
      input.copies * input.seedArity :=
  rfl

/-- Explicit fixed executable algorithm and constants extracted from the
strengthened STV source contract. -/
structure AmplifierWitness where
  algorithm : ExecutableWorstCaseAmplifierAlgorithm
  stvExponent : ℕ
  arityCoefficient : ℕ
  stvExponentPositive : 1 ≤ stvExponent
  arityCoefficientPositive : 1 ≤ arityCoefficient
  sound : ∀ (sizeBound : ℕ → ℕ), TimeConstructible sizeBound →
    ∀ (n : ℕ) (function : BoolFunction n),
      WorstCaseHardAt function (sizeBound n) →
      let output := algorithm.amplify n function
      output.outputArity ≤ arityCoefficient * n ∧
        (∀ circuit : BooleanCircuit output.outputArity,
          circuit.size ≤ integerFloorRoot stvExponent (sizeBound n) →
          agreement circuit.eval output.function ≤
            1 / 2 + Real.rpow (sizeBound n : ℝ)
              (-(1 : ℝ) / stvExponent))

theorem existsAmplifierWitness (contract : ExecutableWorstCaseAmplifierContract) :
    Nonempty AmplifierWitness := by
  rcases contract with
    ⟨algorithm, stvExponent, arityCoefficient, hstv, harity, hsound⟩
  exact ⟨algorithm, stvExponent, arityCoefficient, hstv, harity, hsound⟩

structure CaseOneInput (witness : AmplifierWitness) where
  sizeBound : ℕ → ℕ
  constructible : TimeConstructible sizeBound
  seedArity : ℕ
  seed : BoolFunction seedArity
  worstCaseHard : WorstCaseHardAt seed (sizeBound seedArity)

noncomputable def hardCoreFromCaseOne
    {witness : AmplifierWitness} (input : CaseOneInput witness) :
    HardCore booleanCircuitFamily := by
  let output := witness.algorithm.amplify input.seedArity input.seed
  refine
    { arity := output.outputArity
      function := output.function
      size := integerFloorRoot witness.stvExponent
        (input.sizeBound input.seedArity)
      advantage := Real.rpow (input.sizeBound input.seedArity : ℝ)
        (-(1 : ℝ) / witness.stvExponent)
      hard := ?_ }
  intro candidate hcandidate
  rcases hcandidate with ⟨circuit, hsize, heval⟩
  subst candidate
  exact
    (witness.sound input.sizeBound input.constructible
      input.seedArity input.seed input.worstCaseHard).2 circuit hsize

@[simp] theorem hardCoreFromCaseOne_arity
    {witness : AmplifierWitness} (input : CaseOneInput witness) :
    (hardCoreFromCaseOne input).arity =
      (witness.algorithm.amplify input.seedArity input.seed).outputArity := by
  simp [hardCoreFromCaseOne]

/-! ## Bounded-jump scheduling and exact padding -/

/-- One target-length selection with the Appendix-C half-crossing and
one-sixth jump inequalities written without division or subtraction. -/
structure BoundedJumpSelection (target : ℕ) where
  core : ℕ
  next : ℕ
  coreAtMostTarget : core ≤ target
  crossesHalf : target < 2 * next
  jumpAtMostSixth : 6 * next ≤ 6 * core + target

theorem BoundedJumpSelection.target_lt_three_core
    {target : ℕ} (selection : BoundedJumpSelection target) :
    target < 3 * selection.core := by
  have hcross :=
    (Nat.mul_lt_mul_left (by omega : 0 < 3)).2 selection.crossesHalf
  have hjump := selection.jumpAtMostSixth
  omega

theorem BoundedJumpSelection.core_positive
    {target : ℕ} (selection : BoundedJumpSelection target) :
    0 < selection.core := by
  have := selection.target_lt_three_core
  omega

/-- Canonical decoded output of the fixed target-to-source selector.  Both
source indices are retained because the half-crossing proof concerns
consecutive source instances, whereas the language is indexed by `target`. -/
structure ExecutableScheduleSelection where
  source : ℕ
  nextSource : ℕ
  core : ℕ
  nextCore : ℕ

def ExecutableScheduleSelection.code
    (selection : ExecutableScheduleSelection) : ℕ :=
  Nat.pair selection.source
    (Nat.pair selection.nextSource
      (Nat.pair selection.core selection.nextCore))

def ExecutableScheduleSelection.decode (code : ℕ) :
    ExecutableScheduleSelection :=
  { source := (Nat.unpair code).1
    nextSource := (Nat.unpair (Nat.unpair code).2).1
    core := (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).1
    nextCore := (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2 }

@[simp] theorem ExecutableScheduleSelection.decode_code
    (selection : ExecutableScheduleSelection) :
    ExecutableScheduleSelection.decode selection.code = selection := by
  cases selection
  simp [ExecutableScheduleSelection.decode, ExecutableScheduleSelection.code]

@[simp] theorem ExecutableScheduleSelection.code_decode (code : ℕ) :
    (ExecutableScheduleSelection.decode code).code = code := by
  simp [ExecutableScheduleSelection.decode, ExecutableScheduleSelection.code]

def finSplitEquiv {core target : ℕ} (hcore : core ≤ target) :
    Fin core ⊕ Fin (target - core) ≃ Fin target :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hcore))

/-- Pad a core truth table by ignoring the right summand of a canonical split
of the target coordinates. -/
def padCore {core target : ℕ} (function : BoolFunction core)
    (hcore : core ≤ target) : BoolFunction target :=
  fun input =>
    function fun index => input (finSplitEquiv hcore (.inl index))

/-- Fix all non-core coordinates of a target truth table. -/
def restrictTarget {core target : ℕ} (function : BoolFunction target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    BoolFunction core :=
  fun input =>
    function fun index =>
      Sum.elim input padding ((finSplitEquiv hcore).symm index)

theorem restrict_padCore_roundTrip {core target : ℕ}
    (function : BoolFunction core) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    restrictTarget (padCore function hcore) hcore padding = function := by
  funext input
  simp [restrictTarget, padCore, finSplitEquiv]

/-- The finite averaging statement used in the padding contrapositive, now
specialized to the canonical `Fin core ⊕ Fin padding` split. -/
theorem existsRestrictionForTarget
    {core target : ℕ} (candidate : BoolFunction target)
    (function : BoolFunction core) (hcore : core ≤ target) :
    ∃ padding : BitInput (target - core),
      AppendixC.paddedAgreement
        (fun padding input => restrictTarget candidate hcore padding input)
        function ≤
      AppendixC.sliceAgreement
        (fun padding input => restrictTarget candidate hcore padding input)
        function padding := by
  exact AppendixC.existsRestrictionPreservingAgreement
    (fun padding input => restrictTarget candidate hcore padding input)
    function

/-- The schedule ratio supplies exactly the integer reserve needed to lose one
advantage exponent during padding. -/
theorem scheduledPaddingReserve
    {target c : ℕ} (selection : BoundedJumpSelection target)
    (hlarge : 3 ^ c < selection.core) :
    target ^ c < selection.core ^ (c + 1) :=
  AppendixC.integerPaddingAdvantageReserve target selection.core c
    selection.core_positive
    (Nat.le_of_lt selection.target_lt_three_core)
    hlarge

/-- Exact strictness conversion used by Theorem 2.3: a low-agreement theorem
for every circuit at or below a real cap contraposes to a strict wire lower
bound at the agreement threshold. -/
theorem strictWireLowerBound_of_capHard
    (wires : ℕ) (cap agreementValue threshold : ℝ)
    (hardBelowCap :
      (wires : ℝ) ≤ cap → agreementValue < threshold)
    (highAgreement : threshold ≤ agreementValue) :
    cap < wires := by
  by_contra hcap
  have hwires : (wires : ℝ) ≤ cap := le_of_not_gt hcap
  exact (not_lt_of_ge highAgreement) (hardBelowCap hwires)

/-- A one-length padding adapter for two concrete target classes.  Its premise
is the already proved common core, so the single truth table is frozen before
the mode is selected. -/
structure PaddingHardnessTransfer
    (symmetricFamily thresholdFamily : SizedFunctionFamily)
    (hard : (mode : Mode) → {n : ℕ} → BoolFunction n → Prop) where
  transfer : ∀ (mode : Mode)
    (core : CommonHardCore symmetricFamily thresholdFamily)
    (target : ℕ) (hcore : core.arity ≤ target),
    target < 3 * core.arity →
    hard mode (padCore core.function hcore)

/-- Auditable output of the local recovery layer.  It gives one executable
`E^NP` language, both scheduled per-class facts, and preserves the exact
refuter/schedule provenance used to obtain them. -/
structure RecoveredPerClassFacts
    (hard : (mode : Mode) → {n : ℕ} → BoolFunction n → Prop)
    (language : Language) (auditAt : ℕ → Prop) where
  inENP : InENP language
  eventuallyHard :
    AppendixC.EventuallyHard
      (fun candidate mode n => hard mode (candidate n)) language
  selectedCore : ℕ → ℕ
  selectionEventually : ∃ onset, ∀ n, onset ≤ n →
    selectedCore n ≤ n ∧ n < 3 * selectedCore n
  auditEventually : ∃ onset, ∀ n, onset ≤ n → auditAt n

end NearCubicWires.RecoveryPipeline
