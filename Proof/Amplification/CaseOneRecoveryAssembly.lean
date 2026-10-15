import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.Foundations.CaseOnePadding
import Proof.Foundations.CaseOneScheduleLedger
import Proof.MachineModel.ExecutableProgramRecoveryCompatibility
import Proof.Foundations.PhysicalRecovery
import Proof.Amplification.RecoveryScheduleTransfer
import Proof.Amplification.RecoveryWitnessPolicy
import Proof.Circuits.UnaryPolynomialSelector

/-!
# Direct Case-1 recovery assembly

This module closes the STV branch against the exact smooth core schedules used
by the recovery language.  Source witnesses are selected only from
`PublishedContracts`; the remaining inputs are the canonical outer-PCP branch
data and its hierarchy-YES fact.  In particular, no semantic recovery callback
or separately chosen hard function crosses this boundary.
-/

namespace NearCubicWires.CaseOneRecoveryAssembly

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOnePadding
open NearCubicWires.CaseOneScheduleLedger
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramRecoveryCompatibility
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.ExecutableProgramTightRefuterSource
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalRecovery
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UnaryPolynomialSelector

/-- The unique executable STV witness selected from the published source row. -/
noncomputable def publishedAmplifier
    (contracts : PublishedContracts) : AmplifierWitness :=
  Classical.choice (existsAmplifierWitness contracts.worstCaseAmplifier)

/-- The unique pointwise-PCPP source selected from the published joint row. -/
noncomputable def publishedPointwisePCPP
    (contracts : PublishedContracts) : UniformPointwisePCPPSource :=
  Classical.choice
    (existsUniformPointwisePCPPSource contracts.projectionPcpAndPcpp.2)

/-- The C.12 bit program viewed in the native Boolean-function address ABI
consumed by the amplifier. -/
def recoveredOuterProofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : BoolFunction (pcp.nativeWidth n) :=
  fun address =>
    recoveredTargetBit pcp input (binaryAddress address)

theorem recoveredOuterProofFunction_eq_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (canonical : CanonicalAcceptingProof pcp input) :
    recoveredOuterProofFunction pcp input =
      proofFunction pcp canonical.proof := by
  funext address
  unfold recoveredOuterProofFunction proofFunction
  exact recoveredTargetBit_eq_canonical pcp input canonical
    (binaryAddress address)

/-- Freeze all projection-PCP runtime and size exponents before selecting a
clock, timed hierarchy machine, or refuter source. -/
noncomputable def publishedProjectionPCPSource
    (contracts : PublishedContracts) :
    UniformExecutableProgramProjectionPCPSource :=
  Classical.choice <|
    existsUniformExecutableProgramProjectionPCPSource
      contracts.projectionPcpAndPcpp.1

/-- The certified tight source selected before taking either compatibility
view.  Its hierarchy language, runtime receipt, and refuter stay tied to the
same fixed executable program. -/
noncomputable def publishedTightRefuterSource
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    CertifiedTightExecutableProgramRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth) :=
  Classical.choice <|
    contracts.refuterAndXor.1
      (NearCubicWires.PolynomialClock.pairClock clockDepth)
      (NearCubicWires.PolynomialClock.pairClockAdmissible clockDepth)

/-- Program-backed intermediate view used to instantiate the corrected
projection-PCP source. -/
noncomputable def publishedProgramRefuterSource
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    ExecutableProgramRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth) :=
  (publishedTightRefuterSource contracts clockDepth).toProgramSource

/-- Freeze the genuine timed hierarchy source only after the pairing-clock
depth has been chosen, preserving the refuter contract's quantifier order. -/
noncomputable def publishedRefuterSource
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth) :=
  (publishedProgramRefuterSource contracts clockDepth).toLegacy

private noncomputable def publishedHierarchyOuterPCPBundle
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    { outer :
        HierarchyOuterPCP (publishedRefuterSource contracts clockDepth) //
      outer.runnerDegree =
          (publishedProjectionPCPSource contracts).runnerDegree ∧
        outer.queryExponent =
          (publishedProjectionPCPSource contracts).queryExponent ∧
        outer.substitutionExponent =
          (publishedProjectionPCPSource contracts).substitutionExponent } :=
  Classical.choice <|
    existsLegacyHierarchyOuterPCP
      (NearCubicWires.PolynomialClock.pairClockAdmissible clockDepth)
      (publishedProgramRefuterSource contracts clockDepth)
      (publishedProjectionPCPSource contracts)

/-- The sole outer PCP is instantiated on the hierarchy machine returned by
`publishedRefuterSource`; no unrelated machine can enter the branch split. -/
noncomputable def publishedHierarchyOuterPCP
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    HierarchyOuterPCP (publishedRefuterSource contracts clockDepth) :=
  (publishedHierarchyOuterPCPBundle contracts clockDepth).1

@[simp] theorem publishedHierarchyOuterPCP_runnerDegree
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    (publishedHierarchyOuterPCP contracts clockDepth).runnerDegree =
      (publishedProjectionPCPSource contracts).runnerDegree := by
  exact (publishedHierarchyOuterPCPBundle contracts clockDepth).2.1

@[simp] theorem publishedHierarchyOuterPCP_queryExponent
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    (publishedHierarchyOuterPCP contracts clockDepth).queryExponent =
      (publishedProjectionPCPSource contracts).queryExponent := by
  exact (publishedHierarchyOuterPCPBundle contracts clockDepth).2.2.1

@[simp] theorem publishedHierarchyOuterPCP_substitutionExponent
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent =
      (publishedProjectionPCPSource contracts).substitutionExponent := by
  exact (publishedHierarchyOuterPCPBundle contracts clockDepth).2.2.2

/-- The fixed-refuter interface attached to the same selected hierarchy
source; final recovery uses this value for eventual hierarchy truth. -/
noncomputable def publishedFixedRefuter
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    FixedRefuterWitness
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
      (NearCubicWires.PolynomialClock.pairClock clockDepth) where
  refuter := (publishedRefuterSource contracts clockDepth).refuter
  sound := (publishedRefuterSource contracts clockDepth).sound

/-- Any concrete verifier whose fixed degree fits the selected pairing clock
inherits the runtime premise required by the published refuter. -/
theorem publishedMachine_runsInPairClock
    (machine : ExecutableWeakNondeterministicMachine) (clockDepth : ℕ)
    (hdegree : machine.verifier.degree ≤ 2 ^ clockDepth)
    (hsaving : 1 ≤ machine.verifier.logPower)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10) :
    RunsInLittleO machine.toSemantic
      (NearCubicWires.PolynomialClock.pairClock clockDepth) := by
  apply NearCubicWires.PolynomialClock.executableMachine_quotient_runsInLittleO_pairClock
    machine clockDepth hdegree hsaving
  intro n
  exact (hwitness n).trans (Nat.div_le_self n 10)

/-- The selected published refuter eventually produces the exact hierarchy-YES
word rejected by a concrete one-sided machine. -/
theorem publishedRefuter_eventualConflict
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hdegree : machine.verifier.degree ≤ 2 ^ clockDepth)
    (hsaving : 1 ≤ machine.verifier.logPower)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10)
    (honeSided : EventuallyOneSided
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
      machine) :
    ∃ onset, ∀ n, onset ≤ n →
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts n
          ((publishedRefuterSource contracts clockDepth).refuter.output
            machine n) = true ∧
        ¬machine.toSemantic.accepts
          ((publishedRefuterSource contracts clockDepth).refuter.output
            machine n) := by
  rcases (publishedFixedRefuter contracts clockDepth).eventualConflict machine
      (publishedMachine_runsInPairClock machine clockDepth hdegree hsaving
        hwitness)
      hwitness honeSided with
    ⟨onset, conflict⟩
  refine ⟨onset, fun n hn => ?_⟩
  exact (conflict n hn).2

/-- A sixteenth power absorbs either verified physical-circuit simulation. -/
def simulationPower : ℕ := 16

/-- Least natural power dominating the one-exponent reserve required by the
inverse-polynomial headline adapter. -/
noncomputable def inverseAdvantagePower (advantageExponent : ℝ) : ℕ :=
  ⌈advantageExponent + 1⌉₊

/-- One additional core power is reserved for the final factor-three
target-length padding step. -/
noncomputable def inverseCoreAdvantagePower
    (advantageExponent : ℝ) : ℕ :=
  inverseAdvantagePower advantageExponent + 1

theorem inverseAdvantagePower_dominates (advantageExponent : ℝ) :
    advantageExponent + 1 ≤ (inverseAdvantagePower advantageExponent : ℝ) := by
  exact Nat.le_ceil (advantageExponent + 1)

/-- A natural-power scheduled bound implies the exact real exponent requested
by the headline, without rounding the public statement. -/
theorem inverseAdvantagePower_le
    (advantageExponent : ℝ) (arity : ℕ) (harity : 1 ≤ arity) :
    inversePolynomialAdvantage arity
        (inverseAdvantagePower advantageExponent : ℝ) ≤
      inversePolynomialAdvantage arity (advantageExponent + 1) := by
  unfold inversePolynomialAdvantage
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast harity
  · have hceil := inverseAdvantagePower_dominates advantageExponent
    linarith

/-- Exact exponent loss across the final bounded-jump padding. -/
theorem inverseScheduledPaddingAdvantage
    {target power : ℕ} (selection : BoundedJumpSelection target)
    (hlarge : 3 ^ power < selection.core) :
    inversePolynomialAdvantage selection.core ((power + 1 : ℕ) : ℝ) ≤
      inversePolynomialAdvantage target (power : ℝ) := by
  apply inversePolynomialAdvantage_le_of_pow_le
  · exact selection.core_positive
  · exact selection.core_positive.trans_le selection.coreAtMostTarget
  · exact Nat.le_of_lt (scheduledPaddingReserve selection hlarge)

theorem selectedCore_exceeds_power
    {target power : ℕ} (selection : BoundedJumpSelection target)
    (htarget : 3 * 3 ^ power ≤ target) :
    3 ^ power < selection.core := by
  have hratio := selection.target_lt_three_core
  omega

/-- Combined natural rounding and padding reserve for the public real
inverse-polynomial exponent. -/
theorem inverseCoreAdvantage_le_target
    (advantageExponent : ℝ) {target : ℕ}
    (selection : BoundedJumpSelection target)
    (hlarge : 3 ^ inverseAdvantagePower advantageExponent <
      selection.core) :
    inversePolynomialAdvantage selection.core
        (inverseCoreAdvantagePower advantageExponent : ℝ) ≤
      inversePolynomialAdvantage target (advantageExponent + 1) := by
  exact
    (inverseScheduledPaddingAdvantage selection hlarge).trans
      (inverseAdvantagePower_le advantageExponent target
        (selection.core_positive.trans_le selection.coreAtMostTarget))

/-- The inverse tier must dominate both the requested advantage power and the
fixed amplifier arity coefficient. -/
noncomputable def inverseRate
    (contracts : PublishedContracts) (advantagePower : ℕ) : ℕ :=
  max (publishedAmplifier contracts).arityCoefficient
    (2 * advantagePower + 1)

/-- The fixed tier may increase the copy rate only to absorb the fixed
amplifier arity coefficient. -/
noncomputable def fixedRate
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  max (publishedAmplifier contracts).arityCoefficient requestedRate

theorem existsFixedRateReserve
    (contracts : PublishedContracts) (fixedAdvantage : ℝ)
    (hfixedAdvantage : 0 < fixedAdvantage) :
    ∃ requestedRate : ℕ,
      0 ≤ 1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 ∧
      1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 <
        fixedAdvantage := by
  obtain ⟨requestedRate, hrequested⟩ :=
    exists_pow_lt_of_lt_one
      (by positivity : (0 : ℝ) < 4 * fixedAdvantage)
      (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨requestedRate, by positivity, ?_⟩
  have hrate :
      requestedRate ≤ fixedRate contracts requestedRate :=
    le_max_right _ _
  have hdenominatorNat :
      2 ^ requestedRate ≤ 2 ^ (fixedRate contracts requestedRate) :=
    Nat.pow_le_pow_right (by omega) hrate
  have hdenominator :
      (2 : ℝ) ^ requestedRate ≤
        (2 : ℝ) ^ (fixedRate contracts requestedRate) := by
    exact_mod_cast hdenominatorNat
  have hsmaller :
      1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) ≤
        1 / (2 : ℝ) ^ requestedRate :=
    one_div_le_one_div_of_le (by positivity) hdenominator
  rw [one_div_pow] at hrequested
  nlinarith

/-- Canonical fixed-tier copy rate selected from the exact dyadic reserve. -/
noncomputable def fixedRequestedRate
    (contracts : PublishedContracts) (fixedAdvantage : ℝ)
    (hfixedAdvantage : 0 < fixedAdvantage) : ℕ :=
  Classical.choose
    (existsFixedRateReserve contracts fixedAdvantage hfixedAdvantage)

theorem fixedRequestedRate_spec
    (contracts : PublishedContracts) (fixedAdvantage : ℝ)
    (hfixedAdvantage : 0 < fixedAdvantage) :
    0 ≤
        1 / (2 : ℝ) ^
          (fixedRate contracts
            (fixedRequestedRate contracts fixedAdvantage hfixedAdvantage)) /
          4 ∧
      1 / (2 : ℝ) ^
          (fixedRate contracts
            (fixedRequestedRate contracts fixedAdvantage hfixedAdvantage)) /
          4 <
        fixedAdvantage :=
  Classical.choose_spec
    (existsFixedRateReserve contracts fixedAdvantage hfixedAdvantage)

/-- One degree pays both inverse-tier STV obligations: physical simulation and
the requested inverse-polynomial advantage. -/
noncomputable def inverseRequiredDegree
    (contracts : PublishedContracts) (advantagePower : ℕ) : ℕ :=
  (2 * max simulationPower advantagePower + 1) *
    (publishedAmplifier contracts).stvExponent

/-- One degree pays the fixed-tier physical simulation and its dyadic
advantage reserve. -/
noncomputable def fixedRequiredDegree
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  (max simulationPower (fixedRate contracts requestedRate + 2) + 1) *
    (publishedAmplifier contracts).stvExponent

/-- Padding a raw scheduled core to its linear envelope costs exactly the cube
of the corresponding integer factor in the wire coefficient. -/
noncomputable def scheduledCoefficient (factor : ℕ) : ℝ :=
  1 / (factor : ℝ) ^ 3

theorem scheduledCoefficient_positive {factor : ℕ} (hfactor : 0 < factor) :
    0 < scheduledCoefficient factor := by
  unfold scheduledCoefficient
  positivity

theorem scheduledCoefficient_le_one {factor : ℕ} (hfactor : 0 < factor) :
    scheduledCoefficient factor ≤ 1 := by
  unfold scheduledCoefficient
  have hfactorOne : (1 : ℝ) ≤ factor := by exact_mod_cast hfactor
  have hdenominator : (1 : ℝ) ≤ (factor : ℝ) ^ 3 :=
    one_le_pow₀ hfactorOne
  simpa using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenominator)

theorem wireScale_floor_le_cube
    {coefficient : ℝ} (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficientOne : coefficient ≤ 1)
    (logExponent arity : ℕ) :
    ⌊wireScale coefficient logExponent arity⌋₊ ≤ arity ^ 3 := by
  apply Nat.floor_le_of_le
  have hlogOne : (1 : ℝ) ≤ logScale arity := by
    exact_mod_cast (NearCubicWires.logScale_pos arity)
  have hdenominator :
      (1 : ℝ) ≤ (logScale arity : ℝ) ^ logExponent :=
    one_le_pow₀ hlogOne
  have hnPower : 0 ≤ (arity : ℝ) ^ 3 := by positivity
  calc
    wireScale coefficient logExponent arity =
        coefficient * (arity : ℝ) ^ 3 /
          (logScale arity : ℝ) ^ logExponent := rfl
    _ ≤ coefficient * (arity : ℝ) ^ 3 :=
      div_le_self (mul_nonneg hcoefficientNonnegative hnPower)
        hdenominator
    _ ≤ (arity : ℝ) ^ 3 :=
      mul_le_of_le_one_left hnPower hcoefficientOne
    _ = (arity ^ 3 : ℕ) := by norm_cast

/-- Uniform arithmetic ledger for the two DAG simulations.  The multiplier 50
dominates both concrete simulations, and arity six absorbs the constant. -/
theorem simulationCost_le_power
    (multiplier logExponent arity : ℕ)
    (hmultiplier : multiplier ≤ 50) (harity : 6 ≤ arity)
    {coefficient : ℝ} (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficientOne : coefficient ≤ 1) :
    multiplier *
        (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
      arity ^ simulationPower := by
  have hfloor :=
    wireScale_floor_le_cube hcoefficientNonnegative hcoefficientOne
      logExponent arity
  have hinside :
      arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2 ≤
        2 * arity ^ 3 := by
    have hcubic : arity + 2 ≤ arity ^ 3 := by
      calc
        arity + 2 ≤ arity + arity := by omega
        _ = arity * 2 := by ring
        _ ≤ arity * arity :=
          Nat.mul_le_mul_left arity (by omega)
        _ = arity ^ 2 := by ring
        _ ≤ arity ^ 2 * arity :=
          Nat.le_mul_of_pos_right _ (by omega)
        _ = arity ^ 3 := by ring
    omega
  have hpower :
      (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
        (2 * arity ^ 3) ^ 4 :=
    Nat.pow_le_pow_left hinside 4
  have hconstant : 800 ≤ arity ^ 4 := by
    have hsix : 6 ^ 4 ≤ arity ^ 4 :=
      Nat.pow_le_pow_left harity 4
    norm_num at hsix ⊢
    omega
  calc
    multiplier *
          (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
        50 *
          (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 :=
      Nat.mul_le_mul hmultiplier le_rfl
    _ ≤ 50 * (2 * arity ^ 3) ^ 4 :=
      Nat.mul_le_mul_left 50 hpower
    _ = 800 * arity ^ 12 := by ring
    _ ≤ arity ^ 4 * arity ^ 12 :=
      Nat.mul_le_mul_right (arity ^ 12) hconstant
    _ = arity ^ simulationPower := by
      simp [simulationPower, ← pow_add]

/-- Exact inverse-tier smooth envelope.  Its rate and source degree are fixed
by the published amplifier and the requested advantage power. -/
noncomputable def inverseEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :=
  inverseCoreEnvelope outer (publishedPointwisePCPP contracts)
    (inverseRequiredDegree contracts advantagePower)
    (inverseRate contracts advantagePower)

/-- Exact fixed-tier smooth envelope. -/
noncomputable def fixedEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :=
  fixedCoreEnvelope outer (publishedPointwisePCPP contracts)
    (fixedRequiredDegree contracts requestedRate)
    (fixedRate contracts requestedRate)

/-- The sole executable selectors for the two closed envelopes. -/
noncomputable def inverseSchedule
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    ExecutableEnvelopeSchedule
      (inverseEnvelope contracts outer advantagePower) :=
  executableEnvelopeSchedule (inverseEnvelope contracts outer advantagePower)

noncomputable def fixedSchedule
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    ExecutableEnvelopeSchedule
      (fixedEnvelope contracts outer requestedRate) :=
  executableEnvelopeSchedule (fixedEnvelope contracts outer requestedRate)

/-- Canonical source indices decoded from the two executable selectors. -/
noncomputable def inverseSelectedSource
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ) : ℕ :=
  ((inverseSchedule contracts outer advantagePower).output target).source

noncomputable def fixedSelectedSource
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ) : ℕ :=
  ((fixedSchedule contracts outer requestedRate).output target).source

/-- The exact refuter word at the inverse branch's source length. -/
noncomputable def inverseRefuterInput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) :
    BitInput (sourceLength (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))) :=
  source.refuter.output machine <|
    sourceLength (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))

/-- Fixed-schedule refuter word. -/
noncomputable def fixedRefuterInput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) :
    BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target)) :=
  source.refuter.output machine <|
    sourceLength (fixedSelectedSource contracts outer requestedRate target)

/-- The genuine outer-oracle split at the inverse target's decoded source.
Case-1 data and the canonical Case-2 oracle are created only by this decision. -/
noncomputable def inverseTargetBranch
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target)) :
    ScheduledOuterBranch outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target) :=
  scheduledOuterBranch outer (publishedAmplifier contracts)
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
    (inverseRefuterInput contracts outer machine advantageExponent target)
    hyes

/-- Fixed-tier instance of the same canonical branch decision. -/
noncomputable def fixedTargetBranch
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target)) :
    ScheduledOuterBranch outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target) :=
  scheduledOuterBranch outer (publishedAmplifier contracts)
    (fixedRequiredDegree contracts requestedRate)
    (fixedSelectedSource contracts outer requestedRate target)
    (fixedRefuterInput contracts outer machine requestedRate target) hyes

/-- Case 1 amplifies exactly the proof table recovered by C.12's zero-first
SAT self-reduction.  This rules out a semantic accepting-proof choice beside
the executable recovery language. -/
theorem ScheduledCaseOneData.seed_eq_recoveredOuterProofFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input) :
    (data.amplifierInput hyes).seed =
      recoveredOuterProofFunction (paddedOuterPCP outer) input := by
  let canonical :=
    Classical.choice <|
      existsCanonicalAcceptingProof (paddedOuterPCP outer) input
        (paddedOuterPCP_complete outer input hyes)
  change
    proofFunction (paddedOuterPCP outer) canonical.proof =
      recoveredOuterProofFunction (paddedOuterPCP outer) input
  exact
    (recoveredOuterProofFunction_eq_canonical
      (paddedOuterPCP outer) input canonical).symm

/-- Consequently the Boolean hard core is the published amplifier applied to
that recovered table, not merely an extensionally unrelated hard function. -/
theorem ScheduledCaseOneData.hardCore_arity_eq_recoveredAmplification
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).arity =
      (amplifier.algorithm.amplify
        (scheduledWidth outer sourceIndex)
        (recoveredOuterProofFunction (paddedOuterPCP outer) input)).outputArity := by
  unfold hardCoreFromCaseOne
  dsimp only
  rw [
    NearCubicWires.CaseOneRecoveryAssembly.ScheduledCaseOneData.seed_eq_recoveredOuterProofFunction
      data hyes]
  rfl

theorem ScheduledCaseOneData.hardCore_function_eq_recoveredAmplification
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input) :
    HEq (hardCoreFromCaseOne (data.amplifierInput hyes)).function
      (amplifier.algorithm.amplify
        (scheduledWidth outer sourceIndex)
        (recoveredOuterProofFunction (paddedOuterPCP outer) input)).function := by
  unfold hardCoreFromCaseOne
  dsimp only
  rw [
    NearCubicWires.CaseOneRecoveryAssembly.ScheduledCaseOneData.seed_eq_recoveredOuterProofFunction
      data hyes]
  rfl

/-- Bundled dependent equality used by the executable linker: both output
arity and evaluator agree in one rewrite-safe term. -/
theorem ScheduledCaseOneData.hardCore_eq_recoveredAmplification
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input) :
    (⟨(hardCoreFromCaseOne (data.amplifierInput hyes)).arity,
        (hardCoreFromCaseOne (data.amplifierInput hyes)).function⟩ :
        Σ arity, BoolFunction arity) =
      ⟨(amplifier.algorithm.amplify
          (scheduledWidth outer sourceIndex)
          (recoveredOuterProofFunction
            (paddedOuterPCP outer) input)).outputArity,
        (amplifier.algorithm.amplify
          (scheduledWidth outer sourceIndex)
          (recoveredOuterProofFunction
            (paddedOuterPCP outer) input)).function⟩ := by
  apply Sigma.ext_iff.mpr
  exact
    ⟨ScheduledCaseOneData.hardCore_arity_eq_recoveredAmplification
      data hyes,
    ScheduledCaseOneData.hardCore_function_eq_recoveredAmplification
      data hyes⟩

theorem padCore_eq_of_dependent_function_eq
    {leftArity rightArity target : ℕ}
    {left : BoolFunction leftArity} {right : BoolFunction rightArity}
    (hequal :
      (⟨leftArity, left⟩ : Σ arity, BoolFunction arity) =
        ⟨rightArity, right⟩)
    (hleft : leftArity ≤ target) (hright : rightArity ≤ target) :
    padCore left hleft = padCore right hright := by
  cases hequal
  rfl

/-- The old padding-only inverse coefficient, retained as the intermediate
wire-scale transfer target. -/
noncomputable def inversePaddingPhysicalCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℝ :=
  scheduledCoefficient <|
    inverseCorePaddingFactor outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower)

/-- The XOR witness selected at the low Case-1 import boundary.  This is
definitionally the same choice as `CaseTwoRecoveryAssembly.publishedXorWitness`,
but placing the choice here lets the fixed physical schedule account for all
frozen estimator constants without importing the Case-2 assembly back into
its own dependency. -/
noncomputable def fixedPhysicalXorWitness
    (contracts : PublishedContracts) : XorAmplificationWitness :=
  Classical.choice <|
    existsXorAmplificationWitness contracts.refuterAndXor.2

/-- The exact-decomposition runner selected at the low Case-1 import boundary.
This is definitionally the same choice as the normalized estimator's selected
algorithm.  Keeping the duplicate here lets the physical schedule absorb its
frozen child-count constants without importing the estimator implementation
back into the recovery assembly. -/
noncomputable def fixedPhysicalExactDecompositionAlgorithm
    (contracts : PublishedContracts) : ExecutableExactDecompositionAlgorithm :=
  Classical.choice contracts.disjointExactDecomposition

/-- Natural coefficient-mass cap of the fixed XOR policy.  Both the repaired
radius and the fixed copy count are frozen before the public input length. -/
noncomputable def fixedPhysicalFrozenMassNat
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  ⌈(fixedPhysicalXorWitness contracts).massCoefficient
      (repairedDelta (publishedPointwisePCPP contracts))⌉₊ *
    4 ^ fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate)

/-- Low-import duplicate of the larger of the aggregate-clause and penalty
coefficient masses.  The literal formulas keep the schedule layer independent
of the downstream polynomial-mass modules. -/
noncomputable def fixedPhysicalEstimatorMassCap
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℚ :=
  let mass : ℚ := fixedPhysicalFrozenMassNat contracts requestedRate
  max ((2 + mass) ^ 2 + 2 * (2 + mass))
    (2 * ((2 + mass) ^ 2 + 2 * (2 + mass) ^ 3 + (2 + mass) ^ 4))

/-- Ceiling used by the fixed symmetric estimator's constant odd walk. -/
noncomputable def fixedPhysicalEstimatorWalkCeiling
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  ⌈(4 * (fixedPhysicalEstimatorMassCap contracts requestedRate : ℝ)) /
      ((executableParametersOfSource
        (publishedPointwisePCPP contracts)).estimationError : ℝ)⌉₊

/-- The q-independent odd walk length whose failure pays the entire frozen
fixed coefficient mass. -/
noncomputable def fixedPhysicalEstimatorWalkLength
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  2 * (fixedPhysicalEstimatorWalkCeiling contracts requestedRate + 1) + 1

theorem fixedPhysicalEstimatorWalkLength_odd
    (contracts : PublishedContracts) (requestedRate : ℕ) :
    Odd (fixedPhysicalEstimatorWalkLength contracts requestedRate) := by
  exact ⟨fixedPhysicalEstimatorWalkCeiling contracts requestedRate + 1, rfl⟩

/-- Cycle-free copy of the terminal fixed arm's live scale.  At the selected
outer source this unfolds to `selectedBodyLiveScale contracts`; only upstream
certificate and outer-PCP data occur here. -/
noncomputable def fixedPhysicalCapacityLiveScale
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source) : ℕ :=
  (NearCubicWires.WilliamsPublishedForm.selectedLocalCertificate
      contracts.booleanRectangularProduct).streamed.logExponent +
    outer.proofExponent + 18

/-- Frozen conservative cost of the selected exact-child runner.  Keeping the
runner coefficient in its raw natural form makes the later child-cap proof a
direct monotonicity argument; the extra fixed factor absorbs the elementary
scheduled-measure and tag bookkeeping. -/
noncomputable def fixedPhysicalSymmetricChildCoefficient
    (contracts : PublishedContracts) : ℕ :=
  ((fixedPhysicalExactDecompositionAlgorithm contracts).runner.coefficient + 1) *
    ((fixedPhysicalExactDecompositionAlgorithm contracts).runner.degree + 1)

/-! ### Frozen binary width of the actual scheduled factor geometry -/

/-- Clause-population polynomial in the actual scheduled point coordinate.
Unlike the older source-log envelope, this uses `q` itself as the circuit-width
upper bound, so its binary width is linear in `logScale q` with a frozen
contracts-dependent coefficient. -/
noncomputable def fixedPhysicalScheduledClauseCountEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate q : ℕ) : ℕ :=
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let substituted := outer.substitution.sizeCoefficient *
      (q + oracleSizeBound requiredDegree q + 1) ^
        outer.substitutionExponent + q
  (publishedPointwisePCPP contracts).coefficient *
    (substituted + 2 * q + 3) ^
      (publishedPointwisePCPP contracts).degree

/-- One literal restricted symmetric factor, with every checked-policy field
replaced by its cycle-free polynomial upper bound in the scheduled point
coordinate.  The wire bound deliberately uses the pre-denominator core cube;
therefore this definition does not depend on the physical schedule factor it
will later help choose. -/
noncomputable def fixedPhysicalScheduledFactorDescriptionEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate q : ℕ) : ℕ :=
  let pcpp := publishedPointwisePCPP contracts
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let core := fixedCaseOneWidthFactor outer pcpp requiredDegree rate * q
  let wire := core ^ 3
  let arity := seedArityLinearCoefficient outer pcpp requiredDegree * q
  let description := symmetricDescriptionCap arity wire
  let clauses :=
    fixedPhysicalScheduledClauseCountEnvelope contracts outer requestedRate q
  max 4 <| (wire + 1) *
    ((q + 1) * (q + clauses + description + 4) + q + 1)

/-- Complete scalar whose binary width is consumed by the constant-walk
exact-row support theorem: point coordinate, two degree-two factors, and its
fixed framing slack. -/
noncomputable def fixedPhysicalScheduledParameterEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate q : ℕ) : ℕ :=
  q + 2 *
    fixedPhysicalScheduledFactorDescriptionEnvelope contracts outer
      requestedRate q + 5

theorem fixedPhysicalScheduledParameterEnvelope_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    PolynomiallyBounded
      (fixedPhysicalScheduledParameterEnvelope contracts outer
        requestedRate) := by
  let pcpp := publishedPointwisePCPP contracts
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let hq : PolynomiallyBounded (fun q : ℕ => q) := polynomiallyBounded_id
  let hcore : PolynomiallyBounded (fun q : ℕ =>
      fixedCaseOneWidthFactor outer pcpp requiredDegree rate * q) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_constant
        (fixedCaseOneWidthFactor outer pcpp requiredDegree rate)) hq
  let hwire : PolynomiallyBounded (fun q : ℕ =>
      (fixedCaseOneWidthFactor outer pcpp requiredDegree rate * q) ^ 3) :=
    polynomiallyBounded_pow hcore 3
  let harity : PolynomiallyBounded (fun q : ℕ =>
      seedArityLinearCoefficient outer pcpp requiredDegree * q) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_constant
        (seedArityLinearCoefficient outer pcpp requiredDegree)) hq
  let hone := polynomiallyBounded_constant 1
  let hnormalized : PolynomiallyBounded (fun q : ℕ =>
      normalizedGateDescriptionCap
        (seedArityLinearCoefficient outer pcpp requiredDegree * q)) := by
    unfold normalizedGateDescriptionCap
    exact polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_add harity hone)
        (polynomiallyBounded_add
          (polynomiallyBounded_mul harity harity) hone)) harity
  let hdescription : PolynomiallyBounded (fun q : ℕ =>
      symmetricDescriptionCap
        (seedArityLinearCoefficient outer pcpp requiredDegree * q)
        ((fixedCaseOneWidthFactor outer pcpp requiredDegree rate * q) ^ 3)) := by
    unfold symmetricDescriptionCap
    exact polynomiallyBounded_mul (polynomiallyBounded_add hwire hone)
      (polynomiallyBounded_add hnormalized hone)
  let horacle : PolynomiallyBounded (fun q : ℕ =>
      oracleSizeBound requiredDegree q) :=
    oracleSizeBound_polynomiallyBounded requiredDegree
  let hsubstituted : PolynomiallyBounded (fun q : ℕ =>
      outer.substitution.sizeCoefficient *
          (q + oracleSizeBound requiredDegree q + 1) ^
            outer.substitutionExponent + q) :=
    polynomiallyBounded_add
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant outer.substitution.sizeCoefficient)
        (polynomiallyBounded_pow
          (polynomiallyBounded_add
            (polynomiallyBounded_add hq horacle) hone)
          outer.substitutionExponent)) hq
  let hclauses : PolynomiallyBounded
      (fixedPhysicalScheduledClauseCountEnvelope contracts outer
        requestedRate) := by
    unfold fixedPhysicalScheduledClauseCountEnvelope
    dsimp only
    exact polynomiallyBounded_mul
      (polynomiallyBounded_constant pcpp.coefficient)
      (polynomiallyBounded_pow
        (polynomiallyBounded_add
          (polynomiallyBounded_add hsubstituted
            (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hq))
          (polynomiallyBounded_constant 3)) pcpp.degree)
  let hrestricted : PolynomiallyBounded (fun q : ℕ =>
      (q + 1) *
          (q + fixedPhysicalScheduledClauseCountEnvelope contracts outer
              requestedRate q +
            symmetricDescriptionCap
              (seedArityLinearCoefficient outer pcpp requiredDegree * q)
              ((fixedCaseOneWidthFactor outer pcpp requiredDegree rate * q) ^
                3) + 4) +
        q + 1) :=
    polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_add hq hone)
          (polynomiallyBounded_add
            (polynomiallyBounded_add
              (polynomiallyBounded_add hq hclauses) hdescription)
            (polynomiallyBounded_constant 4))) hq) hone
  let hfactor : PolynomiallyBounded
      (fixedPhysicalScheduledFactorDescriptionEnvelope contracts outer
        requestedRate) := by
    unfold fixedPhysicalScheduledFactorDescriptionEnvelope
    dsimp only
    exact polynomiallyBounded_max (polynomiallyBounded_constant 4)
      (polynomiallyBounded_mul (polynomiallyBounded_add hwire hone)
        hrestricted)
  unfold fixedPhysicalScheduledParameterEnvelope
  exact polynomiallyBounded_add
    (polynomiallyBounded_add hq
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hfactor))
    (polynomiallyBounded_constant 5)

private theorem fixedPhysical_natBitLength_mul_le (left right : ℕ) :
    natBitLength (left * right) ≤ natBitLength left + natBitLength right := by
  have hleftOne : 1 ≤ natBitLength left := by
    unfold natBitLength
    omega
  have hrightOne : 1 ≤ natBitLength right := by
    unfold natBitLength
    omega
  rcases Nat.eq_zero_or_pos (left * right) with hzero | hpositive
  · rw [hzero]
    have : natBitLength 0 = 1 := by simp [natBitLength]
    omega
  · have hleftLt : left < 2 ^ natBitLength left := by
      have hself := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) left
      simpa [natBitLength] using hself
    have hrightLt : right < 2 ^ natBitLength right := by
      have hself := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) right
      simpa [natBitLength] using hself
    have hproduct :
        left * right < 2 ^ (natBitLength left + natBitLength right) := by
      calc
        left * right < 2 ^ natBitLength left * 2 ^ natBitLength right :=
          mul_lt_mul'' hleftLt hrightLt (Nat.zero_le _) (Nat.zero_le _)
        _ = 2 ^ (natBitLength left + natBitLength right) :=
          (pow_add 2 _ _).symm
    have hlog := Nat.log_lt_of_lt_pow (b := 2) hpositive.ne' hproduct
    unfold natBitLength at hlog ⊢
    omega

private theorem fixedPhysical_natBitLength_mono
    {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem fixedPhysical_natBitLength_pow_le (base exponent : ℕ) :
    natBitLength (base ^ exponent) ≤ exponent * natBitLength base + 1 := by
  induction exponent with
  | zero => simp [natBitLength]
  | succ count inductionHypothesis =>
      have hstep := fixedPhysical_natBitLength_mul_le (base ^ count) base
      rw [pow_succ]
      have hexpand :
          (count + 1) * natBitLength base =
            count * natBitLength base + natBitLength base := by ring
      omega

private theorem fixedPhysical_natBitLength_succ_le_logScale (q : ℕ) :
    natBitLength (q + 1) ≤ logScale q := by
  have hpow : q + 1 < 2 ^ logScale q := by
    apply lt_of_lt_of_le (show q + 1 < q + 2 by omega)
    unfold logScale
    exact Nat.le_pow_clog (by omega) (q + 2)
  have hlog := Nat.log_lt_of_lt_pow (b := 2) (by omega) hpow
  unfold natBitLength
  omega

/-- Frozen coefficient for the binary width of the complete scheduled
symmetric-factor description.  It is chosen from the explicit cycle-free
polynomial above, rather than from an unsound uniform numeral.  The choice
depends only on the eight contracts, the selected outer source and the
requested fixed rate, never on the public input length. -/
noncomputable def fixedPhysicalScheduledDescriptionBitCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  let envelope := Classical.choice <|
    polynomiallyBounded_iff_nonemptyEnvelope.mp
      (fixedPhysicalScheduledParameterEnvelope_polynomiallyBounded contracts
        outer requestedRate)
  max 4096 (natBitLength envelope.coefficient + envelope.degree + 2)

theorem fixedPhysicalScheduledDescriptionBitCoefficient_ge
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    4096 ≤ fixedPhysicalScheduledDescriptionBitCoefficient contracts outer
      requestedRate := by
  unfold fixedPhysicalScheduledDescriptionBitCoefficient
  dsimp only
  exact Nat.le_max_left _ _

/-- Public logarithmic-width certificate used by the fixed constant-walk row
specialization. -/
theorem fixedPhysicalScheduledParameterEnvelope_bitLength_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate q : ℕ) :
    natBitLength
          (fixedPhysicalScheduledParameterEnvelope contracts outer
            requestedRate q) + 1 ≤
      fixedPhysicalScheduledDescriptionBitCoefficient contracts outer
          requestedRate *
        (logScale q + 1) := by
  let envelope := Classical.choice <|
    polynomiallyBounded_iff_nonemptyEnvelope.mp
      (fixedPhysicalScheduledParameterEnvelope_polynomiallyBounded contracts
        outer requestedRate)
  have hmono := fixedPhysical_natBitLength_mono (envelope.bound q)
  have hmul := fixedPhysical_natBitLength_mul_le envelope.coefficient
    ((q + 1) ^ envelope.degree)
  have hpow := fixedPhysical_natBitLength_pow_le (q + 1) envelope.degree
  have hbase := fixedPhysical_natBitLength_succ_le_logScale q
  unfold fixedPhysicalScheduledDescriptionBitCoefficient
  dsimp only
  calc
    natBitLength
          (fixedPhysicalScheduledParameterEnvelope contracts outer
            requestedRate q) + 1 ≤
        natBitLength envelope.coefficient +
          envelope.degree * natBitLength (q + 1) + 2 := by omega
    _ ≤ (natBitLength envelope.coefficient + envelope.degree + 2) *
          (logScale q + 1) := by
      have hlog : 0 < logScale q := logScale_pos q
      nlinarith
    _ ≤ max 4096
          (natBitLength envelope.coefficient + envelope.degree + 2) *
          (logScale q + 1) := by
      exact Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

/-! ### Cycle-free inverse compact-row constants -/

/-- Explicit source-index wire-cap coefficient.  The inverse fibre ceiling is
quadratic in `sourceIndex + 1`; cubing the linear smooth core therefore has
degree six. -/
noncomputable def inversePhysicalWirePolynomialCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  let coreCoefficient := inverseTightCoreCoefficient outer
    (publishedPointwisePCPP contracts)
    (inverseRequiredDegree contracts advantagePower)
    (inverseRate contracts advantagePower)
  coreCoefficient ^ 3 * 729 + 1

/-- The exact explicit degree used by the inverse numeric cap. -/
def inversePhysicalWirePolynomialDegree : ℕ := 6

/-- Appendix C.3's inverse-copy coefficient at the low physical boundary. -/
noncomputable def inversePhysicalCopyCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  inverseCopiesLinearCoefficient outer (publishedPointwisePCPP contracts)
    (inverseRate contracts advantagePower)

noncomputable def inversePhysicalAccuracyExponent
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  let rawMassExponent := 2 *
    inversePhysicalCopyCoefficient contracts outer advantagePower + 1
  let wireExponent := inversePhysicalWirePolynomialDegree + 1
  4 * (4 * (wireExponent + rawMassExponent) + 7) + 10

/-- Actual scheduled clause envelope in the inverse point coordinate. -/
noncomputable def inversePhysicalScheduledClauseCountEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower q : ℕ) : ℕ :=
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let substituted := outer.substitution.sizeCoefficient *
      (q + oracleSizeBound requiredDegree q + 1) ^
        outer.substitutionExponent + q
  (publishedPointwisePCPP contracts).coefficient *
    (substituted + 2 * q + 3) ^
      (publishedPointwisePCPP contracts).degree

/-- One inverse scheduled factor after replacing checked fields by their
cycle-free point-coordinate bounds. -/
noncomputable def inversePhysicalScheduledFactorDescriptionEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower q : ℕ) : ℕ :=
  let pcpp := publishedPointwisePCPP contracts
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let wire := q ^ 3
  let arity := seedArityLinearCoefficient outer pcpp requiredDegree * q
  let description := symmetricDescriptionCap arity wire
  let clauses := inversePhysicalScheduledClauseCountEnvelope contracts outer
    advantagePower q
  max 4 <| (wire + 1) *
    ((q + 1) * (q + clauses + description + 4) + q + 1)

noncomputable def inversePhysicalScheduledParameterEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower q : ℕ) : ℕ :=
  q + 2 * inversePhysicalScheduledFactorDescriptionEnvelope contracts outer
    advantagePower q + 5

theorem inversePhysicalScheduledParameterEnvelope_polynomiallyBounded
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    PolynomiallyBounded
      (inversePhysicalScheduledParameterEnvelope contracts outer
        advantagePower) := by
  let pcpp := publishedPointwisePCPP contracts
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let hq : PolynomiallyBounded (fun q : ℕ => q) := polynomiallyBounded_id
  let hone := polynomiallyBounded_constant 1
  let hwire : PolynomiallyBounded (fun q : ℕ => q ^ 3) :=
    polynomiallyBounded_pow hq 3
  let harity : PolynomiallyBounded (fun q : ℕ =>
      seedArityLinearCoefficient outer pcpp requiredDegree * q) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_constant
        (seedArityLinearCoefficient outer pcpp requiredDegree)) hq
  let hnormalized : PolynomiallyBounded (fun q : ℕ =>
      normalizedGateDescriptionCap
        (seedArityLinearCoefficient outer pcpp requiredDegree * q)) := by
    unfold normalizedGateDescriptionCap
    exact polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_add harity hone)
        (polynomiallyBounded_add
          (polynomiallyBounded_mul harity harity) hone)) harity
  let hdescription : PolynomiallyBounded (fun q : ℕ =>
      symmetricDescriptionCap
        (seedArityLinearCoefficient outer pcpp requiredDegree * q)
        (q ^ 3)) := by
    unfold symmetricDescriptionCap
    exact polynomiallyBounded_mul (polynomiallyBounded_add hwire hone)
      (polynomiallyBounded_add hnormalized hone)
  let horacle : PolynomiallyBounded (fun q : ℕ =>
      oracleSizeBound requiredDegree q) :=
    oracleSizeBound_polynomiallyBounded requiredDegree
  let hsubstituted : PolynomiallyBounded (fun q : ℕ =>
      outer.substitution.sizeCoefficient *
          (q + oracleSizeBound requiredDegree q + 1) ^
            outer.substitutionExponent + q) :=
    polynomiallyBounded_add
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant outer.substitution.sizeCoefficient)
        (polynomiallyBounded_pow
          (polynomiallyBounded_add
            (polynomiallyBounded_add hq horacle) hone)
          outer.substitutionExponent)) hq
  let hclauses : PolynomiallyBounded
      (inversePhysicalScheduledClauseCountEnvelope contracts outer
        advantagePower) := by
    unfold inversePhysicalScheduledClauseCountEnvelope
    dsimp only
    exact polynomiallyBounded_mul
      (polynomiallyBounded_constant pcpp.coefficient)
      (polynomiallyBounded_pow
        (polynomiallyBounded_add
          (polynomiallyBounded_add hsubstituted
            (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hq))
          (polynomiallyBounded_constant 3)) pcpp.degree)
  let hrestricted : PolynomiallyBounded (fun q : ℕ =>
      (q + 1) *
          (q + inversePhysicalScheduledClauseCountEnvelope contracts outer
              advantagePower q +
            symmetricDescriptionCap
              (seedArityLinearCoefficient outer pcpp requiredDegree * q)
              (q ^ 3) + 4) +
        q + 1) :=
    polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_add hq hone)
          (polynomiallyBounded_add
            (polynomiallyBounded_add
              (polynomiallyBounded_add hq hclauses) hdescription)
            (polynomiallyBounded_constant 4))) hq) hone
  let hfactor : PolynomiallyBounded
      (inversePhysicalScheduledFactorDescriptionEnvelope contracts outer
        advantagePower) := by
    unfold inversePhysicalScheduledFactorDescriptionEnvelope
    dsimp only
    exact polynomiallyBounded_max (polynomiallyBounded_constant 4)
      (polynomiallyBounded_mul (polynomiallyBounded_add hwire hone)
        hrestricted)
  unfold inversePhysicalScheduledParameterEnvelope
  exact polynomiallyBounded_add
    (polynomiallyBounded_add hq
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hfactor))
    (polynomiallyBounded_constant 5)

noncomputable def inversePhysicalScheduledDescriptionBitCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  let envelope := Classical.choice <|
    polynomiallyBounded_iff_nonemptyEnvelope.mp
      (inversePhysicalScheduledParameterEnvelope_polynomiallyBounded contracts
        outer advantagePower)
  max 4096 (natBitLength envelope.coefficient + envelope.degree + 2)

theorem inversePhysicalScheduledDescriptionBitCoefficient_ge
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    4096 ≤ inversePhysicalScheduledDescriptionBitCoefficient contracts outer
      advantagePower := by
  unfold inversePhysicalScheduledDescriptionBitCoefficient
  dsimp only
  exact Nat.le_max_left _ _

/-- Public logarithmic-width certificate for the exact inverse scheduled
parameter envelope.  This is kept at the physical boundary so the compact
row and its schedule coefficient use the same chosen polynomial envelope. -/
theorem inversePhysicalScheduledParameterEnvelope_bitLength_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower q : ℕ) :
    natBitLength
          (inversePhysicalScheduledParameterEnvelope contracts outer
            advantagePower q) + 1 ≤
      inversePhysicalScheduledDescriptionBitCoefficient contracts outer
          advantagePower * (logScale q + 1) := by
  let envelope := Classical.choice <|
    polynomiallyBounded_iff_nonemptyEnvelope.mp
      (inversePhysicalScheduledParameterEnvelope_polynomiallyBounded contracts
        outer advantagePower)
  have hmono := fixedPhysical_natBitLength_mono (envelope.bound q)
  have hmul := fixedPhysical_natBitLength_mul_le envelope.coefficient
    ((q + 1) ^ envelope.degree)
  have hpow := fixedPhysical_natBitLength_pow_le (q + 1) envelope.degree
  have hbase := fixedPhysical_natBitLength_succ_le_logScale q
  unfold inversePhysicalScheduledDescriptionBitCoefficient
  dsimp only
  calc
    natBitLength
          (inversePhysicalScheduledParameterEnvelope contracts outer
            advantagePower q) + 1 ≤
        natBitLength envelope.coefficient +
          envelope.degree * natBitLength (q + 1) + 2 := by omega
    _ ≤ (natBitLength envelope.coefficient + envelope.degree + 2) *
          (logScale q + 1) := by
      have hlog : 0 < logScale q := logScale_pos q
      nlinarith
    _ ≤ max 4096
          (natBitLength envelope.coefficient + envelope.degree + 2) *
          (logScale q + 1) := by
      exact Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

/-- Structural arithmetic constant in the fixed symmetric row ledger.  Naming
it at the schedule boundary keeps all later support consumers aligned with the
physical coefficient without restating a magic numeral. -/
def fixedPhysicalSymmetricStructuralBaseCoefficient : ℕ := 64145

theorem fixedPhysicalSymmetricStructuralBaseCoefficient_positive :
    0 < fixedPhysicalSymmetricStructuralBaseCoefficient := by
  norm_num [fixedPhysicalSymmetricStructuralBaseCoefficient]

/-- Contracts-dependent fixed-row coefficient used by both the exact-child
support ledger and the physical capacity burden.  It is frozen before the
public input length, so replacing the old structural-only numeral changes no
headline exponent. -/
noncomputable def fixedPhysicalSymmetricRowCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  fixedPhysicalSymmetricStructuralBaseCoefficient *
    fixedPhysicalSymmetricChildCoefficient contracts *
    fixedPhysicalScheduledDescriptionBitCoefficient contracts outer
      requestedRate

theorem fixedPhysicalSymmetricRowCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    0 < fixedPhysicalSymmetricRowCoefficient contracts outer requestedRate := by
  unfold fixedPhysicalSymmetricRowCoefficient
    fixedPhysicalSymmetricChildCoefficient
  exact Nat.mul_pos
    (Nat.mul_pos fixedPhysicalSymmetricStructuralBaseCoefficient_positive
      (Nat.mul_pos (by omega) (by omega)))
    ((show 0 < 4096 by norm_num).trans_le
      (fixedPhysicalScheduledDescriptionBitCoefficient_ge contracts outer
        requestedRate))

/-- Natural square-root burden used by the fixed A.7 capacity calculation. -/
def fixedPhysicalSymmetricRootBurden
    (kappa rowCoefficient walkLength : ℕ) : ℕ :=
  4 * (168 * (kappa + 1) * rowCoefficient * (walkLength + 1)) ^ 2 *
    16 * 64 ^ 2

/-- Full frozen denominator burden after the exact fixed-copy transport. -/
def fixedPhysicalSymmetricFrozenBurden
    (copies kappa rowCoefficient walkLength : ℕ) : ℕ :=
  copies ^ 3 * (2 * kappa *
    fixedPhysicalSymmetricRootBurden kappa rowCoefficient walkLength)

/-- The complete q-independent capacity burden absorbed by the fixed physical
schedule coefficient.  It depends on contracts, the selected outer proof
exponent, and the requested fixed rate, but never on the public length. -/
noncomputable def fixedPhysicalCapacityBurden
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  fixedPhysicalSymmetricFrozenBurden
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedPhysicalCapacityLiveScale contracts outer)
    (fixedPhysicalSymmetricRowCoefficient contracts outer requestedRate)
    (fixedPhysicalEstimatorWalkLength contracts requestedRate)

/-- The old padding-only coefficient, retained as the intermediate transfer
target. -/
noncomputable def fixedPaddingPhysicalCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℝ :=
  scheduledCoefficient <|
    fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)

/-- Integer denominator factor of the burden-aware fixed schedule. -/
noncomputable def fixedPhysicalScheduleFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate) *
    (fixedPhysicalCapacityBurden contracts outer requestedRate + 1)

theorem fixedPhysicalScheduleFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    0 < fixedPhysicalScheduleFactor contracts outer requestedRate := by
  unfold fixedPhysicalScheduleFactor
  exact Nat.mul_pos
    (fixedCorePaddingFactor_positive outer
      (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)) (by omega)

/-- Fixed physical coefficient with the constant A.7 capacity burden absorbed.
The factor changes only a frozen coefficient; the headline exponent remains
exactly five. -/
noncomputable def fixedPhysicalCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℝ :=
  scheduledCoefficient <|
    fixedPhysicalScheduleFactor contracts outer requestedRate

/-- The legacy additive inventory of contract-derived exponents used by the
compact inverse body.  Keeping the inventory named separately makes the
public degree auditable while allowing fixed implementation overheads to be
absorbed without changing the paper-level quantifier order. -/
noncomputable def inversePhysicalCompactBaseDegreeBudget
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  4096 + inversePhysicalAccuracyExponent contracts outer advantagePower +
    inverseRequiredDegree contracts advantagePower + outer.proofExponent +
    outer.substitutionExponent + (publishedPointwisePCPP contracts).degree +
    (fixedPhysicalExactDecompositionAlgorithm contracts).runner.degree +
    inversePhysicalCopyCoefficient contracts outer advantagePower + 1

noncomputable def inversePhysicalCompactDegreeBudget
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  65536 *
    (inversePhysicalCompactBaseDegreeBudget contracts outer advantagePower + 1) ^ 2

/-- Cycle-free spelling of the two-index live scale used by the compact
inverse resource at the common degree budget. -/
noncomputable def inversePhysicalCapacityLiveScale
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  let degree := inversePhysicalCompactDegreeBudget contracts outer
    advantagePower
  degree + degree + outer.proofExponent + 16

theorem inversePhysicalCapacityLiveScale_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    0 < inversePhysicalCapacityLiveScale contracts outer advantagePower := by
  simp only [inversePhysicalCapacityLiveScale]
  omega

/-- Exact normalized inverse row coefficient at the physical boundary. -/
noncomputable def inversePhysicalSymmetricRowCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  fixedPhysicalSymmetricStructuralBaseCoefficient *
    fixedPhysicalSymmetricChildCoefficient contracts *
    inversePhysicalScheduledDescriptionBitCoefficient contracts outer
      advantagePower

theorem inversePhysicalSymmetricRowCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    0 < inversePhysicalSymmetricRowCoefficient contracts outer
      advantagePower := by
  unfold inversePhysicalSymmetricRowCoefficient
    fixedPhysicalSymmetricChildCoefficient
  exact Nat.mul_pos
    (Nat.mul_pos fixedPhysicalSymmetricStructuralBaseCoefficient_positive
      (Nat.mul_pos (by omega) (by omega)))
    ((show 0 < 4096 by norm_num).trans_le
      (inversePhysicalScheduledDescriptionBitCoefficient_ge contracts outer
        advantagePower))

/-- Linear walk coefficient for the exact inverse accuracy. -/
noncomputable def inversePhysicalSymmetricWalkCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  2 * inversePhysicalAccuracyExponent contracts outer advantagePower + 9

/-- Public/fibre logarithm comparison constant. -/
def inversePhysicalFibreLogCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : ℕ :=
  logScale (widthLinearCoefficient outer 2) + 2

def inversePhysicalSymmetricRootBurden
    (kappa rowCoefficient walkCoefficient : ℕ) : ℕ :=
  4 * (168 * (kappa + 1) * rowCoefficient * (walkCoefficient + 1)) ^ 2 *
    64 * 64 ^ 2

/-- Complete inverse A.12 burden.  All arguments are selected before the
public input length. -/
noncomputable def inversePhysicalCapacityBurden
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  let kappa := inversePhysicalCapacityLiveScale contracts outer advantagePower
  let rowCoefficient := inversePhysicalSymmetricRowCoefficient contracts outer
    advantagePower
  let walkCoefficient := inversePhysicalSymmetricWalkCoefficient contracts
    outer advantagePower
  4 * kappa *
    inversePhysicalSymmetricRootBurden kappa rowCoefficient walkCoefficient *
    inversePhysicalFibreLogCoefficient outer ^ 7

/-- Integer denominator factor of the burden-aware inverse schedule. -/
noncomputable def inversePhysicalScheduleFactor
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  inverseCorePaddingFactor outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower) *
    (inversePhysicalCapacityBurden contracts outer advantagePower + 1)

theorem inversePhysicalScheduleFactor_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    0 < inversePhysicalScheduleFactor contracts outer advantagePower := by
  unfold inversePhysicalScheduleFactor
  exact Nat.mul_pos
    (inverseCorePaddingFactor_positive outer
      (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower)) (by omega)

/-- Inverse physical coefficient with the complete compact-row burden
absorbed.  The headline exponents remain ten and twelve. -/
noncomputable def inversePhysicalCoefficient
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℝ :=
  scheduledCoefficient <|
    inversePhysicalScheduleFactor contracts outer advantagePower

theorem inversePhysicalCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    0 < inversePhysicalCoefficient contracts outer advantagePower := by
  apply scheduledCoefficient_positive
  exact inversePhysicalScheduleFactor_positive contracts outer advantagePower

theorem inversePaddingPhysicalCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    0 < inversePaddingPhysicalCoefficient contracts outer advantagePower := by
  apply scheduledCoefficient_positive
  exact inverseCorePaddingFactor_positive outer
    (publishedPointwisePCPP contracts)
    (inverseRequiredDegree contracts advantagePower)
    (inverseRate contracts advantagePower)

theorem inversePhysicalCoefficient_le_padding
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    inversePhysicalCoefficient contracts outer advantagePower ≤
      inversePaddingPhysicalCoefficient contracts outer advantagePower := by
  unfold inversePhysicalCoefficient inversePhysicalScheduleFactor
    inversePaddingPhysicalCoefficient scheduledCoefficient
  let padding := inverseCorePaddingFactor outer
    (publishedPointwisePCPP contracts)
    (inverseRequiredDegree contracts advantagePower)
    (inverseRate contracts advantagePower)
  have hpadding : 0 < padding := by
    dsimp only [padding]
    exact inverseCorePaddingFactor_positive outer
      (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower)
  have hfactor : padding ≤
      padding * (inversePhysicalCapacityBurden contracts outer
        advantagePower + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpow : ((padding : ℕ) : ℝ) ^ 3 ≤
      ((padding * (inversePhysicalCapacityBurden contracts outer
        advantagePower + 1) : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast Nat.pow_le_pow_left hfactor 3
  exact one_div_le_one_div_of_le (by positivity) hpow

theorem inversePhysicalCoefficient_le_one
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) :
    inversePhysicalCoefficient contracts outer advantagePower ≤ 1 :=
  (inversePhysicalCoefficient_le_padding contracts outer advantagePower).trans <|
    scheduledCoefficient_le_one <|
      inverseCorePaddingFactor_positive outer
        (publishedPointwisePCPP contracts)
        (inverseRequiredDegree contracts advantagePower)
        (inverseRate contracts advantagePower)

theorem fixedPhysicalCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    0 < fixedPhysicalCoefficient contracts outer requestedRate := by
  apply scheduledCoefficient_positive
  exact fixedPhysicalScheduleFactor_positive contracts outer requestedRate

theorem fixedPaddingPhysicalCoefficient_positive
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    0 < fixedPaddingPhysicalCoefficient contracts outer requestedRate := by
  apply scheduledCoefficient_positive
  exact fixedCorePaddingFactor_positive outer
    (publishedPointwisePCPP contracts)
    (fixedRequiredDegree contracts requestedRate)

theorem fixedPhysicalCoefficient_le_padding
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    fixedPhysicalCoefficient contracts outer requestedRate ≤
      fixedPaddingPhysicalCoefficient contracts outer requestedRate := by
  unfold fixedPhysicalCoefficient fixedPhysicalScheduleFactor
    fixedPaddingPhysicalCoefficient
    scheduledCoefficient
  have hpadding : 0 < fixedCorePaddingFactor outer
      (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate) :=
    fixedCorePaddingFactor_positive outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)
  have hfactor :
      fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate) ≤
        fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate) *
          (fixedPhysicalCapacityBurden contracts outer requestedRate + 1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hpow :
      ((fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate) : ℕ) : ℝ) ^ 3 ≤
        ((fixedCorePaddingFactor outer (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate) *
          (fixedPhysicalCapacityBurden contracts outer requestedRate + 1) : ℕ) :
            ℝ) ^ 3 := by
    exact_mod_cast Nat.pow_le_pow_left hfactor 3
  exact one_div_le_one_div_of_le (by positivity) hpow

theorem fixedPhysicalCoefficient_le_one
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) :
    fixedPhysicalCoefficient contracts outer requestedRate ≤ 1 :=
  (fixedPhysicalCoefficient_le_padding contracts outer requestedRate).trans <|
    scheduledCoefficient_le_one <|
      fixedCorePaddingFactor_positive outer (publishedPointwisePCPP contracts)
        (fixedRequiredDegree contracts requestedRate)

/-- The displayed onset is the complete inverse-tier Case-1 readiness
condition: arity six, physical simulation, and advantage are synchronized. -/
noncomputable def inverseCaseOneOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ) : ℕ :=
  max 5 <| max
    (inverseCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower) simulationPower)
    (inverseCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseRate contracts advantagePower) advantagePower)

/-- The fixed-tier onset additionally reserves two inverse powers, converting
the STV error into the exact dyadic XOR target. -/
noncomputable def fixedCaseOneOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  max 5 <| max
    (fixedCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedRate contracts requestedRate) simulationPower)
    (fixedCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedRate contracts requestedRate)
      (fixedRate contracts requestedRate + 2))

private theorem inverseSimulationDegree
    (contracts : PublishedContracts) (advantagePower : ℕ) :
    (2 * simulationPower + 1) *
        (publishedAmplifier contracts).stvExponent ≤
      inverseRequiredDegree contracts advantagePower := by
  unfold inverseRequiredDegree
  apply Nat.mul_le_mul_right
  omega

private theorem inverseAdvantageDegree
    (contracts : PublishedContracts) (advantagePower : ℕ) :
    (2 * advantagePower + 1) *
        (publishedAmplifier contracts).stvExponent ≤
      inverseRequiredDegree contracts advantagePower := by
  unfold inverseRequiredDegree
  apply Nat.mul_le_mul_right
  omega

private theorem fixedSimulationDegree
    (contracts : PublishedContracts) (requestedRate : ℕ) :
    (simulationPower + 1) *
        (publishedAmplifier contracts).stvExponent ≤
      fixedRequiredDegree contracts requestedRate := by
  unfold fixedRequiredDegree
  apply Nat.mul_le_mul_right
  omega

private theorem fixedAdvantageDegree
    (contracts : PublishedContracts) (requestedRate : ℕ) :
    (fixedRate contracts requestedRate + 2 + 1) *
        (publishedAmplifier contracts).stvExponent ≤
      fixedRequiredDegree contracts requestedRate := by
  unfold fixedRequiredDegree
  apply Nat.mul_le_mul_right
  omega

/-- Direct inverse-tier Case-1 constructor.  Every quantitative field is
computed above; the only propositions consumed are the branch's own
hierarchy-YES fact and its canonical numeric onset. -/
noncomputable def inversePhysicalCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    PhysicalCommonCore
      (inversePhysicalCoefficient contracts outer advantagePower)
      (inversePhysicalCoefficient contracts outer advantagePower)
      10 12
        ((inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex) := by
  let amplifier := publishedAmplifier contracts
  let pcppSource := publishedPointwisePCPP contracts
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let arity :=
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
      scheduleIndex
  let raw := hardCoreFromCaseOne (data.amplifierInput hyes)
  have hrate : amplifier.arityCoefficient ≤ rate := by
    exact le_max_left _ _
  have hrawArity : raw.arity ≤ arity := by
    exact data.hardCore_arity_le_inverseEnvelope hyes hrate
  let padded := paddedCaseOneHardCore
    (data.amplifierInput hyes) arity hrawArity
  have hindex : 5 ≤ scheduleIndex := by
    exact (le_max_left 5 _).trans hready
  have harity : 6 ≤ arity := by
    dsimp only [arity]
    rw [inverseCoreEnvelope_coreArity]
    have hcoefficient :
        1 ≤ inverseTightCoreCoefficient outer pcppSource
          requiredDegree rate :=
      (inverseTightCoreCoefficient_positive outer pcppSource
        requiredDegree rate)
    calc
      6 ≤ scheduleIndex + 1 := by omega
      _ ≤ inverseTightCoreCoefficient outer pcppSource
            requiredDegree rate * (scheduleIndex + 1) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (scheduleIndex + 1) hcoefficient
  have hsimulationReady :
      inverseCaseOnePowerOnset outer pcppSource requiredDegree rate
          simulationPower ≤ scheduleIndex := by
    exact
      (le_max_left
        (inverseCaseOnePowerOnset outer pcppSource requiredDegree rate
          simulationPower)
        (inverseCaseOnePowerOnset outer pcppSource requiredDegree rate
          advantagePower)).trans
        ((le_max_right 5 _).trans hready)
  have hsize :
      arity ^ simulationPower ≤ raw.size := by
    exact
      NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_size_ge_inverseCorePower
        data hyes hsimulationReady
        (inverseSimulationDegree contracts advantagePower)
  have hcoefficientNonnegative :
      0 ≤ inversePhysicalCoefficient contracts outer advantagePower :=
    le_of_lt (inversePhysicalCoefficient_positive contracts outer
      advantagePower)
  have hcoefficientOne :
      inversePhysicalCoefficient contracts outer advantagePower ≤ 1 := by
    exact inversePhysicalCoefficient_le_one contracts outer advantagePower
  apply physicalCommonCoreOfBoolean contracts.thresholdNormalization padded
    (inversePhysicalCoefficient contracts outer advantagePower)
    (inversePhysicalCoefficient contracts outer advantagePower) 10 12
  · apply (simulationCost_le_power 40 10 arity (by omega) harity
      hcoefficientNonnegative hcoefficientOne).trans
    change arity ^ simulationPower ≤ raw.size
    exact hsize
  · apply (simulationCost_le_power 50 12 arity (by omega) harity
      hcoefficientNonnegative hcoefficientOne).trans
    change arity ^ simulationPower ≤ raw.size
    exact hsize

@[simp] theorem inversePhysicalCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    (inversePhysicalCore contracts outer advantagePower scheduleIndex
      data hyes hready).advantage =
        (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage := by
  rfl

theorem inversePhysicalCore_function
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    ∃ hcore :
        (hardCoreFromCaseOne (data.amplifierInput hyes)).arity ≤
          (inverseEnvelope contracts outer advantagePower).coreArity
            scheduleIndex,
      (inversePhysicalCore contracts outer advantagePower scheduleIndex
          data hyes hready).function =
        padCore (hardCoreFromCaseOne (data.amplifierInput hyes)).function
          hcore := by
  let hcore :=
    data.hardCore_arity_le_inverseEnvelope
      (pcppSource := publishedPointwisePCPP contracts) hyes
      (le_max_left (publishedAmplifier contracts).arityCoefficient
        (2 * advantagePower + 1))
  exact ⟨hcore, rfl⟩

/-- The physical core is exactly the padded published amplification of the
C.12-recovered accepting proof, not merely an extensionally related witness. -/
theorem inversePhysicalCore_function_eq_recoveredAmplification
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    ∃ hamp :
        ((publishedAmplifier contracts).algorithm.amplify
          (scheduledWidth outer (inverseSourceIndex scheduleIndex))
          (recoveredOuterProofFunction (paddedOuterPCP outer) input)).outputArity
          ≤ (inverseEnvelope contracts outer advantagePower).coreArity
            scheduleIndex,
      (inversePhysicalCore contracts outer advantagePower scheduleIndex
          data hyes hready).function =
        padCore
          ((publishedAmplifier contracts).algorithm.amplify
            (scheduledWidth outer (inverseSourceIndex scheduleIndex))
            (recoveredOuterProofFunction
              (paddedOuterPCP outer) input)).function
          hamp := by
  rcases inversePhysicalCore_function contracts outer advantagePower
    scheduleIndex data hyes hready with ⟨hcore, hfunction⟩
  have harity :=
    ScheduledCaseOneData.hardCore_arity_eq_recoveredAmplification data hyes
  have hdependent :=
    ScheduledCaseOneData.hardCore_eq_recoveredAmplification data hyes
  have hamp :
      ((publishedAmplifier contracts).algorithm.amplify
        (scheduledWidth outer (inverseSourceIndex scheduleIndex))
        (recoveredOuterProofFunction
          (paddedOuterPCP outer) input)).outputArity ≤
        (inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex := by
    rw [← harity]
    exact hcore
  refine ⟨hamp, hfunction.trans ?_⟩
  exact padCore_eq_of_dependent_function_eq hdependent hcore hamp

theorem inversePhysicalCore_advantage_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts advantagePower)
      (inverseSourceIndex scheduleIndex) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    (inversePhysicalCore contracts outer advantagePower scheduleIndex
        data hyes hready).advantage ≤
      inversePolynomialAdvantage
        ((inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex)
        (advantagePower : ℝ) := by
  apply
    NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_advantage_le_inverseCore
      data hyes
  · exact
      (le_max_right
        (inverseCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseRate contracts advantagePower) simulationPower)
        (inverseCaseOnePowerOnset outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseRate contracts advantagePower) advantagePower)).trans
        ((le_max_right 5 _).trans hready)
  · exact inverseAdvantageDegree contracts advantagePower

/-- Two extra inverse powers convert a core of arity at least two into the
fixed tier's exact dyadic reserve. -/
theorem inversePower_le_fixedReserve
    (arity rate : ℕ) (harity : 2 ≤ arity) :
    inversePolynomialAdvantage arity ((rate + 2 : ℕ) : ℝ) ≤
      1 / (2 : ℝ) ^ rate / 4 := by
  rw [inversePolynomialAdvantage_natPower arity (rate + 2) (by omega)]
  have hpowerNat :
      2 ^ (rate + 2) ≤ arity ^ (rate + 2) :=
    Nat.pow_le_pow_left harity (rate + 2)
  have hpowerReal :
      (2 : ℝ) ^ (rate + 2) ≤ (arity : ℝ) ^ (rate + 2) := by
    exact_mod_cast hpowerNat
  calc
    1 / (arity : ℝ) ^ (rate + 2) ≤
        1 / (2 : ℝ) ^ (rate + 2) :=
      one_div_le_one_div_of_le (by positivity) hpowerReal
    _ = 1 / (2 : ℝ) ^ rate / 4 := by
      rw [pow_add]
      norm_num
      ring

/-- Direct fixed-tier Case-1 constructor with the same closed quantitative
boundary as `inversePhysicalCore`. -/
noncomputable def fixedPhysicalCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤ sourceIndex) :
    PhysicalCommonCore
      (fixedPhysicalCoefficient contracts outer requestedRate)
      (fixedPhysicalCoefficient contracts outer requestedRate)
      5 9
        ((fixedEnvelope contracts outer requestedRate).coreArity
          sourceIndex) := by
  let amplifier := publishedAmplifier contracts
  let pcppSource := publishedPointwisePCPP contracts
  let requiredDegree := fixedRequiredDegree contracts requestedRate
  let rate := fixedRate contracts requestedRate
  let arity :=
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
      sourceIndex
  let raw := hardCoreFromCaseOne (data.amplifierInput hyes)
  have hrate : amplifier.arityCoefficient ≤ rate := by
    exact le_max_left _ _
  have hrawArity : raw.arity ≤ arity := by
    exact data.hardCore_arity_le_fixedEnvelope hyes hrate
  let padded := paddedCaseOneHardCore
    (data.amplifierInput hyes) arity hrawArity
  have hindex : 5 ≤ sourceIndex := by
    exact (le_max_left 5 _).trans hready
  have harity : 6 ≤ arity := by
    dsimp only [arity]
    rw [fixedCoreEnvelope_coreArity]
    have hcoefficient :
        1 ≤ fixedRawLinearCoefficient outer pcppSource
          requiredDegree rate :=
      (fixedRawLinearCoefficient_positive outer pcppSource
        requiredDegree rate)
    calc
      6 ≤ sourceIndex + 1 := by omega
      _ ≤ fixedRawLinearCoefficient outer pcppSource
            requiredDegree rate * (sourceIndex + 1) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (sourceIndex + 1) hcoefficient
  have hsimulationReady :
      fixedCaseOnePowerOnset outer pcppSource requiredDegree rate
          simulationPower ≤ sourceIndex := by
    exact
      (le_max_left
        (fixedCaseOnePowerOnset outer pcppSource requiredDegree rate
          simulationPower)
        (fixedCaseOnePowerOnset outer pcppSource requiredDegree rate
          (rate + 2))).trans
        ((le_max_right 5 _).trans hready)
  have hsize :
      arity ^ simulationPower ≤ raw.size := by
    exact
      NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_size_ge_fixedCorePower
        data hyes hsimulationReady
        (fixedSimulationDegree contracts requestedRate)
  have hcoefficientNonnegative :
      0 ≤ fixedPhysicalCoefficient contracts outer requestedRate :=
    le_of_lt (fixedPhysicalCoefficient_positive contracts outer requestedRate)
  have hcoefficientOne :
      fixedPhysicalCoefficient contracts outer requestedRate ≤ 1 := by
    exact fixedPhysicalCoefficient_le_one contracts outer requestedRate
  apply physicalCommonCoreOfBoolean contracts.thresholdNormalization padded
    (fixedPhysicalCoefficient contracts outer requestedRate)
    (fixedPhysicalCoefficient contracts outer requestedRate) 5 9
  · apply (simulationCost_le_power 40 5 arity (by omega) harity
      hcoefficientNonnegative hcoefficientOne).trans
    change arity ^ simulationPower ≤ raw.size
    exact hsize
  · apply (simulationCost_le_power 50 9 arity (by omega) harity
      hcoefficientNonnegative hcoefficientOne).trans
    change arity ^ simulationPower ≤ raw.size
    exact hsize

@[simp] theorem fixedPhysicalCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤ sourceIndex) :
    (fixedPhysicalCore contracts outer requestedRate sourceIndex
      data hyes hready).advantage =
        (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage := by
  rfl

theorem fixedPhysicalCore_function
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤ sourceIndex) :
    ∃ hcore :
        (hardCoreFromCaseOne (data.amplifierInput hyes)).arity ≤
          (fixedEnvelope contracts outer requestedRate).coreArity sourceIndex,
      (fixedPhysicalCore contracts outer requestedRate sourceIndex
          data hyes hready).function =
        padCore (hardCoreFromCaseOne (data.amplifierInput hyes)).function
          hcore := by
  let hcore :=
    data.hardCore_arity_le_fixedEnvelope
      (pcppSource := publishedPointwisePCPP contracts) hyes
      (le_max_left (publishedAmplifier contracts).arityCoefficient
        requestedRate)
  exact ⟨hcore, rfl⟩

/-- Fixed-rate schedules use the same exact recovered-proof amplification
pipeline as the inverse-polynomial schedules. -/
theorem fixedPhysicalCore_function_eq_recoveredAmplification
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤ sourceIndex) :
    ∃ hamp :
        ((publishedAmplifier contracts).algorithm.amplify
          (scheduledWidth outer sourceIndex)
          (recoveredOuterProofFunction
            (paddedOuterPCP outer) input)).outputArity ≤
          (fixedEnvelope contracts outer requestedRate).coreArity sourceIndex,
      (fixedPhysicalCore contracts outer requestedRate sourceIndex
          data hyes hready).function =
        padCore
          ((publishedAmplifier contracts).algorithm.amplify
            (scheduledWidth outer sourceIndex)
            (recoveredOuterProofFunction
              (paddedOuterPCP outer) input)).function
          hamp := by
  rcases fixedPhysicalCore_function contracts outer requestedRate sourceIndex
    data hyes hready with ⟨hcore, hfunction⟩
  have harity :=
    ScheduledCaseOneData.hardCore_arity_eq_recoveredAmplification data hyes
  have hdependent :=
    ScheduledCaseOneData.hardCore_eq_recoveredAmplification data hyes
  have hamp :
      ((publishedAmplifier contracts).algorithm.amplify
        (scheduledWidth outer sourceIndex)
        (recoveredOuterProofFunction
          (paddedOuterPCP outer) input)).outputArity ≤
        (fixedEnvelope contracts outer requestedRate).coreArity sourceIndex := by
    rw [← harity]
    exact hcore
  refine ⟨hamp, hfunction.trans ?_⟩
  exact padCore_eq_of_dependent_function_eq hdependent hcore hamp

theorem fixedPhysicalCore_advantage_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate) sourceIndex input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤ sourceIndex) :
    (fixedPhysicalCore contracts outer requestedRate sourceIndex
        data hyes hready).advantage ≤
      1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 := by
  let rate := fixedRate contracts requestedRate
  have hpower :
      (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage ≤
        inversePolynomialAdvantage
          ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)
          ((rate + 2 : ℕ) : ℝ) := by
    apply
      NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_advantage_le_fixedCore
        data hyes
    · exact
        (le_max_right
          (fixedCaseOnePowerOnset outer
            (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate)
            (fixedRate contracts requestedRate) simulationPower)
          (fixedCaseOnePowerOnset outer
            (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate)
            (fixedRate contracts requestedRate)
            (fixedRate contracts requestedRate + 2))).trans
          ((le_max_right 5 _).trans hready)
    · exact fixedAdvantageDegree contracts requestedRate
  change
    (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage ≤
      1 / (2 : ℝ) ^ rate / 4
  exact hpower.trans <|
    inversePower_le_fixedReserve
      ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)
      rate (by
        have hindex : 5 ≤ sourceIndex :=
          (le_max_left 5 _).trans hready
        rw [fixedEnvelope, fixedCoreEnvelope_coreArity]
        have hcoefficient :
            1 ≤ fixedRawLinearCoefficient outer
              (publishedPointwisePCPP contracts)
              (fixedRequiredDegree contracts requestedRate)
              (fixedRate contracts requestedRate) :=
          fixedRawLinearCoefficient_positive outer
            (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate)
            (fixedRate contracts requestedRate)
        calc
          2 ≤ sourceIndex + 1 := by omega
          _ ≤ fixedRawLinearCoefficient outer
                (publishedPointwisePCPP contracts)
                (fixedRequiredDegree contracts requestedRate)
                (fixedRate contracts requestedRate) *
              (sourceIndex + 1) := by
            simpa only [one_mul] using
              Nat.mul_le_mul_right (sourceIndex + 1) hcoefficient)

/-- One computed onset simultaneously makes the inverse selector executable,
the chosen source Case-1-ready, and the final padding reserve large enough. -/
noncomputable def inverseCaseOneTargetOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) : ℕ :=
  let power := inverseCoreAdvantagePower advantageExponent
  let envelope := inverseEnvelope contracts outer power
  max envelope.targetOnset <| max
    (2 * envelope.coreArity
      (inverseCaseOneOnset contracts outer power))
    (3 * 3 ^ inverseAdvantagePower advantageExponent)

/-- Fixed-tier onset needs only selector execution and Case-1 source
readiness; its advantage reserve is independent of the target. -/
noncomputable def fixedCaseOneTargetOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ) : ℕ :=
  let envelope := fixedEnvelope contracts outer requestedRate
  max envelope.targetOnset <|
    2 * envelope.coreArity
      (fixedCaseOneOnset contracts outer requestedRate)

theorem inverseCaseOneTargetOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target) :
    (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target ∧
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target ∧
      3 * 3 ^ inverseAdvantagePower advantageExponent ≤ target := by
  let power := inverseCoreAdvantagePower advantageExponent
  let envelope := inverseEnvelope contracts outer power
  have htarget : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans hlarge
  have hsourceTarget :
      2 * envelope.coreArity
          (inverseCaseOneOnset contracts outer power) ≤ target :=
    (le_max_left
      (2 * envelope.coreArity
        (inverseCaseOneOnset contracts outer power))
      (3 * 3 ^ inverseAdvantagePower advantageExponent)).trans <|
        (le_max_right envelope.targetOnset _).trans hlarge
  have hsource :=
    (inverseSchedule contracts outer power).output_source_ge
      target htarget (inverseCaseOneOnset contracts outer power)
      hsourceTarget
  have hadvantage :
      3 * 3 ^ inverseAdvantagePower advantageExponent ≤ target :=
    (le_max_right
      (2 * envelope.coreArity
        (inverseCaseOneOnset contracts outer power))
      (3 * 3 ^ inverseAdvantagePower advantageExponent)).trans <|
        (le_max_right envelope.targetOnset _).trans hlarge
  exact ⟨htarget, hsource, hadvantage⟩

theorem fixedCaseOneTargetOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target) :
    (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target ∧
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target := by
  let envelope := fixedEnvelope contracts outer requestedRate
  have htarget : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans hlarge
  have hsourceTarget :
      2 * envelope.coreArity
          (fixedCaseOneOnset contracts outer requestedRate) ≤ target :=
    (le_max_right envelope.targetOnset _).trans hlarge
  have hsource :=
    (fixedSchedule contracts outer requestedRate).output_source_ge
      target htarget (fixedCaseOneOnset contracts outer requestedRate)
      hsourceTarget
  exact ⟨htarget, hsource⟩

/-- Convert a target tail into readiness for any theorem stated at the actual
inverse refuter-input length, accounting for the `q log q` source map. -/
theorem inverseSelectedInputReady
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer advantagePower).targetOnset ≤ target)
    (inputOnset : ℕ)
    (hlarge :
      2 * (inverseEnvelope contracts outer advantagePower).coreArity
          (inverseSourceMeasure inputOnset) ≤ target) :
    inputOnset ≤
      sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer advantagePower target)) := by
  have hschedule :
      inverseSourceMeasure inputOnset ≤
        inverseSelectedSource contracts outer advantagePower target :=
    (inverseSchedule contracts outer advantagePower).output_source_ge
      target htarget (inverseSourceMeasure inputOnset) hlarge
  have hinverse :
      inputOnset ≤ inverseSourceIndex
        (inverseSelectedSource contracts outer advantagePower target) := by
    apply le_inverseSourceIndex_of_measure_le
    omega
  exact (sourceIndex_le_sourceLength inputOnset).trans <|
    sourceLength_monotone hinverse

/-- Linear-schedule counterpart of `inverseSelectedInputReady`. -/
theorem fixedSelectedInputReady
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    (inputOnset : ℕ)
    (hlarge :
      2 * (fixedEnvelope contracts outer requestedRate).coreArity
          inputOnset ≤ target) :
    inputOnset ≤ sourceLength
      (fixedSelectedSource contracts outer requestedRate target) := by
  have hsource :
      inputOnset ≤
        fixedSelectedSource contracts outer requestedRate target :=
    (fixedSchedule contracts outer requestedRate).output_source_ge
      target htarget inputOnset hlarge
  exact hsource.trans <|
    sourceIndex_le_sourceLength
      (fixedSelectedSource contracts outer requestedRate target)

/-- Strengthen the Case-1 target tail with any source-length obligation, such
as the onset returned by the concrete refuter conflict theorem. -/
noncomputable def inverseRefuterTargetOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (inputOnset : ℕ) : ℕ :=
  max (inverseCaseOneTargetOnset contracts outer advantageExponent) <|
    2 * (inverseEnvelope contracts outer
      (inverseCoreAdvantagePower advantageExponent)).coreArity
        (inverseSourceMeasure inputOnset)

theorem inverseRefuterTargetOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (inputOnset target : ℕ)
    (hlarge :
      inverseRefuterTargetOnset contracts outer advantageExponent inputOnset ≤
        target) :
    inputOnset ≤
      sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)) ∧
      (inverseEnvelope contracts outer
          (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target ∧
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target ∧
      3 * 3 ^ inverseAdvantagePower advantageExponent ≤ target := by
  let ready :=
    inverseCaseOneTargetOnset_ready contracts outer advantageExponent target
      ((le_max_left _ _).trans hlarge)
  have hinputTarget :
      2 * (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).coreArity
          (inverseSourceMeasure inputOnset) ≤ target :=
    (le_max_right
      (inverseCaseOneTargetOnset contracts outer advantageExponent) _).trans
        hlarge
  exact
    ⟨inverseSelectedInputReady contracts outer
      (inverseCoreAdvantagePower advantageExponent) target ready.1 inputOnset
      hinputTarget,
    ready⟩

/-- Fixed-rate counterpart of `inverseRefuterTargetOnset`. -/
noncomputable def fixedRefuterTargetOnset
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate inputOnset : ℕ) : ℕ :=
  max (fixedCaseOneTargetOnset contracts outer requestedRate) <|
    2 * (fixedEnvelope contracts outer requestedRate).coreArity inputOnset

theorem fixedRefuterTargetOnset_ready
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate inputOnset target : ℕ)
    (hlarge :
      fixedRefuterTargetOnset contracts outer requestedRate inputOnset ≤
        target) :
    inputOnset ≤ sourceLength
        (fixedSelectedSource contracts outer requestedRate target) ∧
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target ∧
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target := by
  let ready :=
    fixedCaseOneTargetOnset_ready contracts outer requestedRate target
      ((le_max_left _ _).trans hlarge)
  have hinputTarget :
      2 * (fixedEnvelope contracts outer requestedRate).coreArity inputOnset ≤
        target :=
    (le_max_right
      (fixedCaseOneTargetOnset contracts outer requestedRate) _).trans hlarge
  exact
    ⟨fixedSelectedInputReady contracts outer requestedRate target ready.1
      inputOnset hinputTarget,
    ready⟩

/-- Contract-closed inverse target tail: every selected branch word is both a
hierarchy-YES instance and a rejection of the same concrete machine. -/
theorem inversePublishedTargetConflict
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hdegree : machine.verifier.degree ≤ 2 ^ clockDepth)
    (hsaving : 1 ≤ machine.verifier.logPower)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10)
    (honeSided : EventuallyOneSided
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
      machine)
    (advantageExponent : ℝ) :
    ∃ targetOnset, ∀ target, targetOnset ≤ target →
      let source := publishedRefuterSource contracts clockDepth
      let outer := publishedHierarchyOuterPCP contracts clockDepth
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target ∧
        source.hierarchyMachine.accepts
            (sourceLength (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
            (inverseRefuterInput contracts outer machine advantageExponent
              target) = true ∧
          ¬machine.toSemantic.accepts
            (inverseRefuterInput contracts outer machine advantageExponent
              target) := by
  rcases publishedRefuter_eventualConflict contracts clockDepth machine
      hdegree hsaving hwitness honeSided with
    ⟨inputOnset, conflict⟩
  let outer := publishedHierarchyOuterPCP contracts clockDepth
  refine
    ⟨inverseRefuterTargetOnset contracts outer advantageExponent inputOnset,
      ?_⟩
  intro target hlarge
  dsimp only
  have ready :=
    inverseRefuterTargetOnset_ready contracts outer advantageExponent
      inputOnset target hlarge
  refine ⟨(le_max_left _ _).trans hlarge, ?_⟩
  simpa only [inverseRefuterInput] using conflict _ ready.1

/-- Contract-closed fixed-rate target conflict for the same selected refuter
and canonical outer branch. -/
theorem fixedPublishedTargetConflict
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hdegree : machine.verifier.degree ≤ 2 ^ clockDepth)
    (hsaving : 1 ≤ machine.verifier.logPower)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10)
    (honeSided : EventuallyOneSided
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
      machine)
    (requestedRate : ℕ) :
    ∃ targetOnset, ∀ target, targetOnset ≤ target →
      let source := publishedRefuterSource contracts clockDepth
      let outer := publishedHierarchyOuterPCP contracts clockDepth
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target ∧
        source.hierarchyMachine.accepts
            (sourceLength
              (fixedSelectedSource contracts outer requestedRate target))
            (fixedRefuterInput contracts outer machine requestedRate target) =
              true ∧
          ¬machine.toSemantic.accepts
            (fixedRefuterInput contracts outer machine requestedRate target) := by
  rcases publishedRefuter_eventualConflict contracts clockDepth machine
      hdegree hsaving hwitness honeSided with
    ⟨inputOnset, conflict⟩
  let outer := publishedHierarchyOuterPCP contracts clockDepth
  refine
    ⟨fixedRefuterTargetOnset contracts outer requestedRate inputOnset, ?_⟩
  intro target hlarge
  dsimp only
  have ready :=
    fixedRefuterTargetOnset_ready contracts outer requestedRate inputOnset
      target hlarge
  refine ⟨(le_max_left _ _).trans hlarge, ?_⟩
  simpa only [fixedRefuterInput] using conflict _ ready.1

/-- The decoded inverse predecessor satisfies the exact two inequalities
consumed by the physical padding theorem. -/
theorem inverseSelectedCoreBounds
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer advantagePower).targetOnset ≤ target) :
    (inverseEnvelope contracts outer advantagePower).coreArity
        (inverseSelectedSource contracts outer advantagePower target) ≤ target ∧
      target < 3 *
        (inverseEnvelope contracts outer advantagePower).coreArity
          (inverseSelectedSource contracts outer advantagePower target) := by
  let schedule := inverseSchedule contracts outer advantagePower
  have houtput := schedule.output_core_eq target htarget
  constructor
  · rw [show
      inverseSelectedSource contracts outer advantagePower target =
        (schedule.output target).source by rfl, ← houtput.1]
    exact schedule.output_core_le_target target htarget
  · rw [show
      inverseSelectedSource contracts outer advantagePower target =
        (schedule.output target).source by rfl, ← houtput.1]
    exact schedule.output_target_lt_three_core target htarget

/-- Fixed-tier counterpart of `inverseSelectedCoreBounds`. -/
theorem fixedSelectedCoreBounds
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target) :
    (fixedEnvelope contracts outer requestedRate).coreArity
        (fixedSelectedSource contracts outer requestedRate target) ≤ target ∧
      target < 3 *
        (fixedEnvelope contracts outer requestedRate).coreArity
          (fixedSelectedSource contracts outer requestedRate target) := by
  let schedule := fixedSchedule contracts outer requestedRate
  have houtput := schedule.output_core_eq target htarget
  constructor
  · rw [show fixedSelectedSource contracts outer requestedRate target =
      (schedule.output target).source by rfl, ← houtput.1]
    exact schedule.output_core_le_target target htarget
  · rw [show fixedSelectedSource contracts outer requestedRate target =
      (schedule.output target).source by rfl, ← houtput.1]
    exact schedule.output_target_lt_three_core target htarget

/-- The target-length inverse function is determined by published contracts,
the decoded source, and the actual Case-1 branch data. -/
noncomputable def inverseCaseOneTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target) :
    BoolFunction target :=
  padCore
    (inversePhysicalCore contracts outer
      (inverseCoreAdvantagePower advantageExponent)
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)
      data hyes hready).function
    (inverseSelectedCoreBounds contracts outer
      (inverseCoreAdvantagePower advantageExponent) target htarget).1

/-- Fixed-tier target function selected by the same canonical interpreter. -/
noncomputable def fixedCaseOneTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target) :
    BoolFunction target :=
  padCore
    (fixedPhysicalCore contracts outer requestedRate
      (fixedSelectedSource contracts outer requestedRate target)
      data hyes hready).function
    (fixedSelectedCoreBounds contracts outer requestedRate target htarget).1

theorem inverseCaseOneTargetFunction_eq
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target) :
    inverseCaseOneTargetFunction contracts outer advantageExponent target
        htarget data hyes hready =
      padCore
        (inversePhysicalCore contracts outer
          (inverseCoreAdvantagePower advantageExponent)
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target)
          data hyes hready).function
        (inverseSelectedCoreBounds contracts outer
          (inverseCoreAdvantagePower advantageExponent) target htarget).1 := by
  rfl

theorem fixedCaseOneTargetFunction_eq
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target) :
    fixedCaseOneTargetFunction contracts outer requestedRate target
        htarget data hyes hready =
      padCore
        (fixedPhysicalCore contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          data hyes hready).function
        (fixedSelectedCoreBounds contracts outer requestedRate target
          htarget).1 := by
  rfl

theorem scheduledInverseAdvantage_le_target
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget : envelope.targetOnset ≤ target)
    (hadvantageReady :
      3 * 3 ^ inverseAdvantagePower advantageExponent ≤ target) :
    inversePolynomialAdvantage
        (envelope.coreArity (schedule.output target).source)
        (inverseCoreAdvantagePower advantageExponent : ℝ) ≤
      inversePolynomialAdvantage target (advantageExponent + 1) := by
  let selection := schedule.select target htarget
  have houtput := schedule.output_core_eq target htarget
  rw [← houtput.1]
  exact inverseCoreAdvantage_le_target advantageExponent selection <|
    selectedCore_exceeds_power selection hadvantageReady

theorem paddedPhysicalModeHardness_mono
    {sourceAdvantage targetAdvantage
      symmetricCoefficient thresholdCoefficient : ℝ}
    {symmetricLogExponent thresholdLogExponent : ℕ}
    {mode : AppendixC.Mode} {n : ℕ} {function : BoolFunction n}
    (hadvantage : sourceAdvantage ≤ targetAdvantage)
    (hard : PaddedPhysicalModeHardness sourceAdvantage
      symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent mode function) :
    PaddedPhysicalModeHardness targetAdvantage
      symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent mode function := by
  cases mode with
  | symmetric =>
      intro circuit hwires
      exact (hard circuit hwires).trans <| by
        gcongr
  | threshold =>
      intro circuit hwires
      exact (hard circuit hwires).trans <| by
        gcongr

/-- Close the inverse Case-1 branch at the exact target selected by the
executable schedule.  No selector, hard function, or hardness callback is
supplied by the caller. -/
theorem inverseCaseOneTargetHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
    (hadvantageReady :
      3 * 3 ^ inverseAdvantagePower advantageExponent ≤ target) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (inversePolynomialAdvantage target (advantageExponent + 1))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        10 12 mode
        (inverseCaseOneTargetFunction contracts outer advantageExponent target
          htarget data hyes hready) := by
  let power := inverseCoreAdvantagePower advantageExponent
  let scheduleIndex :=
    inverseSelectedSource contracts outer power target
  let bounds :=
    inverseSelectedCoreBounds contracts outer power target htarget
  let core :=
    inversePhysicalCore contracts outer power scheduleIndex
      data hyes hready
  have hpadded :=
    padPhysicalCommonCore
      (le_of_lt (inversePhysicalCoefficient_positive contracts outer power))
      (le_of_lt (inversePhysicalCoefficient_positive contracts outer power))
      10 12 target bounds.1 bounds.2 core
  have hschedule :=
    scheduledInverseAdvantage_le_target
      (inverseSchedule contracts outer power)
      advantageExponent target htarget hadvantageReady
  change
    inversePolynomialAdvantage
        ((inverseEnvelope contracts outer power).coreArity scheduleIndex)
        (power : ℝ) ≤
      inversePolynomialAdvantage target (advantageExponent + 1) at hschedule
  have hadvantage :
      core.advantage ≤
        inversePolynomialAdvantage target (advantageExponent + 1) :=
    (inversePhysicalCore_advantage_le contracts outer power scheduleIndex
      data hyes hready).trans hschedule
  rw [inverseCaseOneTargetFunction_eq contracts outer advantageExponent
    target htarget data hyes hready]
  intro mode
  exact paddedPhysicalModeHardness_mono hadvantage (hpadded mode)

/-- Fixed-tier target closure for the same executable selector.  Its exact
dyadic reserve is derived from the published amplifier rather than accepted
as a local proposition. -/
theorem fixedCaseOneTargetHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        5 9 mode
        (fixedCaseOneTargetFunction contracts outer requestedRate target
          htarget data hyes hready) := by
  let sourceIndex :=
    fixedSelectedSource contracts outer requestedRate target
  let bounds :=
    fixedSelectedCoreBounds contracts outer requestedRate target htarget
  let core :=
    fixedPhysicalCore contracts outer requestedRate sourceIndex
      data hyes hready
  have hpadded :=
    padPhysicalCommonCore
      (le_of_lt
        (fixedPhysicalCoefficient_positive contracts outer requestedRate))
      (le_of_lt
        (fixedPhysicalCoefficient_positive contracts outer requestedRate))
      5 9 target bounds.1 bounds.2 core
  have hadvantage :
      core.advantage ≤
        1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 :=
    fixedPhysicalCore_advantage_le contracts outer requestedRate sourceIndex
      data hyes hready
  rw [fixedCaseOneTargetFunction_eq contracts outer requestedRate target
    htarget data hyes hready]
  intro mode
  exact paddedPhysicalModeHardness_mono hadvantage (hpadded mode)

/-- Eventual inverse Case-1 closure.  The sole size premise is membership in
the computed target tail; selector execution and all numeric readiness facts
are reconstructed internally. -/
theorem inverseScheduledCaseOneHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input) :
    let ready :=
      inverseCaseOneTargetOnset_ready contracts outer advantageExponent
        target hlarge
    ∀ mode,
      PaddedPhysicalModeHardness
        (inversePolynomialAdvantage target (advantageExponent + 1))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        10 12 mode
        (inverseCaseOneTargetFunction contracts outer advantageExponent target
          ready.1 data hyes ready.2.1) := by
  let ready :=
    inverseCaseOneTargetOnset_ready contracts outer advantageExponent
      target hlarge
  exact
    inverseCaseOneTargetHardness contracts outer advantageExponent target
      ready.1 data hyes ready.2.1 ready.2.2

/-- Fixed-tier eventual closure with the same single tail premise. -/
theorem fixedScheduledCaseOneHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      input) :
    let ready :=
      fixedCaseOneTargetOnset_ready contracts outer requestedRate target hlarge
    ∀ mode,
      PaddedPhysicalModeHardness
        (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        5 9 mode
        (fixedCaseOneTargetFunction contracts outer requestedRate target
          ready.1 data hyes ready.2) := by
  let ready :=
    fixedCaseOneTargetOnset_ready contracts outer requestedRate target hlarge
  exact
    fixedCaseOneTargetHardness contracts outer requestedRate target
      ready.1 data hyes ready.2

/-- Eliminate the canonical inverse branch as far as the published Case-1
theorems permit.  In Case 2 the sole remaining fact is rejection of the exact
same refuter input, ready for the componentwise machine argument. -/
theorem inverseTargetBranch_progress
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hreject : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target)) :
    match inverseTargetBranch contracts outer machine advantageExponent target
        hyes with
    | .caseOne data =>
        let ready :=
          inverseCaseOneTargetOnset_ready contracts outer advantageExponent
            target hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (inversePolynomialAdvantage target (advantageExponent + 1))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            10 12 mode
            (inverseCaseOneTargetFunction contracts outer advantageExponent
              target ready.1 data hyes ready.2.1)
    | .caseTwo _ => ¬machine.toSemantic.accepts
        (inverseRefuterInput contracts outer machine advantageExponent
          target) := by
  cases hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
        hyes with
  | caseOne data =>
      exact inverseScheduledCaseOneHardness contracts outer advantageExponent
        target hlarge data hyes
  | caseTwo _ =>
      exact hreject

/-- Fixed-rate counterpart of `inverseTargetBranch_progress`. -/
theorem fixedTargetBranch_progress
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hreject : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target)) :
    match fixedTargetBranch contracts outer machine requestedRate target hyes with
    | .caseOne data =>
        let ready :=
          fixedCaseOneTargetOnset_ready contracts outer requestedRate target
            hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            5 9 mode
            (fixedCaseOneTargetFunction contracts outer requestedRate target
              ready.1 data hyes ready.2)
    | .caseTwo _ => ¬machine.toSemantic.accepts
        (fixedRefuterInput contracts outer machine requestedRate target) := by
  cases hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes with
  | caseOne data =>
      exact fixedScheduledCaseOneHardness contracts outer requestedRate target
        hlarge data hyes
  | caseTwo _ =>
      exact hreject

/-- Padding-only inverse transfer retained as the intermediate target. -/
theorem inversePaddingPhysicalWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex logExponent : ℕ) :
    wireScale (inversePaddingPhysicalCoefficient contracts outer advantagePower)
        logExponent
        ((inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex) ≤
      wireScale 1 logExponent
        (inverseScheduledRawCoreArity outer
          (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseRate contracts advantagePower) scheduleIndex) := by
  unfold inversePaddingPhysicalCoefficient scheduledCoefficient inverseEnvelope
  apply NearCubicWires.RecoveryScheduleTransfer.inverseCoreWireScale_le_raw
  · exact (publishedAmplifier contracts).arityCoefficientPositive.trans
      (le_max_left _ _)
  · norm_num

/-- The burden-aware inverse coefficient remains below the raw Case-2 cap. -/
theorem inversePhysicalWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex logExponent : ℕ) :
    wireScale (inversePhysicalCoefficient contracts outer advantagePower)
        logExponent
        ((inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex) ≤
      wireScale 1 logExponent
        (inverseScheduledRawCoreArity outer
          (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseRate contracts advantagePower) scheduleIndex) := by
  exact
    (wireScale_mono_coefficient
      (inversePhysicalCoefficient_le_padding contracts outer advantagePower)
      logExponent
      ((inverseEnvelope contracts outer advantagePower).coreArity
        scheduleIndex)).trans
      (inversePaddingPhysicalWireScale_le_raw contracts outer advantagePower
        scheduleIndex logExponent)

/-- Padding-only fixed-tier counterpart of
`inversePhysicalWireScale_le_raw`. -/
theorem fixedPaddingPhysicalWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex logExponent : ℕ) :
    wireScale (fixedPaddingPhysicalCoefficient contracts outer requestedRate)
        logExponent
        ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex) ≤
      wireScale 1 logExponent
        (fixedRawCoreArity outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedRate contracts requestedRate) sourceIndex) := by
  unfold fixedPaddingPhysicalCoefficient scheduledCoefficient fixedEnvelope
  apply NearCubicWires.RecoveryScheduleTransfer.fixedCoreWireScale_le_raw
  norm_num

/-- Fixed-tier transfer after the frozen A.7 burden is absorbed.  Shrinking
the coefficient can only decrease the scheduled wire cap. -/
theorem fixedPhysicalWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex logExponent : ℕ) :
    wireScale (fixedPhysicalCoefficient contracts outer requestedRate)
        logExponent
        ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex) ≤
      wireScale 1 logExponent
        (fixedRawCoreArity outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedRate contracts requestedRate) sourceIndex) := by
  exact
    (wireScale_mono_coefficient
      (fixedPhysicalCoefficient_le_padding contracts outer requestedRate)
      logExponent
      ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)).trans
      (fixedPaddingPhysicalWireScale_le_raw contracts outer requestedRate
        sourceIndex logExponent)

end NearCubicWires.CaseOneRecoveryAssembly
