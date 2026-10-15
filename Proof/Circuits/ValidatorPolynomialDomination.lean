import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.Circuits.CanonicalForkCall
import Proof.Circuits.CanonicalRoundCall
import Proof.Amplification.RecoveryLimitsComputableFamily
import Proof.Amplification.RecoveryVerifierResourceEnvelope

namespace NearCubicWires.ValidatorPolynomialDomination

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 One uniform domination judgement -/

/-- **The domination judgement.**  `PolyBounded value measure coefficient
degree` says the charge `value` is dominated by the polynomial budget of
`coefficient` and `degree` at `measure`.  It is definitionally the machine's
own `polynomialBudget` inequality, so nothing is lost transporting a spine
fact into a premise of `ExecutableRecoveryMachine`. -/
def PolyBounded (value measure coefficient degree : ℕ) : Prop :=
  value ≤ coefficient * (measure + 1) ^ degree

theorem polyBounded_iff_polynomialBudget
    (value measure coefficient degree : ℕ) :
    PolyBounded value measure coefficient degree ↔
      value ≤ polynomialBudget coefficient degree measure :=
  Iff.rfl

theorem PolyBounded.le_polynomialBudget
    {value measure coefficient degree : ℕ}
    (h : PolyBounded value measure coefficient degree) :
    value ≤ polynomialBudget coefficient degree measure := h

private theorem one_le_measure_pow (measure degree : ℕ) :
    1 ≤ (measure + 1) ^ degree :=
  Nat.one_le_pow _ _ (by omega)

/-- A closed charge is dominated by its own value at every degree: this is the
rule every program-shape overhead in the cone uses. -/
theorem PolyBounded.of_le_coefficient
    {value measure coefficient degree : ℕ} (h : value ≤ coefficient) :
    PolyBounded value measure coefficient degree := by
  refine h.trans ?_
  calc
    coefficient = coefficient * 1 := (Nat.mul_one _).symm
    _ ≤ coefficient * (measure + 1) ^ degree :=
      Nat.mul_le_mul_left _ (one_le_measure_pow measure degree)

theorem polyBounded_const (coefficient measure degree : ℕ) :
    PolyBounded coefficient measure coefficient degree :=
  PolyBounded.of_le_coefficient le_rfl

/-- Weakening on the *charge*: the only rule that consumes an exact fuel
identity. -/
theorem PolyBounded.mono
    {value value' measure coefficient degree : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : value' ≤ value) :
    PolyBounded value' measure coefficient degree := hle.trans h

theorem PolyBounded.coefficient_mono
    {value measure coefficient coefficient' degree : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : coefficient ≤ coefficient') :
    PolyBounded value measure coefficient' degree :=
  h.trans (Nat.mul_le_mul_right _ hle)

theorem PolyBounded.degree_mono
    {value measure coefficient degree degree' : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : degree ≤ degree') :
    PolyBounded value measure coefficient degree' :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hle))

theorem PolyBounded.measure_mono
    {value measure measure' coefficient degree : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : measure ≤ measure') :
    PolyBounded value measure' coefficient degree :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) degree))

/-- Additive composition: sequential charges keep the degree and add the
coefficients. -/
theorem PolyBounded.add
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded left measure leftCoefficient degree)
    (hright : PolyBounded right measure rightCoefficient degree) :
    PolyBounded (left + right) measure
      (leftCoefficient + rightCoefficient) degree := by
  unfold PolyBounded at hleft hright ⊢
  rw [Nat.add_mul]
  omega

/-- Width composition: parallel charges keep the degree and take the larger
coefficient. -/
theorem PolyBounded.max
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded left measure leftCoefficient degree)
    (hright : PolyBounded right measure rightCoefficient degree) :
    PolyBounded (max left right) measure
      (max leftCoefficient rightCoefficient) degree := by
  refine Nat.max_le.2 ⟨hleft.coefficient_mono (le_max_left _ _),
    hright.coefficient_mono (le_max_right _ _)⟩

/-- **The only degree-raising rule.**  A charge repeated once per element of a
counted collection multiplies the two coefficients and *adds* the two degrees.
Every multiplication in the cone is of this shape — a count, a width, an arity
or an index against a per-element charge — never a decoded magnitude. -/
theorem PolyBounded.mul
    {left right measure leftCoefficient rightCoefficient
      leftDegree rightDegree : ℕ}
    (hleft : PolyBounded left measure leftCoefficient leftDegree)
    (hright : PolyBounded right measure rightCoefficient rightDegree) :
    PolyBounded (left * right) measure
      (leftCoefficient * rightCoefficient) (leftDegree + rightDegree) := by
  unfold PolyBounded at hleft hright ⊢
  calc
    left * right ≤
        (leftCoefficient * (measure + 1) ^ leftDegree) *
          (rightCoefficient * (measure + 1) ^ rightDegree) :=
      Nat.mul_le_mul hleft hright
    _ = leftCoefficient * rightCoefficient *
        (measure + 1) ^ (leftDegree + rightDegree) := by
      rw [Nat.pow_add]
      ring

theorem polyBounded_measure_succ (measure degree : ℕ) :
    PolyBounded (measure + 1) measure 1 (degree + 1) := by
  unfold PolyBounded
  calc
    measure + 1 = (measure + 1) ^ 1 := (Nat.pow_one _).symm
    _ ≤ (measure + 1) ^ (degree + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    _ = 1 * (measure + 1) ^ (degree + 1) := (Nat.one_mul _).symm

theorem polyBounded_measure (measure degree : ℕ) :
    PolyBounded measure measure 1 (degree + 1) :=
  (polyBounded_measure_succ measure degree).mono (by omega)

/-- The pointwise judgement, packaged over a request type.  This is the shape
the machine's premises are stated in. -/
def FuelPolyDominated {Request : Type} (fuel measureOf : Request → ℕ)
    (coefficient degree : ℕ) : Prop :=
  ∀ request : Request,
    PolyBounded (fuel request) (measureOf request) coefficient degree

theorem FuelPolyDominated.le_polynomialBudget
    {Request : Type} {fuel measureOf : Request → ℕ}
    {coefficient degree : ℕ}
    (h : FuelPolyDominated fuel measureOf coefficient degree)
    (request : Request) :
    fuel request ≤ polynomialBudget coefficient degree (measureOf request) :=
  h request

/-! ## §2 The linker and call-combinator algebra

Every composite fuel definition in the validator's cone is one of the eight
shapes below.  Each is discharged once, from §1, so a spine walk never has to
re-derive a linker charge. -/

/-- Sequential composition: the second program's register span is a closed
program-shape overhead, so linking is degree-preserving. -/
theorem linkFuel_polyBounded
    {second : NPOracleProgram}
    {firstFuel secondFuel measure firstCoefficient secondCoefficient
      degree : ℕ}
    (hfirst : PolyBounded firstFuel measure firstCoefficient degree)
    (hsecond : PolyBounded secondFuel measure secondCoefficient degree) :
    PolyBounded (linkFuel second firstFuel secondFuel) measure
      (programRegisterSpan second + 5 + firstCoefficient + secondCoefficient)
      degree := by
  have hoverhead :
      PolyBounded (programRegisterSpan second + 5) measure
        (programRegisterSpan second + 5) degree :=
    polyBounded_const _ _ _
  refine ((hoverhead.add hfirst).add hsecond).mono ?_
  simp only [linkFuel]
  omega

theorem preserveRightFuel_polyBounded
    {sourceFuel measure coefficient degree : ℕ}
    (hsource : PolyBounded sourceFuel measure coefficient degree) :
    PolyBounded (preserveRightFuel sourceFuel) measure
      (coefficient + 4) degree := by
  refine (hsource.add (polyBounded_const 4 measure degree)).mono ?_
  simp only [preserveRightFuel, le_refl]

theorem taggedProgramChoiceFuel_polyBounded
    {sourceFuel measure coefficient degree : ℕ}
    (hsource : PolyBounded sourceFuel measure coefficient degree) :
    PolyBounded (taggedProgramChoiceFuel sourceFuel) measure
      (coefficient + 5) degree := by
  refine (hsource.add (polyBounded_const 5 measure degree)).mono ?_
  simp only [taggedProgramChoiceFuel, le_refl]

/-- Closed program-shape overhead of one paired call. -/
def pairedCallOverhead (source : NPOracleProgram) : ℕ :=
  programRegisterSpan swapPairProgram + 5 +
    (programRegisterSpan (preserveRightProgram source) + 5 +
      (programRegisterSpan swapPairProgram + 5 + 4 + 4) + 4) + 4

theorem pairedCallFuel_polyBounded
    {source : NPOracleProgram}
    {leftFuel rightFuel measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded leftFuel measure leftCoefficient degree)
    (hright : PolyBounded rightFuel measure rightCoefficient degree) :
    PolyBounded (pairedCallFuel source leftFuel rightFuel) measure
      (pairedCallOverhead source + leftCoefficient + rightCoefficient)
      degree := by
  have hinner :=
    linkFuel_polyBounded (second := swapPairProgram)
      (preserveRightFuel_polyBounded hleft) (polyBounded_const 4 measure degree)
  have houter :=
    linkFuel_polyBounded (second := preserveRightProgram source) hinner
      (preserveRightFuel_polyBounded hright)
  have htop :=
    linkFuel_polyBounded (second := swapPairProgram) houter
      (polyBounded_const 4 measure degree)
  refine htop.coefficient_mono ?_
  simp only [pairedCallOverhead]
  omega

/-- Closed program-shape overhead of one fork call. -/
def forkCallOverhead (first second : NPOracleProgram) : ℕ :=
  programRegisterSpan (pairedCallProgram (taggedProgramChoice first second)) +
      5 + 6 +
    (pairedCallOverhead (taggedProgramChoice first second) + 5 + 5)

theorem forkCallFuel_polyBounded
    {first second : NPOracleProgram}
    {firstFuel secondFuel measure firstCoefficient secondCoefficient
      degree : ℕ}
    (hfirst : PolyBounded firstFuel measure firstCoefficient degree)
    (hsecond : PolyBounded secondFuel measure secondCoefficient degree) :
    PolyBounded (forkCallFuel first second firstFuel secondFuel) measure
      (forkCallOverhead first second + firstCoefficient + secondCoefficient)
      degree := by
  have hpaired :=
    pairedCallFuel_polyBounded (source := taggedProgramChoice first second)
      (taggedProgramChoiceFuel_polyBounded hfirst)
      (taggedProgramChoiceFuel_polyBounded hsecond)
  have htop :=
    linkFuel_polyBounded
      (second := pairedCallProgram (taggedProgramChoice first second))
      (polyBounded_const 6 measure degree) hpaired
  refine htop.coefficient_mono ?_
  simp only [forkCallOverhead]
  omega

theorem balancedCallFuel_le
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (requests : List ℕ) (bound : ℕ)
    (hbound : ∀ request ∈ requests, calleeFuel request ≤ bound) :
    balancedCallFuel callee calleeFuel requests ≤
      37 + requests.length *
        ((balancedCallLayout callee).calleeSpan + 73 + bound) := by
  have hstructural :=
    balancedTraversalStructuralSteps_le_linear requests
  have hleaves :
      (requests.map fun request =>
          balancedCallLeafBudget callee (calleeFuel request)).sum ≤
        requests.length *
          ((balancedCallLayout callee).calleeSpan + 3 + bound) := by
    have hpointwise :
        ∀ value ∈ requests.map fun request =>
            balancedCallLeafBudget callee (calleeFuel request),
          value ≤ (balancedCallLayout callee).calleeSpan + 3 + bound := by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨request, hrequest, rfl⟩ := hvalue
      have := hbound request hrequest
      simp only [balancedCallLeafBudget]
      omega
    have hsum :=
      List.sum_le_card_nsmul _ _ hpointwise
    simpa [smul_eq_mul, Nat.mul_comm] using hsum
  have hexpand :
      requests.length *
          ((balancedCallLayout callee).calleeSpan + 73 + bound) =
        requests.length *
            ((balancedCallLayout callee).calleeSpan + 3 + bound) +
          70 * requests.length := by
    rw [Nat.mul_comm 70 requests.length, ← Nat.mul_add]
    ring
  simp only [balancedCallFuel]
  omega

theorem balancedCallFuel_polyBounded
    {callee : NPOracleProgram} {calleeFuel : ℕ → ℕ}
    {requests : List ℕ} {bound measure countCoefficient calleeCoefficient
      countDegree calleeDegree : ℕ}
    (hcount : PolyBounded requests.length measure countCoefficient countDegree)
    (hcallee : PolyBounded bound measure calleeCoefficient calleeDegree)
    (hbound : ∀ request ∈ requests, calleeFuel request ≤ bound) :
    PolyBounded (balancedCallFuel callee calleeFuel requests) measure
      (37 + countCoefficient *
        ((balancedCallLayout callee).calleeSpan + 73 + calleeCoefficient))
      (countDegree + calleeDegree) := by
  have hleaf :
      PolyBounded ((balancedCallLayout callee).calleeSpan + 73 + bound)
        measure
        ((balancedCallLayout callee).calleeSpan + 73 + calleeCoefficient)
        calleeDegree :=
    (polyBounded_const ((balancedCallLayout callee).calleeSpan + 73) measure
      calleeDegree).add hcallee
  have hproduct := hcount.mul hleaf
  have htotal :=
    (polyBounded_const 37 measure (countDegree + calleeDegree)).add
      (hproduct.degree_mono (le_refl (countDegree + calleeDegree)))
  exact htotal.mono (balancedCallFuel_le callee calleeFuel requests bound hbound)

/-- Closed program-shape overhead of one balanced validation map. -/
def balancedValidationMapOverhead (callee : NPOracleProgram) : ℕ :=
  programRegisterSpan
      (linkPrograms (preserveRightProgram nativeInputRequestTreeProgram)
        (preserveRightProgram (balancedCallProgram callee))) + 5 +
    (programRegisterSpan (preserveRightProgram (balancedCallProgram callee)) +
      5 + 4 + 4)

theorem balancedValidationMapFuel_polyBounded
    {callee : NPOracleProgram} {calleeFuel : ℕ → ℕ}
    {inputLength raw measure guardCoefficient treeCoefficient
      callCoefficient degree : ℕ}
    (hguard :
      PolyBounded (balancedValidationMapGuardFuel raw) measure
        guardCoefficient degree)
    (htree :
      PolyBounded
        (nativeInputRequestTreeFuel (balancedValidationMapCodes raw)) measure
        treeCoefficient degree)
    (hcall :
      PolyBounded
        (balancedCallFuel callee calleeFuel
          (balancedValidationMapRequests inputLength raw)) measure
        callCoefficient degree) :
    PolyBounded (balancedValidationMapFuel callee calleeFuel inputLength raw)
      measure
      (balancedValidationMapOverhead callee + guardCoefficient +
        treeCoefficient + callCoefficient) degree := by
  have hinner :=
    linkFuel_polyBounded
      (second := preserveRightProgram (balancedCallProgram callee))
      (preserveRightFuel_polyBounded htree)
      (preserveRightFuel_polyBounded hcall)
  have houter :=
    linkFuel_polyBounded
      (second :=
        linkPrograms (preserveRightProgram nativeInputRequestTreeProgram)
          (preserveRightProgram (balancedCallProgram callee)))
      hguard hinner
  refine houter.coefficient_mono ?_
  simp only [balancedValidationMapOverhead]
  omega

/-- Exact linear ledger of one counted round call against a uniform per-round
bound. -/
theorem roundCallLoopFuel_le
    (callee : NPOracleProgram) (calleeFuel step : ℕ → ℕ → ℕ)
    (bound : ℕ) (rounds : ℕ)
    (hbound : ∀ carried counter, calleeFuel carried counter ≤ bound)
    (initialState : ℕ) :
    roundCallLoopFuel callee calleeFuel step initialState rounds ≤
      1 + rounds * (programRegisterSpan callee + bound + 6) := by
  induction rounds generalizing initialState with
  | zero => simp [roundCallLoopFuel]
  | succ count inductionHypothesis =>
      have htail :=
        inductionHypothesis (step initialState (count + 1))
      have hhead := hbound initialState (count + 1)
      rw [roundCallLoopFuel_succ]
      have hexpand :
          (count + 1) * (programRegisterSpan callee + bound + 6) =
            count * (programRegisterSpan callee + bound + 6) +
              (programRegisterSpan callee + bound + 6) := by
        ring
      omega

theorem roundCallFuel_polyBounded
    {callee : NPOracleProgram} {calleeFuel step : ℕ → ℕ → ℕ}
    {initialState rounds bound measure roundCoefficient calleeCoefficient
      roundDegree calleeDegree : ℕ}
    (hrounds : PolyBounded rounds measure roundCoefficient roundDegree)
    (hcallee : PolyBounded bound measure calleeCoefficient calleeDegree)
    (hbound : ∀ carried counter, calleeFuel carried counter ≤ bound) :
    PolyBounded (roundCallFuel callee calleeFuel step initialState rounds)
      measure
      (4 + roundCoefficient *
        (programRegisterSpan callee + calleeCoefficient + 6))
      (roundDegree + calleeDegree) := by
  have hround :
      PolyBounded (programRegisterSpan callee + bound + 6) measure
        (programRegisterSpan callee + calleeCoefficient + 6) calleeDegree := by
    have hsum :=
      (polyBounded_const (programRegisterSpan callee) measure
        calleeDegree).add hcallee
    have := hsum.add (polyBounded_const 6 measure calleeDegree)
    exact this.mono (by omega)
  have hproduct := hrounds.mul hround
  have htotal :=
    (polyBounded_const 4 measure (roundDegree + calleeDegree)).add hproduct
  refine htotal.mono ?_
  have hloop :=
    roundCallLoopFuel_le callee calleeFuel step bound rounds hbound
      initialState
  simp only [roundCallFuel]
  omega

/-- Scaling by a closed repetition count keeps the degree. -/
theorem PolyBounded.const_mul
    {value measure coefficient degree : ℕ} (factor : ℕ)
    (h : PolyBounded value measure coefficient degree) :
    PolyBounded (factor * value) measure (factor * coefficient) degree := by
  unfold PolyBounded at h ⊢
  calc
    factor * value ≤ factor * (coefficient * (measure + 1) ^ degree) :=
      Nat.mul_le_mul_left _ h
    _ = factor * coefficient * (measure + 1) ^ degree := by ring

def recoveryValidatorMaximumStageFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max recoveryValidatorStructuralPrefixFuel <|
    max (recoveryOracleValidationFuel
      (recoveryValidatorStructuralPrefixOutput limits raw)) <|
      max (recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))
        recoveryValidatorModeRawFuel

def recoveryValidatorMaximumStageBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorStructuralPrefixBits inputLength limits raw) <|
      max (recoveryOracleValidationBits inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw)) <|
        max (recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw))
          (recoveryValidatorModeRawBits inputLength
            (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))

/-- Every arithmetic fact about the spine coefficient is proved at the level of
*variables* and then instantiated.  The three register spans are closed natural
numbers over the whole linked validator program, so any goal that mentions them
and could be closed by reflexivity would be evaluated by the kernel; the
composed coefficient is therefore never unfolded, reassociated or compared. -/
private theorem le_spineCoefficient
    (modeRawSpan envelopeSpan oracleSpan coefficient : ℕ) :
    coefficient ≤
      modeRawSpan + 5 +
        (envelopeSpan + 5 + (oracleSpan + 5 + coefficient + coefficient) +
          coefficient) + coefficient := by
  omega

/-- **Fuel side of the spine, dominated.**  Three applications of
`linkFuel_polyBounded`: a polynomial envelope for the validator's largest stage
charge is a polynomial envelope for the validator, at the same degree. -/
theorem recoveryWitnessValidatorFuel_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure stageCoefficient degree : ℕ}
    (hstage :
      PolyBounded (recoveryValidatorMaximumStageFuel inputLength limits raw)
        measure stageCoefficient degree) :
    PolyBounded (recoveryWitnessValidatorFuel inputLength limits raw) measure
      (programRegisterSpan recoveryValidatorModeRawProgram + 5 +
        (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationProgram + 5 +
            stageCoefficient + stageCoefficient) +
          stageCoefficient) +
        stageCoefficient) degree := by
  have hstructural :
      PolyBounded recoveryValidatorStructuralPrefixFuel measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageFuel]
    exact le_max_left _ _
  have horacle :
      PolyBounded (recoveryOracleValidationFuel
        (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageFuel]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have henvelope :
      PolyBounded (recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)) measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageFuel]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmodeRaw :
      PolyBounded recoveryValidatorModeRawFuel measure stageCoefficient
        degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageFuel]
    exact
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have horaclePrefix :
      PolyBounded (recoveryValidatorOraclePrefixFuel limits raw) measure
        (programRegisterSpan recoveryOracleValidationProgram + 5 +
          stageCoefficient + stageCoefficient) degree := by
    rw [recoveryValidatorOraclePrefixFuel]
    exact linkFuel_polyBounded hstructural horacle
  have hlegalSumPrefix :
      PolyBounded (recoveryValidatorLegalSumPrefixFuel inputLength limits raw)
        measure
        (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationProgram + 5 +
            stageCoefficient + stageCoefficient) + stageCoefficient)
        degree := by
    rw [recoveryValidatorLegalSumPrefixFuel]
    exact linkFuel_polyBounded horaclePrefix henvelope
  rw [recoveryWitnessValidatorFuel]
  exact linkFuel_polyBounded hlegalSumPrefix hmodeRaw

/-- **The fuel ledger.**  The whole validator costs the closed spine overhead
plus four copies of its largest stage charge, in exactly the association the
three `linkFuel` nodes produce — the degree-zero instance of the domination
statement above. -/
theorem recoveryWitnessValidatorFuel_le_maximumStage
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorFuel inputLength limits raw ≤
      programRegisterSpan recoveryValidatorModeRawProgram + 5 +
        (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationProgram + 5 +
            recoveryValidatorMaximumStageFuel inputLength limits raw +
            recoveryValidatorMaximumStageFuel inputLength limits raw) +
          recoveryValidatorMaximumStageFuel inputLength limits raw) +
        recoveryValidatorMaximumStageFuel inputLength limits raw := by
  have hstage :
      PolyBounded (recoveryValidatorMaximumStageFuel inputLength limits raw) 0
        (recoveryValidatorMaximumStageFuel inputLength limits raw) 0 :=
    polyBounded_const _ _ _
  have hbound := recoveryWitnessValidatorFuel_polyBounded hstage
  unfold PolyBounded at hbound
  rw [pow_zero, Nat.mul_one] at hbound
  exact hbound

/-- **The width ledger.**  Register width is a pure maximum along the spine:
no linker widens a register beyond the widest stage it joins. -/
theorem recoveryWitnessValidatorBits_le_maximumStage
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorBits inputLength limits raw ≤
      recoveryValidatorMaximumStageBits inputLength limits raw := by
  have hlength :
      natBitLength inputLength ≤
        recoveryValidatorMaximumStageBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageBits]
    exact le_max_left _ _
  have hstructural :
      recoveryValidatorStructuralPrefixBits inputLength limits raw ≤
        recoveryValidatorMaximumStageBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageBits]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have horacle :
      recoveryOracleValidationBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw) ≤
        recoveryValidatorMaximumStageBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageBits]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have henvelope :
      recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw) ≤
        recoveryValidatorMaximumStageBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageBits]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hmodeRaw :
      recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
        recoveryValidatorMaximumStageBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageBits]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  rw [recoveryWitnessValidatorBits, recoveryValidatorLegalSumPrefixBits,
    recoveryValidatorOraclePrefixBits]
  exact max_le hlength (max_le (max_le hlength (max_le
    (max_le hlength (max_le hstructural horacle)) henvelope)) hmodeRaw)

/-- **Width side of the spine, dominated.** -/
theorem recoveryWitnessValidatorBits_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure stageCoefficient degree : ℕ}
    (hstage :
      PolyBounded (recoveryValidatorMaximumStageBits inputLength limits raw)
        measure stageCoefficient degree) :
    PolyBounded (recoveryWitnessValidatorBits inputLength limits raw) measure
      stageCoefficient degree :=
  hstage.mono
    (recoveryWitnessValidatorBits_le_maximumStage inputLength limits raw)

/-! ## §4 The width of the frozen limits record

The width ledger of §3 exposes exactly one ingredient that is not a charge of
an executable stage: the validator's structural prefix carries
`encodeRecoveryWitnessLimits limits` through its handoff, so its register width
is bounded only once the encoded policy record is.  This section closes that
for the computable limits family, whose every field is explicit arithmetic in
the frozen amplifier numerals, the copy bound and the arity. -/

/-- Binary width is subadditive under multiplication. -/
theorem natBitLength_mul_le (left right : ℕ) :
    natBitLength (left * right) ≤ natBitLength left + natBitLength right := by
  have hleftOne : 1 ≤ natBitLength left := by
    unfold natBitLength
    omega
  have hrightOne : 1 ≤ natBitLength right := by
    unfold natBitLength
    omega
  rcases Nat.eq_zero_or_pos (left * right) with hzero | hpositive
  · rw [hzero]
    have : natBitLength 0 = 1 := by
      simp [natBitLength]
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
        _ = 2 ^ (natBitLength left + natBitLength right) := (pow_add _ _ _).symm
    have hlog :=
      Nat.log_lt_of_lt_pow (b := 2) hpositive.ne' hproduct
    unfold natBitLength at hlog ⊢
    omega

/-- Binary width of a power is linear in the exponent. -/
theorem natBitLength_pow_le (base exponent : ℕ) :
    natBitLength (base ^ exponent) ≤ exponent * natBitLength base + 1 := by
  induction exponent with
  | zero => simp [natBitLength]
  | succ count inductionHypothesis =>
      have hstep := natBitLength_mul_le (base ^ count) base
      rw [pow_succ]
      have hexpand :
          (count + 1) * natBitLength base =
            count * natBitLength base + natBitLength base := by
        ring
      omega

/-! ### The serialized policy record -/

/-- Width certificate for one legal-sum policy: every numeric field, and both
components of the rational mass cap, fit in `parameter` bits. -/
structure LegalSumLimitsWidth (limits : LegalSumLimits) (parameter : ℕ) :
    Prop where
  expectedArity : natBitLength limits.expectedArity ≤ parameter
  termCap : natBitLength limits.termCap ≤ parameter
  coefficientBitCap : natBitLength limits.coefficientBitCap ≤ parameter
  massNumerator :
    natBitLength limits.coefficientMassCap.num.natAbs ≤ parameter
  massDenominator : natBitLength limits.coefficientMassCap.den ≤ parameter
  wireCap : natBitLength limits.wireCap ≤ parameter
  descriptionCap : natBitLength limits.descriptionCap ≤ parameter

/-- Width certificate for a complete recovery policy. -/
structure RecoveryWitnessLimitsWidth
    (limits : RecoveryWitnessLimits) (parameter : ℕ) : Prop where
  oracleArity : natBitLength limits.oracleArity ≤ parameter
  oracleSizeCap : natBitLength limits.oracleSizeCap ≤ parameter
  sumArity : natBitLength limits.sumArity ≤ parameter
  symmetric : LegalSumLimitsWidth limits.symmetric parameter
  threshold : LegalSumLimitsWidth limits.threshold parameter

/-- Five nested pairs of fields, each doubling the width. -/
theorem natBitLength_encodeLegalSumLimits_le
    (limits : LegalSumLimits) (fieldBound : ℕ)
    (harity : natBitLength limits.expectedArity ≤ fieldBound)
    (hterm : natBitLength limits.termCap ≤ fieldBound)
    (hcoefficientBit : natBitLength limits.coefficientBitCap ≤ fieldBound)
    (hmass :
      natBitLength (encodeCanonicalRational limits.coefficientMassCap) ≤
        fieldBound)
    (hwire : natBitLength limits.wireCap ≤ fieldBound)
    (hdescription : natBitLength limits.descriptionCap ≤ fieldBound) :
    natBitLength (encodeLegalSumLimits limits) ≤ 32 * fieldBound := by
  have hinner := pairCodeBits_le limits.wireCap limits.descriptionCap
  have hmassPair :=
    pairCodeBits_le (encodeCanonicalRational limits.coefficientMassCap)
      (Nat.pair limits.wireCap limits.descriptionCap)
  have hbitPair :=
    pairCodeBits_le limits.coefficientBitCap
      (Nat.pair (encodeCanonicalRational limits.coefficientMassCap)
        (Nat.pair limits.wireCap limits.descriptionCap))
  have htermPair :=
    pairCodeBits_le limits.termCap
      (Nat.pair limits.coefficientBitCap
        (Nat.pair (encodeCanonicalRational limits.coefficientMassCap)
          (Nat.pair limits.wireCap limits.descriptionCap)))
  have harityPair :=
    pairCodeBits_le limits.expectedArity
      (Nat.pair limits.termCap
        (Nat.pair limits.coefficientBitCap
          (Nat.pair (encodeCanonicalRational limits.coefficientMassCap)
            (Nat.pair limits.wireCap limits.descriptionCap))))
  simp only [encodeLegalSumLimits]
  omega

/-- Four nested pairs of fields, each doubling the width. -/
theorem natBitLength_encodeRecoveryWitnessLimits_le
    (limits : RecoveryWitnessLimits) (fieldBound : ℕ)
    (horacleArity : natBitLength limits.oracleArity ≤ fieldBound)
    (horacleSize : natBitLength limits.oracleSizeCap ≤ fieldBound)
    (hsumArity : natBitLength limits.sumArity ≤ fieldBound)
    (hsymmetric :
      natBitLength (encodeLegalSumLimits limits.symmetric) ≤ fieldBound)
    (hthreshold :
      natBitLength (encodeLegalSumLimits limits.threshold) ≤ fieldBound) :
    natBitLength (encodeRecoveryWitnessLimits limits) ≤ 16 * fieldBound := by
  have hbranches :=
    pairCodeBits_le (encodeLegalSumLimits limits.symmetric)
      (encodeLegalSumLimits limits.threshold)
  have hsumPair :=
    pairCodeBits_le limits.sumArity
      (Nat.pair (encodeLegalSumLimits limits.symmetric)
        (encodeLegalSumLimits limits.threshold))
  have hsizePair :=
    pairCodeBits_le limits.oracleSizeCap
      (Nat.pair limits.sumArity
        (Nat.pair (encodeLegalSumLimits limits.symmetric)
          (encodeLegalSumLimits limits.threshold)))
  have harityPair :=
    pairCodeBits_le limits.oracleArity
      (Nat.pair limits.oracleSizeCap
        (Nat.pair limits.sumArity
          (Nat.pair (encodeLegalSumLimits limits.symmetric)
            (encodeLegalSumLimits limits.threshold))))
  simp only [encodeRecoveryWitnessLimits]
  omega

/-- Uniform width of a serialized recovery policy whose fields all fit in
`parameter` bits. -/
def recoveryWitnessLimitsCodeBitBound (parameter : ℕ) : ℕ :=
  512 * max parameter (canonicalRationalCodeBitBound parameter)

/-- **The serialized policy width.**  A field-width certificate bounds the
whole encoded record. -/
theorem natBitLength_encodeRecoveryWitnessLimits_le_parameter
    {limits : RecoveryWitnessLimits} {parameter : ℕ}
    (hwidth : RecoveryWitnessLimitsWidth limits parameter) :
    natBitLength (encodeRecoveryWitnessLimits limits) ≤
      recoveryWitnessLimitsCodeBitBound parameter := by
  set fieldBound := max parameter (canonicalRationalCodeBitBound parameter)
    with hfieldBound
  have hparameter : parameter ≤ fieldBound := le_max_left _ _
  have hrational :
      canonicalRationalCodeBitBound parameter ≤ fieldBound := le_max_right _ _
  have hbranch :
      ∀ policy : LegalSumLimits, LegalSumLimitsWidth policy parameter →
        natBitLength (encodeLegalSumLimits policy) ≤ 32 * fieldBound := by
    intro policy hpolicy
    refine natBitLength_encodeLegalSumLimits_le policy fieldBound
      (hpolicy.expectedArity.trans hparameter)
      (hpolicy.termCap.trans hparameter)
      (hpolicy.coefficientBitCap.trans hparameter) ?_
      (hpolicy.wireCap.trans hparameter)
      (hpolicy.descriptionCap.trans hparameter)
    exact (encodeCanonicalRational_bits_le_parameter policy.coefficientMassCap
      parameter hpolicy.massNumerator hpolicy.massDenominator).trans hrational
  have hsymmetric := hbranch limits.symmetric hwidth.symmetric
  have hthreshold := hbranch limits.threshold hwidth.threshold
  have hrecord :=
    natBitLength_encodeRecoveryWitnessLimits_le limits (32 * fieldBound)
      (hwidth.oracleArity.trans (hparameter.trans (by omega)))
      (hwidth.oracleSizeCap.trans (hparameter.trans (by omega)))
      (hwidth.sumArity.trans (hparameter.trans (by omega)))
      hsymmetric hthreshold
  simp only [recoveryWitnessLimitsCodeBitBound, ← hfieldBound]
  omega

/-! ### The computable limits family

Every field of `computableXorRecoveryWitnessLimits` is explicit arithmetic in
the four frozen profile numerals, the copy bound and the arity, so the width
certificate above is available unconditionally. -/

/-- Explicit width parameter of the computable recovery policy: one summand per
field, each either a frozen numeral's width, a multiple of the copy bound, or
the width of an explicit polynomial in the arity and the wire cap. -/
def computableRecoveryWitnessLimitsWidthParameter
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ) : ℕ :=
  natBitLength oracleArity + natBitLength oracleSizeCap +
    natBitLength sumArity + natBitLength symmetricWireCap +
    natBitLength thresholdWireCap +
    natBitLength profile.termCoefficientCap +
    natBitLength profile.massCoefficientCap +
    natBitLength profile.coefficientBitCoefficient +
    5 * copyBound +
    profile.coefficientBitDegree * natBitLength (sumArity + 1) +
    natBitLength (symmetricDescriptionCap sumArity symmetricWireCap) +
    natBitLength (thresholdDescriptionCap sumArity thresholdWireCap) + 2

private theorem computableTermCap_width
    (profile : XorNumeralProfile) (copyBound arity : ℕ) :
    natBitLength (computableTermCap profile copyBound arity) ≤
      natBitLength profile.termCoefficientCap + natBitLength arity +
        5 * copyBound + 1 := by
  have hpower : natBitLength ((16 : ℕ) ^ copyBound) ≤ 5 * copyBound + 1 := by
    have hbound := natBitLength_pow_le 16 copyBound
    have hlog : Nat.log 2 16 = 4 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    have hsixteen : natBitLength 16 = 5 := by
      simp only [natBitLength, hlog]
    rw [hsixteen] at hbound
    omega
  have houter :=
    natBitLength_mul_le (profile.termCoefficientCap * arity)
      ((16 : ℕ) ^ copyBound)
  have hinner := natBitLength_mul_le profile.termCoefficientCap arity
  simp only [computableTermCap]
  omega

private theorem computableCoefficientBitCap_width
    (profile : XorNumeralProfile) (arity : ℕ) :
    natBitLength (computableCoefficientBitCap profile arity) ≤
      natBitLength profile.coefficientBitCoefficient +
        profile.coefficientBitDegree * natBitLength (arity + 1) + 1 := by
  have hpower :=
    natBitLength_pow_le (arity + 1) profile.coefficientBitDegree
  have houter :=
    natBitLength_mul_le profile.coefficientBitCoefficient
      ((arity + 1) ^ profile.coefficientBitDegree)
  simp only [computableCoefficientBitCap]
  omega

private theorem computableMassCap_numerator
    (profile : XorNumeralProfile) (copyBound : ℕ) :
    (computableMassCap profile copyBound).num.natAbs =
      profile.massCoefficientCap * 4 ^ copyBound := by
  rw [computableMassCap, Rat.num_natCast]
  exact Int.natAbs_natCast _

private theorem computableMassCap_denominator
    (profile : XorNumeralProfile) (copyBound : ℕ) :
    (computableMassCap profile copyBound).den = 1 := by
  rw [computableMassCap]
  exact Rat.den_natCast _

private theorem computableMassCap_width
    (profile : XorNumeralProfile) (copyBound : ℕ) :
    natBitLength (computableMassCap profile copyBound).num.natAbs ≤
      natBitLength profile.massCoefficientCap + 3 * copyBound + 1 := by
  have hpower : natBitLength ((4 : ℕ) ^ copyBound) ≤ 3 * copyBound + 1 := by
    have hbound := natBitLength_pow_le 4 copyBound
    have hlog : Nat.log 2 4 = 2 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    have hfour : natBitLength 4 = 3 := by
      simp only [natBitLength, hlog]
    rw [hfour] at hbound
    omega
  have hproduct :=
    natBitLength_mul_le profile.massCoefficientCap ((4 : ℕ) ^ copyBound)
  rw [computableMassCap_numerator]
  omega

private theorem computableMassCap_denominator_width
    (profile : XorNumeralProfile) (copyBound parameter : ℕ)
    (hparameter : 1 ≤ parameter) :
    natBitLength (computableMassCap profile copyBound).den ≤ parameter := by
  rw [computableMassCap_denominator]
  have hlog : Nat.log 2 1 = 0 := Nat.log_one_right 2
  simp only [natBitLength, hlog]
  omega

private theorem computableSymmetricLegalSumLimits_width
    (profile : XorNumeralProfile) (copyBound arity wireCap parameter : ℕ)
    (harity : natBitLength arity ≤ parameter)
    (hterm :
      natBitLength (computableTermCap profile copyBound arity) ≤ parameter)
    (hcoefficient :
      natBitLength (computableCoefficientBitCap profile arity) ≤ parameter)
    (hmass :
      natBitLength (computableMassCap profile copyBound).num.natAbs ≤
        parameter)
    (hwire : natBitLength wireCap ≤ parameter)
    (hdescription :
      natBitLength (symmetricDescriptionCap arity wireCap) ≤ parameter)
    (hpositive : 1 ≤ parameter) :
    LegalSumLimitsWidth
      (computableSymmetricLegalSumLimits profile copyBound arity wireCap)
      parameter :=
  { expectedArity := harity
    termCap := hterm
    coefficientBitCap := hcoefficient
    massNumerator := hmass
    massDenominator :=
      computableMassCap_denominator_width profile copyBound parameter hpositive
    wireCap := hwire
    descriptionCap := hdescription }

private theorem computableThresholdLegalSumLimits_width
    (profile : XorNumeralProfile) (copyBound arity wireCap parameter : ℕ)
    (harity : natBitLength arity ≤ parameter)
    (hterm :
      natBitLength (computableTermCap profile copyBound arity) ≤ parameter)
    (hcoefficient :
      natBitLength (computableCoefficientBitCap profile arity) ≤ parameter)
    (hmass :
      natBitLength (computableMassCap profile copyBound).num.natAbs ≤
        parameter)
    (hwire : natBitLength wireCap ≤ parameter)
    (hdescription :
      natBitLength (thresholdDescriptionCap arity wireCap) ≤ parameter)
    (hpositive : 1 ≤ parameter) :
    LegalSumLimitsWidth
      (computableThresholdLegalSumLimits profile copyBound arity wireCap)
      parameter :=
  { expectedArity := harity
    termCap := hterm
    coefficientBitCap := hcoefficient
    massNumerator := hmass
    massDenominator :=
      computableMassCap_denominator_width profile copyBound parameter hpositive
    wireCap := hwire
    descriptionCap := hdescription }

/-- **The computable policy's width certificate.**  Unconditional: no schedule
hypothesis is consumed, only the arithmetic shape of the family. -/
theorem computableXorRecoveryWitnessLimits_width
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ) :
    RecoveryWitnessLimitsWidth
      (computableXorRecoveryWitnessLimits profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap)
      (computableRecoveryWitnessLimitsWidthParameter profile copyBound
        oracleArity oracleSizeCap sumArity symmetricWireCap
        thresholdWireCap) := by
  set parameter :=
    computableRecoveryWitnessLimitsWidthParameter profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap
    with hparameter
  have hterm := computableTermCap_width profile copyBound sumArity
  have hcoefficient := computableCoefficientBitCap_width profile sumArity
  have hmass := computableMassCap_width profile copyBound
  have hexpand :
      parameter =
        natBitLength oracleArity + natBitLength oracleSizeCap +
          natBitLength sumArity + natBitLength symmetricWireCap +
          natBitLength thresholdWireCap +
          natBitLength profile.termCoefficientCap +
          natBitLength profile.massCoefficientCap +
          natBitLength profile.coefficientBitCoefficient +
          5 * copyBound +
          profile.coefficientBitDegree * natBitLength (sumArity + 1) +
          natBitLength (symmetricDescriptionCap sumArity symmetricWireCap) +
          natBitLength (thresholdDescriptionCap sumArity thresholdWireCap) +
          2 := by
    rw [hparameter, computableRecoveryWitnessLimitsWidthParameter]
  have hpositive : 1 ≤ parameter := by omega
  have hsymmetricDescription :
      natBitLength (symmetricDescriptionCap sumArity symmetricWireCap) ≤
        parameter := by omega
  have hthresholdDescription :
      natBitLength (thresholdDescriptionCap sumArity thresholdWireCap) ≤
        parameter := by omega
  exact
    { oracleArity := by
        change natBitLength oracleArity ≤ parameter
        omega
      oracleSizeCap := by
        change natBitLength oracleSizeCap ≤ parameter
        omega
      sumArity := by
        change natBitLength sumArity ≤ parameter
        omega
      symmetric :=
        computableSymmetricLegalSumLimits_width profile copyBound sumArity
          symmetricWireCap parameter (by omega) (by omega) (by omega)
          (by omega) (by omega) hsymmetricDescription hpositive
      threshold :=
        computableThresholdLegalSumLimits_width profile copyBound sumArity
          thresholdWireCap parameter (by omega) (by omega) (by omega)
          (by omega) (by omega) hthresholdDescription hpositive }

/-- **The computable policy's serialized width.**  Measure-polynomial as soon
as the arity, the wire caps and the copy bound are: every summand of the width
parameter is a frozen numeral's width, a multiple of the copy bound, or the
width of an explicit polynomial in the arity and the wire cap. -/
theorem natBitLength_encodeComputableXorRecoveryWitnessLimits_le
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ) :
    natBitLength (encodeRecoveryWitnessLimits
        (computableXorRecoveryWitnessLimits profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap)) ≤
      recoveryWitnessLimitsCodeBitBound
        (computableRecoveryWitnessLimitsWidthParameter profile copyBound
          oracleArity oracleSizeCap sumArity symmetricWireCap
          thresholdWireCap) :=
  natBitLength_encodeRecoveryWitnessLimits_le_parameter
    (computableXorRecoveryWitnessLimits_width profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap)

theorem hvalidatorFuel_of_stageFuel
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageFuel (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget
        (programRegisterSpan recoveryValidatorModeRawProgram + 5 +
          (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
            (programRegisterSpan recoveryOracleValidationProgram + 5 +
              stageCoefficient + stageCoefficient) +
            stageCoefficient) +
          stageCoefficient)
        recoveryVerifierDegree request.measure :=
  ((recoveryWitnessValidatorFuel_polyBounded
    (hstage request)).degree_mono hdegree).le_polynomialBudget

theorem hvalidatorBits_of_stageBits
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageBits (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget stageCoefficient recoveryVerifierDegree
        request.measure :=
  ((recoveryWitnessValidatorBits_polyBounded
    (hstage request)).degree_mono hdegree).le_polynomialBudget

/-- Both premises at one coefficient, in exactly the shape
`RecoveryVerifierResourceEnvelope.executableRecoveryMachineOfComponents`
consumes. -/
theorem hvalidator_of_stageFrontier
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hfuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageFuel (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (hbits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageBits (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness))
        request.measure stageCoefficient degree) :
    (∀ request : WeakVerifierRequest,
      recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
        polynomialBudget
          (programRegisterSpan recoveryValidatorModeRawProgram + 5 +
            (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
              (programRegisterSpan recoveryOracleValidationProgram + 5 +
                stageCoefficient + stageCoefficient) +
              stageCoefficient) +
            stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
            (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
          polynomialBudget
            (programRegisterSpan recoveryValidatorModeRawProgram + 5 +
              (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
                (programRegisterSpan recoveryOracleValidationProgram + 5 +
                  stageCoefficient + stageCoefficient) +
                stageCoefficient) +
              stageCoefficient)
            recoveryVerifierDegree request.measure := by
  refine ⟨fun request => ?_, fun request => ?_⟩
  · refine (hvalidatorBits_of_stageBits limitsOf stageCoefficient degree
      hdegree hbits request).trans ?_
    exact Nat.mul_le_mul_right _ (le_spineCoefficient _ _ _ _)
  · exact hvalidatorFuel_of_stageFuel limitsOf stageCoefficient degree hdegree
      hfuel request

end NearCubicWires.ValidatorPolynomialDomination
