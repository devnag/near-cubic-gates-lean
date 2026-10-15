import Proof.Circuits.ValidatorStageEnvelopes

namespace NearCubicWires.ValidatorLegalSumWalk

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The nine-node chain, named

`recoveryLegalSumEnvelopeFuel` links ten sub-stage charges through nine
`linkFuel` nodes.  The `n`-th node's second program is the tail of the chain
below it, so the nine tails are one another's suffixes; naming them once keeps
the chain coefficient readable and, more importantly, lets the chain lemma be
instantiated at *explicitly supplied* program arguments, so no metavariable is
ever solved by unfolding a composed `programRegisterSpan`. -/

/-- The ninth (innermost) linked tail. -/
def legalSumChainTail₉ : NPOracleProgram :=
  recoveryLegalSumResourceTailProgram

/-- The eighth linked tail. -/
def legalSumChainTail₈ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassProgram legalSumChainTail₉

/-- The seventh linked tail. -/
def legalSumChainTail₇ : NPOracleProgram :=
  linkPrograms recoveryLegalTermBitCapStageProgram legalSumChainTail₈

/-- The sixth linked tail. -/
def legalSumChainTail₆ : NPOracleProgram :=
  linkPrograms recoveryLegalTermBitCapLoweringProgram legalSumChainTail₇

/-- The fifth linked tail. -/
def legalSumChainTail₅ : NPOracleProgram :=
  linkPrograms recoveryLegalTermCircuitStageProgram legalSumChainTail₆

/-- The fourth linked tail. -/
def legalSumChainTail₄ : NPOracleProgram :=
  linkPrograms recoveryLegalTermCircuitLoweringProgram legalSumChainTail₅

/-- The third linked tail. -/
def legalSumChainTail₃ : NPOracleProgram :=
  linkPrograms recoveryLegalTermCoefficientStageProgram legalSumChainTail₄

/-- The second linked tail. -/
def legalSumChainTail₂ : NPOracleProgram :=
  linkPrograms recoveryLegalTermCoefficientLoweringProgram legalSumChainTail₃

/-- The first (outermost) linked tail: everything the syntax stage hands on
to. -/
def legalSumChainTail₁ : NPOracleProgram :=
  linkPrograms recoveryLegalSumBoundStageProgram legalSumChainTail₂

/-- The chain's own program is the syntax stage linked to the first tail. -/
theorem recoveryLegalSumEnvelopeProgram_eq :
    recoveryLegalSumEnvelopeProgram =
      linkPrograms recoveryLegalSumSyntaxProgram legalSumChainTail₁ := rfl

/-- **The coefficient the nine-node chain produces** from a uniform sub-stage
coefficient.  Nine closed program-shape overheads and ten copies of the stage
coefficient; the expression is never evaluated. -/
def legalSumEnvelopeChainCoefficient (stage : ℕ) : ℕ :=
  legalSumEnvelopeCoefficient (programRegisterSpan legalSumChainTail₁)
    (programRegisterSpan legalSumChainTail₂)
    (programRegisterSpan legalSumChainTail₃)
    (programRegisterSpan legalSumChainTail₄)
    (programRegisterSpan legalSumChainTail₅)
    (programRegisterSpan legalSumChainTail₆)
    (programRegisterSpan legalSumChainTail₇)
    (programRegisterSpan legalSumChainTail₈)
    (programRegisterSpan legalSumChainTail₉) stage

/-- The bit-cap stage's argument: the circuit stage's output. -/
def legalSumBitCapStageInput (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalTermCircuitStageOutput inputLength handoff

/-- The mass stage's argument: the bit-cap stage's output. -/
def legalSumMassStageInput (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalTermBitCapStageOutput (legalSumBitCapStageInput inputLength handoff)

/-- **The legal-sum envelope's fuel, dominated.**  A uniform envelope for the
ten sub-stage charges is an envelope for the whole nine-node chain, at the same
degree: linking is degree-preserving, so the legal-sum stage's degree is
exactly the largest of its ten sub-stages' degrees. -/
theorem recoveryLegalSumEnvelopeFuel_polyBounded
    {inputLength handoff measure stage degree : ℕ}
    (hsyntax :
      PolyBounded (recoveryLegalSumSyntaxFuel handoff) measure stage degree)
    (hbound :
      PolyBounded (recoveryLegalSumBoundStageFuel handoff) measure stage degree)
    (hcoefficientLowering :
      PolyBounded recoveryLegalTermCoefficientLoweringFuel measure stage degree)
    (hcoefficientStage :
      PolyBounded (recoveryLegalTermCoefficientStageFuel inputLength handoff)
        measure stage degree)
    (hcircuitLowering :
      PolyBounded recoveryLegalTermCircuitLoweringFuel measure stage degree)
    (hcircuitStage :
      PolyBounded (recoveryLegalTermCircuitStageFuel inputLength handoff)
        measure stage degree)
    (hbitCapLowering :
      PolyBounded recoveryLegalTermBitCapLoweringFuel measure stage degree)
    (hbitCapStage :
      PolyBounded
        (recoveryLegalTermBitCapStageFuel
          (legalSumBitCapStageInput inputLength handoff)) measure stage degree)
    (hmass :
      PolyBounded
        (recoveryLegalTermMassFuel inputLength
          (legalSumMassStageInput inputLength handoff)) measure stage degree)
    (hresourceTail :
      PolyBounded (recoveryLegalSumResourceTailFuel inputLength handoff) measure
        stage degree) :
    PolyBounded (recoveryLegalSumEnvelopeFuel inputLength handoff) measure
      (legalSumEnvelopeChainCoefficient stage) degree := by
  have hchain :
      PolyBounded
        (linkFuel legalSumChainTail₁ (recoveryLegalSumSyntaxFuel handoff) <|
          linkFuel legalSumChainTail₂ (recoveryLegalSumBoundStageFuel handoff) <|
            linkFuel legalSumChainTail₃
              recoveryLegalTermCoefficientLoweringFuel <|
              linkFuel legalSumChainTail₄
                (recoveryLegalTermCoefficientStageFuel inputLength handoff) <|
                linkFuel legalSumChainTail₅
                  recoveryLegalTermCircuitLoweringFuel <|
                  linkFuel legalSumChainTail₆
                    (recoveryLegalTermCircuitStageFuel inputLength handoff) <|
                    linkFuel legalSumChainTail₇
                      recoveryLegalTermBitCapLoweringFuel <|
                      linkFuel legalSumChainTail₈
                        (recoveryLegalTermBitCapStageFuel
                          (legalSumBitCapStageInput inputLength handoff)) <|
                        linkFuel legalSumChainTail₉
                          (recoveryLegalTermMassFuel inputLength
                            (legalSumMassStageInput inputLength handoff))
                          (recoveryLegalSumResourceTailFuel inputLength handoff))
        measure (legalSumEnvelopeChainCoefficient stage) degree :=
    legalSumChainFuel_polyBounded (first := legalSumChainTail₁)
      (second := legalSumChainTail₂) (third := legalSumChainTail₃)
      (fourth := legalSumChainTail₄) (fifth := legalSumChainTail₅)
      (sixth := legalSumChainTail₆) (seventh := legalSumChainTail₇)
      (eighth := legalSumChainTail₈) (ninth := legalSumChainTail₉)
      hsyntax hbound hcoefficientLowering hcoefficientStage hcircuitLowering
      hcircuitStage hbitCapLowering hbitCapStage hmass hresourceTail
  exact hchain

/-! ## §2 The eleven-way maximum, named

The width side of the chain is a maximum, so it costs no coefficient at all: a
uniform envelope for the eleven entries *is* an envelope for the chain, at the
same coefficient and the same degree. -/

/-- **The legal-sum envelope's register requirement, dominated.** -/
theorem recoveryLegalSumEnvelopeBits_polyBounded
    {inputLength handoff measure stage degree : ℕ}
    (hlength : PolyBounded (natBitLength inputLength) measure stage degree)
    (hsyntax :
      PolyBounded (recoveryLegalSumSyntaxBits inputLength handoff) measure stage
        degree)
    (hbound :
      PolyBounded (recoveryLegalSumBoundStageBits inputLength handoff) measure
        stage degree)
    (hcoefficientLowering :
      PolyBounded (recoveryLegalTermCoefficientLoweringBits inputLength handoff)
        measure stage degree)
    (hcoefficientStage :
      PolyBounded (recoveryLegalTermCoefficientStageBits inputLength handoff)
        measure stage degree)
    (hcircuitLowering :
      PolyBounded (recoveryLegalTermCircuitLoweringBits inputLength handoff)
        measure stage degree)
    (hcircuitStage :
      PolyBounded (recoveryLegalTermCircuitStageBits inputLength handoff)
        measure stage degree)
    (hbitCapLowering :
      PolyBounded
        (recoveryLegalTermBitCapLoweringBits inputLength
          (legalSumBitCapStageInput inputLength handoff)) measure stage degree)
    (hbitCapStage :
      PolyBounded
        (recoveryLegalTermBitCapStageBits inputLength
          (legalSumBitCapStageInput inputLength handoff)) measure stage degree)
    (hmass :
      PolyBounded
        (recoveryLegalTermMassBits inputLength
          (legalSumMassStageInput inputLength handoff)) measure stage degree)
    (hresourceTail :
      PolyBounded (recoveryLegalSumResourceTailBits inputLength handoff) measure
        stage degree) :
    PolyBounded (recoveryLegalSumEnvelopeBits inputLength handoff) measure stage
      degree := by
  have hchain :
      PolyBounded
        (max (natBitLength inputLength) <|
          max (recoveryLegalSumSyntaxBits inputLength handoff) <|
            max (recoveryLegalSumBoundStageBits inputLength handoff) <|
              max (recoveryLegalTermCoefficientLoweringBits inputLength
                handoff) <|
                max (recoveryLegalTermCoefficientStageBits inputLength
                  handoff) <|
                  max (recoveryLegalTermCircuitLoweringBits inputLength
                    handoff) <|
                    max (recoveryLegalTermCircuitStageBits inputLength
                      handoff) <|
                      max
                        (recoveryLegalTermBitCapLoweringBits inputLength
                          (legalSumBitCapStageInput inputLength handoff)) <|
                        max
                          (recoveryLegalTermBitCapStageBits inputLength
                            (legalSumBitCapStageInput inputLength handoff)) <|
                          max
                            (recoveryLegalTermMassBits inputLength
                              (legalSumMassStageInput inputLength handoff))
                            (recoveryLegalSumResourceTailBits inputLength
                              handoff))
        measure stage degree :=
    legalSumChainBits_polyBounded hlength hsyntax hbound hcoefficientLowering
      hcoefficientStage hcircuitLowering hcircuitStage hbitCapLowering
      hbitCapStage hmass hresourceTail
  exact hchain

/-! ## §3 The chain coefficient of an arbitrary linker chain

Every sub-stage of the legal-sum envelope is itself a right-nested `linkFuel`
chain, so one list-indexed coefficient serves them all.  `chainCoefficient` is
the exact expression a cascade of `linkFuel_polyBounded` applications produces
at a uniform stage coefficient: reading the spans off the chain's tails from the
outside in, each node contributes its own span, the linker's `5`, and one copy
of the stage coefficient, and the innermost node contributes one extra copy for
the terminal charge.

The list is a list of *closed* natural numbers over composed programs.  It is
consumed only by `List.foldr`, whose reduction is structural in the list, so no
`programRegisterSpan` is ever evaluated. -/

/-- The coefficient an `n`-node right-nested `linkFuel` chain produces from the
`n` linked tails' spans and one uniform stage coefficient. -/
def chainCoefficient (spans : List ℕ) (stage : ℕ) : ℕ :=
  spans.foldr (fun span rest => span + 5 + stage + rest) stage

/-- `chainCoefficient` at nine tails agrees with the envelope module's
nine-argument coefficient.  Stated over *variables*: the nine spans are closed
natural numbers over composed programs, so a goal closable by reflexivity at
the instantiated spans would be evaluated by the kernel. -/
theorem chainCoefficient_nine
    (span₁ span₂ span₃ span₄ span₅ span₆ span₇ span₈ span₉ stage : ℕ) :
    chainCoefficient
        [span₁, span₂, span₃, span₄, span₅, span₆, span₇, span₈, span₉] stage =
      legalSumEnvelopeCoefficient span₁ span₂ span₃ span₄ span₅ span₆ span₇
        span₈ span₉ stage := rfl

/-- The twelfth (innermost) linked tail of the mass chain. -/
def massChainTail₁₂ : NPOracleProgram :=
  recoveryLegalTermMassComparisonProgram

def massChainTail₁₁ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassLeStageProgram massChainTail₁₂

def massChainTail₁₀ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassLeLoweringProgram massChainTail₁₁

def massChainTail₉ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassRightProductStageProgram massChainTail₁₀

def massChainTail₈ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassRightProductLoweringProgram massChainTail₉

def massChainTail₇ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassLeftProductStageProgram massChainTail₈

def massChainTail₆ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassLeftProductLoweringProgram massChainTail₇

def massChainTail₅ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassCapStageProgram massChainTail₆

def massChainTail₄ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassCapLoweringProgram massChainTail₅

def massChainTail₃ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassFoldStageProgram massChainTail₄

def massChainTail₂ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassFoldLoweringProgram massChainTail₃

/-- The first (outermost) linked tail of the mass chain. -/
def massChainTail₁ : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassSummaryStageProgram massChainTail₂

/-- The twelve linked tails of the mass chain, outermost first. -/
def massChainSpans : List ℕ :=
  [programRegisterSpan massChainTail₁, programRegisterSpan massChainTail₂,
    programRegisterSpan massChainTail₃, programRegisterSpan massChainTail₄,
    programRegisterSpan massChainTail₅, programRegisterSpan massChainTail₆,
    programRegisterSpan massChainTail₇, programRegisterSpan massChainTail₈,
    programRegisterSpan massChainTail₉, programRegisterSpan massChainTail₁₀,
    programRegisterSpan massChainTail₁₁, programRegisterSpan massChainTail₁₂]

/-- **The mass stage, dominated.**  Its seven inline numerals are absorbed by a
stage coefficient of at least `21`; the six pipeline stages are the hypotheses.
Linking is degree-preserving, so the mass chain's degree is the largest of the
six stages' degrees. -/
theorem recoveryLegalTermMassFuel_polyBounded
    {inputLength bitCapStage measure stage degree : ℕ}
    (hnumerals : 21 ≤ stage)
    (hsummary :
      PolyBounded (recoveryLegalTermMassSummaryStageFuel inputLength bitCapStage)
        measure stage degree)
    (hfold :
      PolyBounded (recoveryLegalTermMassFoldStageFuel inputLength bitCapStage)
        measure stage degree)
    (hcap :
      PolyBounded (recoveryLegalTermMassCapStageFuel inputLength bitCapStage)
        measure stage degree)
    (hleftProduct :
      PolyBounded
        (recoveryLegalTermMassLeftProductStageFuel inputLength bitCapStage)
        measure stage degree)
    (hrightProduct :
      PolyBounded
        (recoveryLegalTermMassRightProductStageFuel inputLength bitCapStage)
        measure stage degree)
    (hle :
      PolyBounded (recoveryLegalTermMassLeStageFuel inputLength bitCapStage)
        measure stage degree) :
    PolyBounded (recoveryLegalTermMassFuel inputLength bitCapStage) measure
      (chainCoefficient massChainSpans stage) degree := by
  have h₂₁ : PolyBounded 21 measure stage degree :=
    PolyBounded.of_le_coefficient hnumerals
  have h₇ : PolyBounded 7 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have h₁₃ : PolyBounded 13 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have h₁₀ : PolyBounded 10 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have h₉ : PolyBounded 9 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have h₁₁ : PolyBounded 11 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have node₁₂ := linkFuel_polyBounded (second := massChainTail₁₂) hle h₂₁
  have node₁₁ := linkFuel_polyBounded (second := massChainTail₁₁) h₇ node₁₂
  have node₁₀ :=
    linkFuel_polyBounded (second := massChainTail₁₀) hrightProduct node₁₁
  have node₉ := linkFuel_polyBounded (second := massChainTail₉) h₁₃ node₁₀
  have node₈ :=
    linkFuel_polyBounded (second := massChainTail₈) hleftProduct node₉
  have node₇ := linkFuel_polyBounded (second := massChainTail₇) h₁₀ node₈
  have node₆ := linkFuel_polyBounded (second := massChainTail₆) hcap node₇
  have node₅ := linkFuel_polyBounded (second := massChainTail₅) h₁₀ node₆
  have node₄ := linkFuel_polyBounded (second := massChainTail₄) hfold node₅
  have node₃ := linkFuel_polyBounded (second := massChainTail₃) h₉ node₄
  have node₂ := linkFuel_polyBounded (second := massChainTail₂) hsummary node₃
  have node₁ := linkFuel_polyBounded (second := massChainTail₁) h₁₁ node₂
  exact node₁

private theorem bitsLength_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

/-- **The bit-serial multiplier, dominated.**  Its fuel is linear in the
multiplier's width, so the degree is the width certificate's degree. -/
theorem bitSerialMulFuel_polyBounded
    {right measure coefficient degree : ℕ}
    (hwidth : PolyBounded (natBitLength right) measure coefficient degree) :
    PolyBounded (bitSerialMulFuel right) measure (8 * coefficient + 5) degree := by
  have htotal :=
    (hwidth.const_mul 8).add (polyBounded_const 5 measure degree)
  refine htotal.mono ?_
  have hleaf := bitSerialMulFuel_le right
  have hbits := bitsLength_le_natBitLength right
  omega

/-- **The native comparison, dominated.**  Its fuel is linear in the width of
the compared pair. -/
theorem nativeNatLeFuel_polyBounded
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded (natBitLength left) measure leftCoefficient degree)
    (hright : PolyBounded (natBitLength right) measure rightCoefficient degree) :
    PolyBounded (nativeNatLeFuel left right) measure
      (36 * max leftCoefficient rightCoefficient + 8) degree := by
  have hpair := polyBounded_natBitLength_pair hleft hright
  have hscaled := hpair.const_mul (factor := 18)
  have htotal := hscaled.add (polyBounded_const 8 measure degree)
  have hcoefficient :
      18 * (2 * max leftCoefficient rightCoefficient) + 8 =
        36 * max leftCoefficient rightCoefficient + 8 := by ring
  rw [hcoefficient] at htotal
  refine htotal.mono ?_
  have hleaf := nativeNatLeFuel_le left right
  have hinput :
      nativeNatLeBits left right = natBitLength (Nat.pair left right) := rfl
  rw [hinput] at hleaf
  exact hleaf

/-- **The mass pipeline's left product stage, discharged.** -/
theorem recoveryLegalTermMassLeftProductStageFuel_polyBounded
    {inputLength bitCapStage measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded
        (natBitLength
          (rationalSummaryDenominator
            (recoveryLegalTermMassCapSummary inputLength bitCapStage))) measure
        coefficient degree) :
    PolyBounded
      (recoveryLegalTermMassLeftProductStageFuel inputLength bitCapStage) measure
      (8 * coefficient + 5 + 4) degree :=
  preserveRightFuel_polyBounded (bitSerialMulFuel_polyBounded hwidth)

/-- **The mass pipeline's right product stage, discharged.** -/
theorem recoveryLegalTermMassRightProductStageFuel_polyBounded
    {inputLength bitCapStage measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded
        (natBitLength
          (Nat.unpair
            (recoveryLegalTermMassFoldValue inputLength bitCapStage)).2) measure
        coefficient degree) :
    PolyBounded
      (recoveryLegalTermMassRightProductStageFuel inputLength bitCapStage)
      measure (8 * coefficient + 5 + 4) degree :=
  preserveRightFuel_polyBounded (bitSerialMulFuel_polyBounded hwidth)

/-- **The mass pipeline's comparison stage, discharged.** -/
theorem recoveryLegalTermMassLeStageFuel_polyBounded
    {inputLength bitCapStage measure leftCoefficient rightCoefficient
      degree : ℕ}
    (hleft :
      PolyBounded
        (natBitLength (recoveryLegalTermMassLeftProduct inputLength bitCapStage))
        measure leftCoefficient degree)
    (hright :
      PolyBounded
        (natBitLength
          (recoveryLegalTermMassRightProduct inputLength bitCapStage)) measure
        rightCoefficient degree) :
    PolyBounded (recoveryLegalTermMassLeStageFuel inputLength bitCapStage)
      measure (36 * max leftCoefficient rightCoefficient + 8 + 4) degree :=
  preserveRightFuel_polyBounded (nativeNatLeFuel_polyBounded hleft hright)

/-- The largest closed charge of the syntax chain. -/
def legalSumSyntaxClosedBound : ℕ :=
  max recoveryLegalSumTupleLoweringFuel <|
    max recoveryLegalSumTupleStageFuel <|
      max recoveryLegalSumProjectionFuel <|
        max recoveryLegalSumArityLoweringFuel <|
          max recoveryLegalSumTermsLoweringFuel
            recoveryLegalSumLengthLoweringFuel

def syntaxChainTail₉ : NPOracleProgram :=
  recoveryLegalSumLengthStageProgram

def syntaxChainTail₈ : NPOracleProgram :=
  linkPrograms recoveryLegalSumLengthLoweringProgram syntaxChainTail₉

def syntaxChainTail₇ : NPOracleProgram :=
  linkPrograms recoveryLegalSumTermsStageProgram syntaxChainTail₈

def syntaxChainTail₆ : NPOracleProgram :=
  linkPrograms recoveryLegalSumTermsLoweringProgram syntaxChainTail₇

def syntaxChainTail₅ : NPOracleProgram :=
  linkPrograms recoveryLegalSumArityStageProgram syntaxChainTail₆

def syntaxChainTail₄ : NPOracleProgram :=
  linkPrograms recoveryLegalSumArityLoweringProgram syntaxChainTail₅

def syntaxChainTail₃ : NPOracleProgram :=
  linkPrograms recoveryLegalSumQStageProgram syntaxChainTail₄

def syntaxChainTail₂ : NPOracleProgram :=
  linkPrograms recoveryLegalSumProjectionProgram syntaxChainTail₃

def syntaxChainTail₁ : NPOracleProgram :=
  linkPrograms recoveryLegalSumTupleStageProgram syntaxChainTail₂

/-- The nine linked tails of the syntax chain, outermost first. -/
def syntaxChainSpans : List ℕ :=
  [programRegisterSpan syntaxChainTail₁, programRegisterSpan syntaxChainTail₂,
    programRegisterSpan syntaxChainTail₃, programRegisterSpan syntaxChainTail₄,
    programRegisterSpan syntaxChainTail₅, programRegisterSpan syntaxChainTail₆,
    programRegisterSpan syntaxChainTail₇, programRegisterSpan syntaxChainTail₈,
    programRegisterSpan syntaxChainTail₉]

/-- **The syntax stage, dominated.** -/
theorem recoveryLegalSumSyntaxFuel_polyBounded
    {handoff measure stage degree : ℕ}
    (hclosed : legalSumSyntaxClosedBound ≤ stage)
    (hq :
      PolyBounded (recoveryLegalSumQStageFuel handoff) measure stage degree)
    (harity :
      PolyBounded (recoveryLegalSumArityStageFuel handoff) measure stage degree)
    (hterms :
      PolyBounded (recoveryLegalSumTermsStageFuel handoff) measure stage degree)
    (hlength :
      PolyBounded (recoveryLegalSumLengthStageFuel handoff) measure stage
        degree) :
    PolyBounded (recoveryLegalSumSyntaxFuel handoff) measure
      (chainCoefficient syntaxChainSpans stage) degree := by
  have htupleLowering :
      PolyBounded recoveryLegalSumTupleLoweringFuel measure stage degree :=
    PolyBounded.of_le_coefficient (le_trans (le_max_left _ _) hclosed)
  have htupleStage :
      PolyBounded recoveryLegalSumTupleStageFuel measure stage degree :=
    PolyBounded.of_le_coefficient
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hclosed)
  have hprojection :
      PolyBounded recoveryLegalSumProjectionFuel measure stage degree :=
    PolyBounded.of_le_coefficient
      (le_trans
        (le_trans (le_max_left _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))
        hclosed)
  have harityLowering :
      PolyBounded recoveryLegalSumArityLoweringFuel measure stage degree :=
    PolyBounded.of_le_coefficient
      (le_trans
        (le_trans (le_max_left _ _)
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))))
        hclosed)
  have htermsLowering :
      PolyBounded recoveryLegalSumTermsLoweringFuel measure stage degree :=
    PolyBounded.of_le_coefficient
      (le_trans
        (le_trans (le_max_left _ _)
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _)
              (le_trans (le_max_right _ _) (le_max_right _ _)))))
        hclosed)
  have hlengthLowering :
      PolyBounded recoveryLegalSumLengthLoweringFuel measure stage degree :=
    PolyBounded.of_le_coefficient
      (le_trans
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _)
              (le_trans (le_max_right _ _) (le_max_right _ _)))))
        hclosed)
  have node₉ :=
    linkFuel_polyBounded (second := syntaxChainTail₉) hlengthLowering hlength
  have node₈ := linkFuel_polyBounded (second := syntaxChainTail₈) hterms node₉
  have node₇ :=
    linkFuel_polyBounded (second := syntaxChainTail₇) htermsLowering node₈
  have node₆ := linkFuel_polyBounded (second := syntaxChainTail₆) harity node₇
  have node₅ :=
    linkFuel_polyBounded (second := syntaxChainTail₅) harityLowering node₆
  have node₄ := linkFuel_polyBounded (second := syntaxChainTail₄) hq node₅
  have node₃ :=
    linkFuel_polyBounded (second := syntaxChainTail₃) hprojection node₄
  have node₂ :=
    linkFuel_polyBounded (second := syntaxChainTail₂) htupleStage node₃
  have node₁ :=
    linkFuel_polyBounded (second := syntaxChainTail₁) htupleLowering node₂
  exact node₁

theorem recoveryLegalSumQStageFuel_polyBounded
    {handoff measure coefficient degree : ℕ}
    (hleaf :
      PolyBounded (canonicalNatValidationFuel (recoveryLegalSumQCode handoff))
        measure coefficient degree) :
    PolyBounded (recoveryLegalSumQStageFuel handoff) measure (coefficient + 4)
      degree :=
  preserveRightFuel_polyBounded hleaf

theorem recoveryLegalSumArityStageFuel_polyBounded
    {handoff measure coefficient degree : ℕ}
    (hleaf :
      PolyBounded
        (nativeNatEqFuel (recoveryLegalSumArityValue handoff)
          (handoffSelectedExpectedArity handoff)) measure coefficient degree) :
    PolyBounded (recoveryLegalSumArityStageFuel handoff) measure
      (coefficient + 4) degree :=
  preserveRightFuel_polyBounded hleaf

theorem recoveryLegalSumTermsStageFuel_polyBounded
    {handoff measure coefficient degree : ℕ}
    (hleaf :
      PolyBounded
        (balancedValidationMapGuardFuel (recoveryLegalSumTermsCode handoff))
        measure coefficient degree) :
    PolyBounded (recoveryLegalSumTermsStageFuel handoff) measure
      (coefficient + 4) degree :=
  preserveRightFuel_polyBounded hleaf

theorem recoveryLegalSumLengthStageFuel_polyBounded
    {handoff measure coefficient degree : ℕ}
    (hleaf :
      PolyBounded (balancedLengthFuel (recoveryLegalSumTermCodes handoff))
        measure coefficient degree) :
    PolyBounded (recoveryLegalSumLengthStageFuel handoff) measure
      (coefficient + 4) degree :=
  preserveRightFuel_polyBounded hleaf

/-- **The legal-sum bound stage, discharged.**  One linker node over a closed
lowering charge and the shared bound check. -/
theorem recoveryLegalSumBoundStageFuel_polyBounded
    {handoff measure countCoefficient capCoefficient degree : ℕ}
    (hcount :
      PolyBounded (natBitLength (recoveryLegalSumTermCount handoff)) measure
        countCoefficient degree)
    (hcap :
      PolyBounded (natBitLength (handoffSelectedTermCap handoff)) measure
        capCoefficient degree) :
    PolyBounded (recoveryLegalSumBoundStageFuel handoff) measure
      (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
          recoveryLegalSumBoundLoweringFuel +
        (36 * max countCoefficient capCoefficient + 24)) degree := by
  have hcheck := recoveryBoundedContextCheckFuel_polyBounded hcount hcap
  have hnode :=
    linkFuel_polyBounded (second := recoveryBoundedContextCheckProgram)
      (polyBounded_const recoveryLegalSumBoundLoweringFuel measure degree)
      hcheck
  exact hnode

/-- **The legal-sum resource tail, reduced.**  One linker node over the
resource stage and the *closed* finalization charge. -/
theorem recoveryLegalSumResourceTailFuel_polyBounded
    {inputLength handoff measure stageCoefficient finalCoefficient degree : ℕ}
    (hresource :
      PolyBounded (recoveryLegalSumResourceStageFuel inputLength handoff)
        measure stageCoefficient degree)
    (hfinalization :
      PolyBounded recoveryLegalSumFinalizationFuel measure finalCoefficient
        degree) :
    PolyBounded (recoveryLegalSumResourceTailFuel inputLength handoff) measure
      (programRegisterSpan recoveryLegalSumFinalizationProgram + 5 +
        stageCoefficient + finalCoefficient) degree := by
  have hnode :=
    linkFuel_polyBounded (second := recoveryLegalSumFinalizationProgram)
      hresource hfinalization
  exact hnode

/-- **The bit-cap stage, reduced.**  One native call into the coefficient
bit-cap list validator, wrapped in the context-preserving adapter: the request
list is a singleton, so the node is degree-preserving and the stage's degree is
the callee's. -/
theorem recoveryLegalTermBitCapStageFuel_polyBounded
    {circuitStage measure calleeCoefficient degree : ℕ}
    (hcallee :
      PolyBounded
        (recoveryLegalTermCoefficientBitCapListFuel
          (recoveryLegalTermBitCapSelectedCap circuitStage)
          (recoveryLegalTermBitCapMappedCode circuitStage)) measure
        calleeCoefficient degree) :
    PolyBounded (recoveryLegalTermBitCapStageFuel circuitStage) measure
      (nativeCallOverhead recoveryLegalTermCoefficientBitCapListProgram +
        calleeCoefficient + 4) degree := by
  have hcall :
      PolyBounded
        (nativeCallFuel recoveryLegalTermCoefficientBitCapListProgram
          (recoveryLegalTermCoefficientBitCapListFuel
            (recoveryLegalTermBitCapSelectedCap circuitStage)
            (recoveryLegalTermBitCapMappedCode circuitStage))
          (recoveryLegalTermBitCapSelectedCap circuitStage)
          (recoveryLegalTermBitCapMappedCode circuitStage)) measure
        (nativeCallOverhead recoveryLegalTermCoefficientBitCapListProgram +
          calleeCoefficient) degree :=
    ((polyBounded_const
      (nativeCallOverhead recoveryLegalTermCoefficientBitCapListProgram) measure
      degree).add hcallee).mono (nativeCallFuel_le _ _ _ _)
  exact preserveRightFuel_polyBounded hcall

/-- **The mass pipeline's summary stage, reduced.**  One native call into the
rational-summary list validator. -/
theorem recoveryLegalTermMassSummaryStageFuel_polyBounded
    {inputLength bitCapStage measure calleeCoefficient degree : ℕ}
    (hcallee :
      PolyBounded
        (recoveryLegalTermRationalSummaryListFuel inputLength
          (recoveryLegalTermMassMappedCode bitCapStage)) measure
        calleeCoefficient degree) :
    PolyBounded (recoveryLegalTermMassSummaryStageFuel inputLength bitCapStage)
      measure
      (nativeCallOverhead recoveryLegalTermRationalSummaryListProgram +
        calleeCoefficient + 4) degree := by
  have hcall :
      PolyBounded
        (nativeCallFuel recoveryLegalTermRationalSummaryListProgram
          (recoveryLegalTermRationalSummaryListFuel inputLength
            (recoveryLegalTermMassMappedCode bitCapStage))
          inputLength (recoveryLegalTermMassMappedCode bitCapStage)) measure
        (nativeCallOverhead recoveryLegalTermRationalSummaryListProgram +
          calleeCoefficient) degree :=
    ((polyBounded_const
      (nativeCallOverhead recoveryLegalTermRationalSummaryListProgram) measure
      degree).add hcallee).mono (nativeCallFuel_le _ _ _ _)
  exact preserveRightFuel_polyBounded hcall

/-- **The legal-sum resource stage, reduced.**  One linker node over the wire
stage and the description stage. -/
theorem recoveryLegalSumResourceStageFuel_polyBounded
    {inputLength handoff measure wireCoefficient descriptionCoefficient
      degree : ℕ}
    (hwire :
      PolyBounded
        (recoveryLegalTermWireStageFuel
          (recoveryLegalSumMassStageOutput inputLength handoff)) measure
        wireCoefficient degree)
    (hdescription :
      PolyBounded
        (recoveryLegalTermDescriptionStageFuel
          (recoveryLegalSumWireGateOutput inputLength handoff)) measure
        descriptionCoefficient degree) :
    PolyBounded (recoveryLegalSumResourceStageFuel inputLength handoff) measure
      (programRegisterSpan recoveryLegalTermDescriptionStageProgram + 5 +
        wireCoefficient + descriptionCoefficient) degree := by
  have hnode :=
    linkFuel_polyBounded (second := recoveryLegalTermDescriptionStageProgram)
      hwire hdescription
  exact hnode

/-- **The mass pipeline's cap stage, reduced.**  One rational validation. -/
theorem recoveryLegalTermMassCapStageFuel_polyBounded
    {inputLength bitCapStage measure coefficient degree : ℕ}
    (hleaf :
      PolyBounded
        (rationalValidationFuel inputLength
          (Nat.unpair
            (recoveryLegalTermMassCapLoweringOutput inputLength
              bitCapStage)).1) measure coefficient degree) :
    PolyBounded (recoveryLegalTermMassCapStageFuel inputLength bitCapStage)
      measure (coefficient + 4) degree :=
  preserveRightFuel_polyBounded hleaf

/-- The handoff the legal-sum envelope runs on, for one weak-verifier
request. -/
def legalSumRequestHandoff
    (limitsOf : ℕ → RecoveryWitnessLimits) (request : WeakVerifierRequest) : ℕ :=
  recoveryValidatorOraclePrefixOutput (limitsOf request.inputArity)
    (encodeBitInput request.witness)

theorem hvalidatorFuel_of_legalSumStages
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stage frontier stageCoefficient degree : ℕ)
    (hdegree : degree ≤ recoveryVerifierDegree)
    (hlink : legalSumEnvelopeChainCoefficient stage ≤ frontier)
    (hcoefficient :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (programRegisterSpan
              (linkPrograms recoveryOracleCallProgram <|
                linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
              recoveryOracleCallLoweringFuel +
            (programRegisterSpan
                (linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
                (nativeContextCallOverhead booleanCircuitValidationProgram +
                  frontier) +
              (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
                  recoveryOracleBoundLoweringFuel +
                (36 * max frontier frontier + 24)))) <|
          max frontier recoveryValidatorModeRawFuel) ≤ stageCoefficient)
    (hcircuit : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness)))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hsyntax : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumSyntaxFuel (legalSumRequestHandoff limitsOf request))
        request.measure stage degree)
    (hbound : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumBoundStageFuel
          (legalSumRequestHandoff limitsOf request)) request.measure stage
        degree)
    (hcoefficientLowering : ∀ request : WeakVerifierRequest,
      PolyBounded recoveryLegalTermCoefficientLoweringFuel request.measure stage
        degree)
    (hcoefficientStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCoefficientStageFuel
          (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure stage
        degree)
    (hcircuitLowering : ∀ request : WeakVerifierRequest,
      PolyBounded recoveryLegalTermCircuitLoweringFuel request.measure stage
        degree)
    (hcircuitStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCircuitStageFuel (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure stage
        degree)
    (hbitCapLowering : ∀ request : WeakVerifierRequest,
      PolyBounded recoveryLegalTermBitCapLoweringFuel request.measure stage
        degree)
    (hbitCapStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermBitCapStageFuel
          (legalSumBitCapStageInput (WeakVerifierRequest.length request)
            (legalSumRequestHandoff limitsOf request))) request.measure stage
        degree)
    (hmass : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermMassFuel (WeakVerifierRequest.length request)
          (legalSumMassStageInput (WeakVerifierRequest.length request)
            (legalSumRequestHandoff limitsOf request))) request.measure stage
        degree)
    (hresourceTail : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumResourceTailFuel (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure stage
        degree)
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
  hvalidatorFuel_of_frontier limitsOf frontier stageCoefficient degree hdegree
    hcoefficient hcircuit hresult hhandoff
    (fun request =>
      (recoveryLegalSumEnvelopeFuel_polyBounded (hsyntax request)
        (hbound request) (hcoefficientLowering request)
        (hcoefficientStage request) (hcircuitLowering request)
        (hcircuitStage request) (hbitCapLowering request)
        (hbitCapStage request) (hmass request)
        (hresourceTail request)).coefficient_mono hlink)
    request

theorem hvalidatorBits_of_legalSumStages
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (frontier stageCoefficient degree : ℕ)
    (hdegree : degree ≤ recoveryVerifierDegree)
    (hcoefficient :
      (max frontier <|
        max (max frontier (16 * frontier)) <|
          max (max (max frontier (4 * frontier)) frontier) <|
            max frontier (max frontier (2 * frontier))) ≤ stageCoefficient)
    (hlength : ∀ request : WeakVerifierRequest,
      PolyBounded (natBitLength (WeakVerifierRequest.length request))
        request.measure frontier degree)
    (hprefix : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorPrefixWidth (limitsOf request.inputArity)
          (encodeBitInput request.witness)) request.measure frontier degree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request) (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hsyntax : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumSyntaxBits (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hbound : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumBoundStageBits (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hcoefficientLowering : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCoefficientLoweringBits
          (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hcoefficientStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCoefficientStageBits
          (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hcircuitLowering : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCircuitLoweringBits
          (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hcircuitStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermCircuitStageBits (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (hbitCapLowering : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermBitCapLoweringBits
          (WeakVerifierRequest.length request)
          (legalSumBitCapStageInput (WeakVerifierRequest.length request)
            (legalSumRequestHandoff limitsOf request))) request.measure frontier
        degree)
    (hbitCapStage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermBitCapStageBits (WeakVerifierRequest.length request)
          (legalSumBitCapStageInput (WeakVerifierRequest.length request)
            (legalSumRequestHandoff limitsOf request))) request.measure frontier
        degree)
    (hmass : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalTermMassBits (WeakVerifierRequest.length request)
          (legalSumMassStageInput (WeakVerifierRequest.length request)
            (legalSumRequestHandoff limitsOf request))) request.measure frontier
        degree)
    (hresourceTail : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumResourceTailBits (WeakVerifierRequest.length request)
          (legalSumRequestHandoff limitsOf request)) request.measure frontier
        degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget stageCoefficient recoveryVerifierDegree
        request.measure :=
  hvalidatorBits_of_frontier limitsOf frontier stageCoefficient degree hdegree
    hcoefficient hlength hprefix hstage hcall
    (fun request =>
      recoveryLegalSumEnvelopeBits_polyBounded (hlength request)
        (hsyntax request) (hbound request) (hcoefficientLowering request)
        (hcoefficientStage request) (hcircuitLowering request)
        (hcircuitStage request) (hbitCapLowering request)
        (hbitCapStage request) (hmass request) (hresourceTail request))
    hmode request

theorem recoveryVerifierDegree_eq_four : recoveryVerifierDegree = 4 := rfl

/-- The degree numeral the walk itself costs: `0`.  Stated as the fact that a
residual envelope of degree `degree` yields a validator premise at the same
`degree`, for every `degree`. -/
theorem legalSumWalk_degree_preserving
    {inputLength handoff measure stage degree : ℕ}
    (hsyntax :
      PolyBounded (recoveryLegalSumSyntaxFuel handoff) measure stage degree)
    (hbound :
      PolyBounded (recoveryLegalSumBoundStageFuel handoff) measure stage degree)
    (hcoefficientLowering :
      PolyBounded recoveryLegalTermCoefficientLoweringFuel measure stage degree)
    (hcoefficientStage :
      PolyBounded (recoveryLegalTermCoefficientStageFuel inputLength handoff)
        measure stage degree)
    (hcircuitLowering :
      PolyBounded recoveryLegalTermCircuitLoweringFuel measure stage degree)
    (hcircuitStage :
      PolyBounded (recoveryLegalTermCircuitStageFuel inputLength handoff)
        measure stage degree)
    (hbitCapLowering :
      PolyBounded recoveryLegalTermBitCapLoweringFuel measure stage degree)
    (hbitCapStage :
      PolyBounded
        (recoveryLegalTermBitCapStageFuel
          (legalSumBitCapStageInput inputLength handoff)) measure stage degree)
    (hmass :
      PolyBounded
        (recoveryLegalTermMassFuel inputLength
          (legalSumMassStageInput inputLength handoff)) measure stage degree)
    (hresourceTail :
      PolyBounded (recoveryLegalSumResourceTailFuel inputLength handoff) measure
        stage degree) :
    PolyBounded (recoveryLegalSumEnvelopeFuel inputLength handoff) measure
      (legalSumEnvelopeChainCoefficient stage) degree :=
  recoveryLegalSumEnvelopeFuel_polyBounded hsyntax hbound hcoefficientLowering
    hcoefficientStage hcircuitLowering hcircuitStage hbitCapLowering
    hbitCapStage hmass hresourceTail

end NearCubicWires.ValidatorLegalSumWalk
