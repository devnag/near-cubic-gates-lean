import Proof.Circuits.ValidatorLeafFuelBounds

namespace NearCubicWires.ValidatorCompositeLeafBounds

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §1 The decoded list is the structural parse

`balancedValidationMapCodes` is the public decoder's output, and the public
decoder accepts only canonical codes — so whenever it accepts, the list it
returns is exactly the structural parser's atom list.  On a rejected code the
list is empty.  Either way its length is bounded by the parse's, which §2 of
`ValidatorLeafWidthCore` caps at twice the code's width. -/

theorem balancedValidationMapCodes_length_le (raw : ℕ) :
    (balancedValidationMapCodes raw).length ≤
      (rawBalancedTraversalTree raw).atoms.length := by
  unfold balancedValidationMapCodes
  cases hdecode : decodeBalancedList raw with
  | none => simp
  | some codes =>
      have hcode : encodeBalancedList codes = raw :=
        encodeBalancedList_of_decode hdecode
      have htree : (balancedTraversalTree codes).code = raw := by
        rw [balancedTraversalTree_code, hcode]
      have hnormalized :
          (rawBalancedTraversalTree raw).normalized =
            balancedTraversalTree codes := by
        rw [← htree]
        exact rawBalancedTraversalTree_normalized_code _
      have hatoms : (rawBalancedTraversalTree raw).atoms = codes := by
        change (rawBalancedTraversalTree raw).normalized.atoms = codes
        rw [hnormalized, balancedTraversalTree_atoms]
      simp [hatoms]

/-- **The composite layer's counting ledger.** -/
theorem balancedValidationMapCodes_length_succ_le (raw : ℕ) :
    (balancedValidationMapCodes raw).length + 1 ≤ 2 * natBitLength raw := by
  have hle := balancedValidationMapCodes_length_le raw
  have hatoms := rawBalancedTraversalTree_atoms_length_succ_le raw
  omega

theorem polyBounded_balancedValidationMapCodes_length
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (balancedValidationMapCodes raw).length measure
      (2 * coefficient) degree := by
  refine (hraw.const_mul 2).mono ?_
  have := balancedValidationMapCodes_length_succ_le raw
  omega

theorem balancedValidationMapRequests_length (inputLength raw : ℕ) :
    (balancedValidationMapRequests inputLength raw).length =
      (balancedValidationMapCodes raw).length := by
  simp [balancedValidationMapRequests]

theorem balancedValidationMapOutputs_length
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    (balancedValidationMapOutputs inputLength raw output).length =
      (balancedValidationMapCodes raw).length := by
  simp [balancedValidationMapOutputs, balancedValidationMapRequests]

/-- Width of a count: never more than one bit past the count itself. -/
theorem natBitLength_le_succ (value : ℕ) : natBitLength value ≤ value + 1 := by
  have hlog : Nat.log 2 value ≤ value := Nat.log_le_self 2 value
  unfold natBitLength
  omega

theorem polyBounded_natBitLength_of_polyBounded
    {value measure coefficient degree : ℕ}
    (hvalue : PolyBounded value measure coefficient degree) :
    PolyBounded (natBitLength value) measure (coefficient + 1) degree :=
  (hvalue.add (polyBounded_const 1 measure degree)).mono
    (natBitLength_le_succ value)

theorem nonzeroAtomCount_le_length (values : List ℕ) :
    nonzeroAtomCount values ≤ values.length := by
  induction values with
  | nil => simp [nonzeroAtomCount]
  | cons value rest inductionHypothesis =>
      have hstep : (if value = 0 then 0 else 1) ≤ 1 := by split <;> omega
      simp only [nonzeroAtomCount, List.length_cons]
      omega

theorem nativeInputRequestTreeFuel_le (requestCodes : List ℕ) :
    nativeInputRequestTreeFuel requestCodes ≤ 71 * requestCodes.length + 37 := by
  have hsteps := balancedTraversalStructuralSteps_le_linear requestCodes
  unfold nativeInputRequestTreeFuel
  omega

theorem nativeInputRequestTreeFuel_polyBounded
    {requestCodes : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded requestCodes.length measure coefficient degree) :
    PolyBounded (nativeInputRequestTreeFuel requestCodes) measure
      (71 * coefficient + 37) degree :=
  ((hlength.const_mul 71).add (polyBounded_const 37 measure degree)).mono
    (nativeInputRequestTreeFuel_le requestCodes)

theorem balancedNonzeroCountFuel_polyBounded
    {values : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded values.length measure coefficient degree) :
    PolyBounded (balancedNonzeroCountFuel values) measure
      (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
        (30 * coefficient + 27) + 5) degree := by
  have hwork :
      PolyBounded (7 + supplierSupportCountWorkFuel
        [balancedTraversalTree values]) measure (30 * coefficient + 27)
        degree := by
    refine (((hlength.const_mul 30).add
      (polyBounded_const 27 measure degree))).mono ?_
    have hforest :=
      supplierSupportCountWorkFuel_le [balancedTraversalTree values]
    have hnodes := balancedTraversalTree_nodeCount_le values
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hforest
    omega
  exact linkFuel_polyBounded (second := balancedBoolCountProjectionProgram)
    hwork (polyBounded_const 5 measure degree)

/-- The coefficient one counted map produces. -/
def balancedValidationMapCoefficient (callee : NPOracleProgram)
    (widthCoefficient guardCoefficient calleeCoefficient : ℕ) : ℕ :=
  balancedValidationMapOverhead callee + guardCoefficient +
      (71 * (2 * widthCoefficient) + 37) +
    (37 + 2 * widthCoefficient *
      ((balancedCallLayout callee).calleeSpan + 73 + calleeCoefficient))

/-- **The counted map, dominated.** -/
theorem balancedValidationMapFuel_polyBounded_of_width
    {callee : NPOracleProgram} {calleeFuel : ℕ → ℕ}
    {inputLength raw measure widthCoefficient guardCoefficient
      calleeCoefficient bound widthDegree calleeDegree target : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure widthCoefficient widthDegree)
    (hguard :
      PolyBounded (balancedValidationMapGuardFuel raw) measure guardCoefficient
        target)
    (hcallee : PolyBounded bound measure calleeCoefficient calleeDegree)
    (hbound : ∀ request ∈ balancedValidationMapRequests inputLength raw,
      calleeFuel request ≤ bound)
    (hwidthDegree : widthDegree ≤ target)
    (hcallDegree : widthDegree + calleeDegree ≤ target) :
    PolyBounded (balancedValidationMapFuel callee calleeFuel inputLength raw)
      measure
      (balancedValidationMapCoefficient callee widthCoefficient
        guardCoefficient calleeCoefficient) target := by
  have hcodes := polyBounded_balancedValidationMapCodes_length hraw
  have htree :
      PolyBounded
        (nativeInputRequestTreeFuel (balancedValidationMapCodes raw)) measure
        (71 * (2 * widthCoefficient) + 37) target :=
    (nativeInputRequestTreeFuel_polyBounded hcodes).degree_mono hwidthDegree
  have hrequests :
      PolyBounded (balancedValidationMapRequests inputLength raw).length measure
        (2 * widthCoefficient) widthDegree := by
    rw [balancedValidationMapRequests_length]
    exact hcodes
  have hcall :
      PolyBounded
        (balancedCallFuel callee calleeFuel
          (balancedValidationMapRequests inputLength raw)) measure
        (37 + 2 * widthCoefficient *
          ((balancedCallLayout callee).calleeSpan + 73 + calleeCoefficient))
        target :=
    (balancedCallFuel_polyBounded hrequests hcallee hbound).degree_mono
      hcallDegree
  exact balancedValidationMapFuel_polyBounded hguard htree hcall

/-! ## §4 The counted summary

The summary runs the map and then four counted post-passes — a balanced length
over the callee outputs, a nonzero count over the same outputs, a native
equality between the two resulting counts, and two constant gates.  Every one
of them is charged by the *output list's length*, which is the request list's
length, which is the decoded code list's length: §1's single number.  No
post-pass reads a callee output's magnitude, so the summary needs no width
certificate for the callee results at all, and its degree is the map's. -/

def balancedLengthCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan
        (linkPrograms balancedLengthCountInputProgram <|
          linkPrograms balancedBoolCountProgram
            balancedLengthProjectionProgram) + 5 +
      (71 * coefficient + 37) +
    (programRegisterSpan
          (linkPrograms balancedBoolCountProgram
            balancedLengthProjectionProgram) + 5 + 3 +
      (programRegisterSpan balancedLengthProjectionProgram + 5 +
          (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
            (30 * coefficient + 27) + 5) +
        2))

theorem balancedLengthFuel_polyBounded'
    {values : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded values.length measure coefficient degree) :
    PolyBounded (balancedLengthFuel values) measure
      (balancedLengthCoefficient coefficient) degree :=
  balancedLengthFuel_polyBounded hlength

def nativeNatEqCoefficient (leftCoefficient rightCoefficient : ℕ) : ℕ :=
  programRegisterSpan nativeNatEqCoreProgram + 5 + 6 +
    (programRegisterSpan nativeNatEqGateProgram + 5 +
        (pairedCallOverhead nativeNatLeProgram +
            (36 * max leftCoefficient rightCoefficient + 8) +
          (36 * max rightCoefficient leftCoefficient + 8)) +
      6)

theorem nativeNatEqFuel_polyBounded'
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded (natBitLength left) measure leftCoefficient degree)
    (hright : PolyBounded (natBitLength right) measure rightCoefficient degree) :
    PolyBounded (nativeNatEqFuel left right) measure
      (nativeNatEqCoefficient leftCoefficient rightCoefficient) degree :=
  nativeNatEqFuel_polyBounded hleft hright

def balancedValidationAllLengthCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan (preserveRightProgram balancedLengthProgram) + 5 + 5 +
    (balancedLengthCoefficient coefficient + 4)

theorem balancedValidationAllLengthFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ} {output : ℕ → ℕ}
    (hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure coefficient
        degree) :
    PolyBounded (balancedValidationAllLengthFuel inputLength raw output) measure
      (balancedValidationAllLengthCoefficient coefficient) degree := by
  have houtputs :
      PolyBounded (balancedValidationMapOutputs inputLength raw output).length
        measure coefficient degree := by
    rw [balancedValidationMapOutputs_length]
    exact hcount
  exact linkFuel_polyBounded (second := preserveRightProgram balancedLengthProgram)
    (polyBounded_const 5 measure degree)
    (preserveRightFuel_polyBounded (balancedLengthFuel_polyBounded' houtputs))

def balancedValidationAllCountCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan balancedBoolCountProgram + 5 + 7 +
    (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
      (30 * coefficient + 27) + 5)

theorem balancedValidationAllCountFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ} {output : ℕ → ℕ}
    (hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure coefficient
        degree) :
    PolyBounded (balancedValidationAllCountFuel inputLength raw output) measure
      (balancedValidationAllCountCoefficient coefficient) degree := by
  have houtputs :
      PolyBounded (balancedValidationMapOutputs inputLength raw output).length
        measure coefficient degree := by
    rw [balancedValidationMapOutputs_length]
    exact hcount
  exact linkFuel_polyBounded (second := balancedBoolCountProgram)
    (polyBounded_const 7 measure degree)
    (balancedNonzeroCountFuel_polyBounded houtputs)

def balancedValidationAllEqualityCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan (preserveRightProgram nativeNatEqProgram) + 5 + 7 +
    (nativeNatEqCoefficient (coefficient + 1) (coefficient + 1) + 4)

theorem balancedValidationAllEqualityFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ} {output : ℕ → ℕ}
    (hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure coefficient
        degree) :
    PolyBounded (balancedValidationAllEqualityFuel inputLength raw output)
      measure (balancedValidationAllEqualityCoefficient coefficient) degree := by
  have houtputs :
      PolyBounded (balancedValidationMapOutputs inputLength raw output).length
        measure coefficient degree := by
    rw [balancedValidationMapOutputs_length]
    exact hcount
  have hlength :
      PolyBounded
        (natBitLength
          (balancedValidationMapOutputs inputLength raw output).length) measure
        (coefficient + 1) degree :=
    polyBounded_natBitLength_of_polyBounded houtputs
  have hcountWidth :
      PolyBounded
        (natBitLength
          (nonzeroAtomCount
            (balancedValidationMapOutputs inputLength raw output))) measure
        (coefficient + 1) degree :=
    polyBounded_natBitLength_of_polyBounded
      (houtputs.mono
        (nonzeroAtomCount_le_length
          (balancedValidationMapOutputs inputLength raw output)))
  exact linkFuel_polyBounded (second := preserveRightProgram nativeNatEqProgram)
    (polyBounded_const 7 measure degree)
    (preserveRightFuel_polyBounded
      (nativeNatEqFuel_polyBounded' hcountWidth hlength))

def balancedValidationAllCheckedTailCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan
      (linkPrograms balancedValidationAllEqualityProgram
        balancedValidationAllGateProgram) + 5 +
      balancedValidationAllCountCoefficient coefficient +
    (programRegisterSpan balancedValidationAllGateProgram + 5 +
        balancedValidationAllEqualityCoefficient coefficient +
      balancedValidationAllGateFuel)

theorem balancedValidationAllCheckedTailFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ} {output : ℕ → ℕ}
    (hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure coefficient
        degree) :
    PolyBounded (balancedValidationAllCheckedTailFuel inputLength raw output)
      measure (balancedValidationAllCheckedTailCoefficient coefficient)
      degree := by
  have hgate :=
    linkFuel_polyBounded (second := balancedValidationAllGateProgram)
      (balancedValidationAllEqualityFuel_polyBounded (inputLength := inputLength)
      (output := output) hcount)
      (polyBounded_const balancedValidationAllGateFuel measure degree)
  exact linkFuel_polyBounded
    (second :=
      linkPrograms balancedValidationAllEqualityProgram
        balancedValidationAllGateProgram)
    (balancedValidationAllCountFuel_polyBounded (inputLength := inputLength)
      (output := output) hcount) hgate

/-- The coefficient one counted summary produces from its map's coefficient and
the shared count coefficient. -/
def balancedValidationSummaryCoefficient
    (mapCoefficient countCoefficient : ℕ) : ℕ :=
  programRegisterSpan
      (linkPrograms balancedValidationAllLengthProgram <|
        linkPrograms balancedValidationSummaryPrepareProgram <|
          linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram) + 5 + mapCoefficient +
    (programRegisterSpan
        (linkPrograms balancedValidationSummaryPrepareProgram <|
          linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram) + 5 +
        balancedValidationAllLengthCoefficient countCoefficient +
      (programRegisterSpan
          (linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram) + 5 + 9 +
        (programRegisterSpan balancedValidationSummaryGateProgram + 5 +
            (balancedValidationAllCheckedTailCoefficient countCoefficient + 4) +
          6)))

/-- **The counted summary, dominated.**  Degree-preserving over its map. -/
theorem balancedValidationSummaryFuel_polyBounded
    {callee : NPOracleProgram} {calleeFuel output : ℕ → ℕ}
    {inputLength raw measure mapCoefficient countCoefficient degree : ℕ}
    (hmap :
      PolyBounded (balancedValidationMapFuel callee calleeFuel inputLength raw)
        measure mapCoefficient degree)
    (hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure
        countCoefficient degree) :
    PolyBounded
      (balancedValidationSummaryFuel callee calleeFuel inputLength raw output)
      measure
      (balancedValidationSummaryCoefficient mapCoefficient countCoefficient)
      degree := by
  have hchecked :
      PolyBounded (balancedValidationSummaryCheckedFuel inputLength raw output)
        measure
        (balancedValidationAllCheckedTailCoefficient countCoefficient + 4)
        degree :=
    preserveRightFuel_polyBounded
      (balancedValidationAllCheckedTailFuel_polyBounded (inputLength := inputLength)
        (output := output) hcount)
  have hgate :=
    linkFuel_polyBounded (second := balancedValidationSummaryGateProgram)
      hchecked (polyBounded_const 6 measure degree)
  have hprepare :=
    linkFuel_polyBounded
      (second :=
        linkPrograms balancedValidationSummaryCheckedProgram
          balancedValidationSummaryGateProgram)
      (polyBounded_const 9 measure degree) hgate
  have hlength :=
    linkFuel_polyBounded
      (second :=
        linkPrograms balancedValidationSummaryPrepareProgram <|
          linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram)
      (balancedValidationAllLengthFuel_polyBounded (inputLength := inputLength)
        (output := output) hcount)
      hprepare
  exact linkFuel_polyBounded
    (second :=
      linkPrograms balancedValidationAllLengthProgram <|
        linkPrograms balancedValidationSummaryPrepareProgram <|
          linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram)
    hmap hlength

private theorem flatMap_map_streamOfCode (streams : List (List ℕ)) :
    (streams.map encodeTaggedList).flatMap
        BalancedClauseStreamFlattenProgram.streamOfCode = streams.flatten := by
  induction streams with
  | nil => simp
  | cons head tail inductionHypothesis => simp [inductionHypothesis]

theorem balancedBitSingletonFuel_le (bits : List ℕ) :
    balancedBitSingletonFuel bits ≤ 74 * bits.length + 37 := by
  have hsteps := balancedTraversalStructuralSteps_le_linear bits
  unfold balancedBitSingletonFuel
  omega

theorem balancedClauseStreamFlattenFuel_le (streams : List (List ℕ)) :
    BalancedClauseStreamFlattenProgram.balancedClauseStreamFlattenFuel streams ≤
      32 * streams.length + 16 * streams.flatten.length + 23 := by
  have hphase :=
    phaseFuel_le [balancedTraversalTree (streams.map encodeTaggedList)]
  have hnodes := balancedTraversalTree_nodeCount_le (streams.map encodeTaggedList)
  have hstream :
      (BalancedClauseStreamFlattenProgram.forestStreamValues
        [balancedTraversalTree (streams.map encodeTaggedList)]).length =
        streams.flatten.length := by
    have hatoms := balancedTraversalTree_atoms (streams.map encodeTaggedList)
    simp only [BalancedClauseStreamFlattenProgram.forestStreamValues,
      BalancedClauseStreamFlattenProgram.treeStreamValues, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hatoms]
    exact congrArg List.length (flatMap_map_streamOfCode streams)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hstream, List.length_map] at hphase hnodes
  have hdef :
      BalancedClauseStreamFlattenProgram.balancedClauseStreamFlattenFuel
          streams =
        BalancedClauseStreamFlattenProgram.phaseFuel
            [balancedTraversalTree (streams.map encodeTaggedList)] +
          8 * streams.flatten.length + 7 := rfl
  rw [hdef]
  omega

private theorem flatten_map_singleton (bits : List ℕ) :
    (bits.map fun bit => [bit]).flatten = bits := by
  induction bits with
  | nil => simp
  | cons bit rest inductionHypothesis => simp [inductionHypothesis]

theorem balancedBitsToTaggedFuel_le (bits : List ℕ) :
    balancedBitsToTaggedFuel bits ≤
      programRegisterSpan BalancedClauseStreamFlattenProgram.balancedClauseStreamFlattenProgram +
        5 + (74 * bits.length + 37) + (48 * bits.length + 23) := by
  have hsingleton := balancedBitSingletonFuel_le bits
  have hflatten := balancedClauseStreamFlattenFuel_le (bits.map fun bit => [bit])
  rw [flatten_map_singleton bits] at hflatten
  simp only [List.length_map] at hflatten
  unfold balancedBitsToTaggedFuel linkFuel
  omega

/-- The coefficient the bit-stream re-tagger produces. -/
def balancedBitsToTaggedCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan
      BalancedClauseStreamFlattenProgram.balancedClauseStreamFlattenProgram + 5 +
      (74 * coefficient + 37) +
    (48 * coefficient + 23)

theorem balancedBitsToTaggedFuel_polyBounded
    {bits : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded bits.length measure coefficient degree) :
    PolyBounded (balancedBitsToTaggedFuel bits) measure
      (balancedBitsToTaggedCoefficient coefficient) degree := by
  have hsingleton :
      PolyBounded (74 * bits.length + 37) measure (74 * coefficient + 37)
        degree :=
    (hlength.const_mul 74).add (polyBounded_const 37 measure degree)
  have hflatten :
      PolyBounded (48 * bits.length + 23) measure (48 * coefficient + 23)
        degree :=
    (hlength.const_mul 48).add (polyBounded_const 23 measure degree)
  have hsum :=
    ((polyBounded_const
      (programRegisterSpan
        BalancedClauseStreamFlattenProgram.balancedClauseStreamFlattenProgram +
          5) measure degree).add hsingleton).add hflatten
  exact hsum.mono
    ((balancedBitsToTaggedFuel_le bits).trans (by omega))

/-- The coefficient the canonical bit decoder produces. -/
def canonicalNatDecodeListCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan taggedBitFoldProgram + 5 +
      balancedBitsToTaggedCoefficient coefficient +
    (7 * coefficient + 5)

theorem canonicalNatDecodeListFuel_polyBounded
    {bits : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded bits.length measure coefficient degree) :
    PolyBounded (canonicalNatDecodeListFuel bits) measure
      (canonicalNatDecodeListCoefficient coefficient) degree := by
  have hfold :
      PolyBounded (taggedBitFoldFuel bits) measure (7 * coefficient + 5)
        degree :=
    ((hlength.const_mul 7).add (polyBounded_const 5 measure degree)).mono
      (taggedBitFoldFuel_le bits)
  exact linkFuel_polyBounded (second := taggedBitFoldProgram)
    (balancedBitsToTaggedFuel_polyBounded hlength) hfold

/-! ### The folded value's width -/

private theorem taggedBitFoldValue_le (bits : List ℕ) :
    ∀ accumulator place : ℕ,
      taggedBitFoldValue bits accumulator place + place ≤
        accumulator + place * 2 ^ bits.length := by
  induction bits with
  | nil =>
      intro accumulator place
      simp [taggedBitFoldValue]
  | cons bit rest inductionHypothesis =>
      intro accumulator place
      have hstep :=
        inductionHypothesis
          (if bit = 0 then accumulator else accumulator + place)
          (place + place)
      have hbranch :
          (if bit = 0 then accumulator else accumulator + place) ≤
            accumulator + place := by
        split <;> omega
      have hpow :
          (2 : ℕ) ^ (rest.length + 1) = 2 ^ rest.length + 2 ^ rest.length := by
        rw [Nat.pow_succ]
        ring
      have harith :
          (place + place) * 2 ^ rest.length =
            place * (2 ^ rest.length + 2 ^ rest.length) := by ring
      simp only [taggedBitFoldValue, List.length_cons]
      rw [hpow]
      omega

theorem natBitLength_canonicalNatCandidate_le (raw : ℕ) :
    natBitLength (canonicalNatCandidate raw) ≤
      (rawBalancedTraversalTree raw).atoms.length + 1 := by
  have hbound := taggedBitFoldValue_le (rawBalancedTraversalTree raw).atoms 0 1
  have hvalue :
      canonicalNatCandidate raw <
        2 ^ (rawBalancedTraversalTree raw).atoms.length := by
    unfold canonicalNatCandidate
    omega
  rcases Nat.eq_zero_or_pos (canonicalNatCandidate raw) with hzero | hpositive
  · rw [hzero, natBitLength_zero]
    omega
  · have hlog :
        Nat.log 2 (canonicalNatCandidate raw) <
          (rawBalancedTraversalTree raw).atoms.length :=
      Nat.log_lt_of_lt_pow (by omega) hvalue
    unfold natBitLength
    omega

private theorem bitsLength_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

/-- **The canonical re-encoding's width is linear in the code's width.**  This
is where the quadratic-shallowness lemma is spent: the re-encoding costs a
quadratic in the folded value's bit count, and the bit count's *square* is
already capped by the code's width. -/
theorem natBitLength_encodeNat_canonicalNatCandidate_le (raw : ℕ) :
    natBitLength (encodeNat (canonicalNatCandidate raw)) ≤
      512 * natBitLength raw := by
  have hbits :
      (canonicalNatCandidate raw).bits.length ≤
        (rawBalancedTraversalTree raw).atoms.length + 1 :=
    (bitsLength_le_natBitLength (canonicalNatCandidate raw)).trans
      (natBitLength_canonicalNatCandidate_le raw)
  have hmembers :
      ∀ value ∈ (canonicalNatCandidate raw).bits.map boolCode,
        natBitLength value ≤ 1 := by
    intro value hvalue
    rw [List.mem_map] at hvalue
    obtain ⟨bit, _, rfl⟩ := hvalue
    cases bit
    · rw [show boolCode false = 0 from rfl, natBitLength_zero]
    · rw [show boolCode true = 1 from rfl, natBitLength_one]
  have hquadratic :=
    natBitLength_encodeBalancedList_le_quadratic
      ((canonicalNatCandidate raw).bits.map boolCode) 1 (le_refl 1) hmembers
  have hcode :
      encodeNat (canonicalNatCandidate raw) =
        encodeBalancedList ((canonicalNatCandidate raw).bits.map boolCode) :=
    rfl
  rw [hcode]
  simp only [List.length_map, Nat.mul_one] at hquadratic
  have hstep :
      (canonicalNatCandidate raw).bits.length + 1 ≤
        2 * ((rawBalancedTraversalTree raw).atoms.length + 1) := by omega
  have hpow :
      ((canonicalNatCandidate raw).bits.length + 1) ^ 2 ≤
        (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)) ^ 2 :=
    Nat.pow_le_pow_left hstep 2
  have hexpand :
      (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)) ^ 2 =
        4 * ((rawBalancedTraversalTree raw).atoms.length + 1) ^ 2 := by ring
  have hsquare := rawBalancedTraversalTree_atoms_length_sq_le raw
  omega

/-! ### The composite -/

/-- The coefficient the raw canonicalizer produces. -/
def balancedRawCanonicalizeCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan balancedCanonicalizeProgram + 5 + (35 * coefficient + 2) +
    (programRegisterSpan taggedToBalancedProgram + 5 +
        (programRegisterSpan balancedClauseStreamFlattenProgram + 5 +
            (39 * coefficient + 2) +
          (32 * coefficient + 7)) +
      (42 * coefficient + 14))

def canonicalNatCandidateCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan canonicalNatDecodeProgram + 5 +
      balancedRawCanonicalizeCoefficient (2 * coefficient) +
    canonicalNatDecodeListCoefficient (2 * coefficient)

theorem canonicalNatCandidateFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (canonicalNatCandidateFuel raw) measure
      (canonicalNatCandidateCoefficient coefficient) degree := by
  have hnodes := polyBounded_rawBalancedTraversalTree_nodeCount hraw
  have hatoms :
      PolyBounded (rawBalancedTraversalTree raw).atoms.length measure
        (2 * coefficient) degree := by
    refine (hraw.const_mul 2).mono ?_
    have := rawBalancedTraversalTree_atoms_length_succ_le raw
    omega
  exact linkFuel_polyBounded (second := canonicalNatDecodeProgram)
    (balancedRawCanonicalizeFuel_polyBounded hnodes)
    (canonicalNatDecodeListFuel_polyBounded hatoms)

def candidateWithRawCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan (preserveRightProgram canonicalNatCandidateProgram) + 5 +
      2 +
    (canonicalNatCandidateCoefficient coefficient + 4)

theorem candidateWithRawFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (candidateWithRawFuel raw) measure
      (candidateWithRawCoefficient coefficient) degree :=
  linkFuel_polyBounded (second := preserveRightProgram canonicalNatCandidateProgram)
    (polyBounded_const 2 measure degree)
    (preserveRightFuel_polyBounded (canonicalNatCandidateFuel_polyBounded hraw))

def canonicalNatEqualityCoefficient (coefficient : ℕ) : ℕ :=
  nativeNatEqCoefficient (512 * coefficient) coefficient + 4

theorem canonicalNatEqualityFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (canonicalNatEqualityFuel raw) measure
      (canonicalNatEqualityCoefficient coefficient) degree := by
  have hreencode :
      PolyBounded (natBitLength (encodeNat (canonicalNatCandidate raw))) measure
        (512 * coefficient) degree :=
    (hraw.const_mul 512).mono
      (natBitLength_encodeNat_canonicalNatCandidate_le raw)
  exact preserveRightFuel_polyBounded
    (nativeNatEqFuel_polyBounded' hreencode hraw)

/-- The coefficient the canonical natural validator produces. -/
def canonicalNatValidationCoefficient (coefficient : ℕ) : ℕ :=
  programRegisterSpan canonicalNatValidationGateProgram + 5 +
      (programRegisterSpan canonicalNatEqualityProgram + 5 +
          (programRegisterSpan canonicalNatEqualityPrepareProgram + 5 +
              candidateWithRawCoefficient coefficient + 6) +
        canonicalNatEqualityCoefficient coefficient) +
    6

/-- **The canonical natural validator, dominated — at the anchor's own
degree.** -/
theorem canonicalNatValidationFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (canonicalNatValidationFuel raw) measure
      (canonicalNatValidationCoefficient coefficient) degree := by
  have hprepare :=
    linkFuel_polyBounded (second := canonicalNatEqualityPrepareProgram)
      (candidateWithRawFuel_polyBounded hraw)
      (polyBounded_const 6 measure degree)
  have hequality :=
    linkFuel_polyBounded (second := canonicalNatEqualityProgram) hprepare
      (canonicalNatEqualityFuel_polyBounded hraw)
  exact linkFuel_polyBounded (second := canonicalNatValidationGateProgram)
    hequality (polyBounded_const 6 measure degree)

/-! ### Field widths of a fixed-arity tagged tuple -/

private theorem decodeTaggedTupleAux_natBitLength_le :
    ∀ (arity cursor accumulator fields : ℕ),
      decodeTaggedTupleAux arity cursor accumulator = some fields →
        natBitLength fields ≤
          2 ^ arity * max (natBitLength accumulator) (natBitLength cursor) := by
  intro arity
  induction arity with
  | zero =>
      intro cursor accumulator fields hdecode
      simp only [decodeTaggedTupleAux] at hdecode
      split at hdecode
      · simp only [Option.some.injEq] at hdecode
        subst hdecode
        simp only [Nat.pow_zero, Nat.one_mul]
        exact le_max_left _ _
      · simp at hdecode
  | succ remaining inductionHypothesis =>
      intro cursor accumulator fields hdecode
      simp only [decodeTaggedTupleAux] at hdecode
      split at hdecode
      · simp at hdecode
      · split at hdecode
        · have hstep := inductionHypothesis _ _ _ hdecode
          have houter : (Nat.unpair cursor).2 ≤ cursor := Nat.unpair_right_le _
          have hleft :
              (Nat.unpair (Nat.unpair cursor).2).1 ≤ cursor :=
            (Nat.unpair_left_le _).trans houter
          have hright :
              (Nat.unpair (Nat.unpair cursor).2).2 ≤ cursor :=
            (Nat.unpair_right_le _).trans houter
          have hpair :=
            pairCodeBits_le accumulator (Nat.unpair (Nat.unpair cursor).2).1
          have hleftWidth :
              natBitLength (Nat.unpair (Nat.unpair cursor).2).1 ≤
                natBitLength cursor := natBitLength_mono hleft
          have hrightWidth :
              natBitLength (Nat.unpair (Nat.unpair cursor).2).2 ≤
                natBitLength cursor := natBitLength_mono hright
          have hpow : (2 : ℕ) ^ (remaining + 1) = 2 * 2 ^ remaining := by
            rw [Nat.pow_succ]
            ring
          have hpositive : 1 ≤ (2 : ℕ) ^ remaining := Nat.one_le_pow _ _ (by omega)
          have hmax :
              max
                  (natBitLength
                    (Nat.pair accumulator (Nat.unpair (Nat.unpair cursor).2).1))
                  (natBitLength (Nat.unpair (Nat.unpair cursor).2).2) ≤
                2 * max (natBitLength accumulator) (natBitLength cursor) := by
            have hone := one_le_natBitLength accumulator
            have htwo := one_le_natBitLength cursor
            refine Nat.max_le.2 ⟨?_, ?_⟩ <;> omega
          have hscale :
              2 ^ remaining *
                  max
                    (natBitLength
                      (Nat.pair accumulator
                        (Nat.unpair (Nat.unpair cursor).2).1))
                    (natBitLength (Nat.unpair (Nat.unpair cursor).2).2) ≤
                2 ^ remaining *
                  (2 * max (natBitLength accumulator) (natBitLength cursor)) :=
            Nat.mul_le_mul_left _ hmax
          have hrewrite :
              2 ^ remaining *
                  (2 * max (natBitLength accumulator) (natBitLength cursor)) =
                2 ^ (remaining + 1) *
                  max (natBitLength accumulator) (natBitLength cursor) := by
            rw [hpow]
            ring
          omega
        · simp at hdecode

theorem natBitLength_taggedTupleOutput_le (arity raw : ℕ) :
    natBitLength (taggedTupleOutput arity raw) ≤
      2 * (2 ^ arity * natBitLength raw) := by
  have hraw := one_le_natBitLength raw
  have hpositive : 1 ≤ (2 : ℕ) ^ arity := Nat.one_le_pow _ _ (by omega)
  unfold taggedTupleOutput
  cases hdecode : decodeTaggedTuple arity raw with
  | none =>
      simp only [natBitLength_zero]
      have : 1 ≤ 2 ^ arity * natBitLength raw :=
        Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
  | some fields =>
      have hfields :=
        decodeTaggedTupleAux_natBitLength_le arity raw 0 fields hdecode
      have hzero : natBitLength 0 = 1 := natBitLength_zero
      have hmax : max (natBitLength 0) (natBitLength raw) = natBitLength raw := by
        rw [hzero]
        omega
      rw [hmax] at hfields
      have hpair := pairCodeBits_le 1 fields
      have hone : natBitLength 1 = 1 := natBitLength_one
      have hscale : natBitLength raw ≤ 2 ^ arity * natBitLength raw :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only []
      omega

/-! ### The rational validator's chain -/

def rationalChainTail₇ : NPOracleProgram := rationalValidationGateProgram

def rationalChainTail₆ : NPOracleProgram :=
  linkPrograms rationalGcdStageProgram rationalChainTail₇

def rationalChainTail₅ : NPOracleProgram :=
  linkPrograms rationalGcdLoweringProgram rationalChainTail₆

def rationalChainTail₄ : NPOracleProgram :=
  linkPrograms rationalDenominatorStageProgram rationalChainTail₅

def rationalChainTail₃ : NPOracleProgram :=
  linkPrograms rationalDenominatorLoweringProgram rationalChainTail₄

def rationalChainTail₂ : NPOracleProgram :=
  linkPrograms rationalMagnitudeStageProgram rationalChainTail₃

def rationalChainTail₁ : NPOracleProgram :=
  linkPrograms rationalProjectionProgram rationalChainTail₂

/-! ### The three data-dependent stages -/

theorem rationalMagnitudeCode_le (raw : ℕ) :
    rationalMagnitudeCode raw ≤ rationalTupleOutput raw := by
  refine (Nat.unpair_right_le _).trans ?_
  refine (Nat.unpair_right_le _).trans ?_
  refine (Nat.unpair_left_le _).trans ?_
  exact Nat.unpair_right_le _

theorem rationalDenominatorCode_le (raw : ℕ) :
    rationalDenominatorCode raw ≤ rationalTupleOutput raw := by
  refine (Nat.unpair_right_le _).trans ?_
  exact Nat.unpair_right_le _

theorem rationalMagnitudeValue_le (raw : ℕ) :
    rationalMagnitudeValue raw ≤
      canonicalNatCandidate (rationalMagnitudeCode raw) := by
  simp only [rationalMagnitudeValue, rationalMagnitudeValidation,
    canonicalNatValidationOutput]
  split
  · simp
  · simp

theorem rationalDenominatorValue_le (raw : ℕ) :
    rationalDenominatorValue raw ≤
      canonicalNatCandidate (rationalDenominatorCode raw) := by
  simp only [rationalDenominatorValue, rationalDenominatorValidation,
    canonicalNatValidationOutput]
  split
  · simp
  · simp

/-- The gcd operands' widths, from the tuple output's. -/
theorem natBitLength_rationalMagnitudeValue_le (raw : ℕ) :
    natBitLength (rationalMagnitudeValue raw) ≤
      2 * natBitLength (rationalTupleOutput raw) := by
  have hvalue := natBitLength_mono (rationalMagnitudeValue_le raw)
  have hcandidate :=
    natBitLength_canonicalNatCandidate_le (rationalMagnitudeCode raw)
  have hatoms :=
    rawBalancedTraversalTree_atoms_length_succ_le (rationalMagnitudeCode raw)
  have hcode :=
    natBitLength_mono (rationalMagnitudeCode_le raw)
  omega

theorem natBitLength_rationalDenominatorValue_le (raw : ℕ) :
    natBitLength (rationalDenominatorValue raw) ≤
      2 * natBitLength (rationalTupleOutput raw) := by
  have hvalue := natBitLength_mono (rationalDenominatorValue_le raw)
  have hcandidate :=
    natBitLength_canonicalNatCandidate_le (rationalDenominatorCode raw)
  have hatoms :=
    rawBalancedTraversalTree_atoms_length_succ_le (rationalDenominatorCode raw)
  have hcode :=
    natBitLength_mono (rationalDenominatorCode_le raw)
  omega

/-- **The gcd stage, dominated at degree `2d`.**  Iteration count times
per-iteration charge: two width-linear factors. -/
theorem rationalGcdStageFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded (natBitLength (rationalTupleOutput raw)) measure coefficient
        degree) :
    PolyBounded (rationalGcdStageFuel raw) measure
      ((2 * (2 * coefficient) + 2) *
          (19 + gcdCalleeSpan + 13 * (2 * coefficient)) + 5 + 4)
      (degree + degree) := by
  set bound :=
    max (rationalMagnitudeValue raw) (rationalDenominatorValue raw) with hbound
  have hleft : rationalMagnitudeValue raw ≤ bound := le_max_left _ _
  have hright : rationalDenominatorValue raw ≤ bound := le_max_right _ _
  have hboundWidth :
      PolyBounded (natBitLength bound) measure (2 * coefficient) degree := by
    refine (hwidth.const_mul 2).mono ?_
    have hmagnitude := natBitLength_rationalMagnitudeValue_le raw
    have hdenominator := natBitLength_rationalDenominatorValue_le raw
    rcases Nat.le_total (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw) with hle | hle
    · rw [hbound, Nat.max_eq_right hle]
      omega
    · rw [hbound, Nat.max_eq_left hle]
      omega
  have hrounds :
      PolyBounded (2 * natBitLength bound + 2) measure
        (2 * (2 * coefficient) + 2) degree :=
    (hboundWidth.const_mul 2).add (polyBounded_const 2 measure degree)
  have hcharge :
      PolyBounded (canonicalGcdStepCharge bound) measure
        (19 + gcdCalleeSpan + 13 * (2 * coefficient)) degree := by
    refine ((polyBounded_const (19 + gcdCalleeSpan) measure degree).add
      (hboundWidth.const_mul 13)).mono ?_
    unfold canonicalGcdStepCharge
    omega
  have hproduct := hrounds.mul hcharge
  have hgcd :
      PolyBounded
        (canonicalGcdFuel (rationalMagnitudeValue raw)
          (rationalDenominatorValue raw)) measure
        ((2 * (2 * coefficient) + 2) *
          (19 + gcdCalleeSpan + 13 * (2 * coefficient)) + 5)
        (degree + degree) :=
    (hproduct.add (polyBounded_const 5 measure (degree + degree))).mono
      (canonicalGcdFuel_le bound (rationalMagnitudeValue raw)
        (rationalDenominatorValue raw) hleft hright)
  exact preserveRightFuel_polyBounded hgcd

/-- The coefficient the rational validator produces. -/
def rationalValidationCoefficient
    (magnitudeCoefficient denominatorCoefficient gcdCoefficient : ℕ) : ℕ :=
  programRegisterSpan rationalChainTail₁ + 5 + rationalTupleFuel +
    (programRegisterSpan rationalChainTail₂ + 5 + rationalProjectionFuel +
      (programRegisterSpan rationalChainTail₃ + 5 + magnitudeCoefficient +
        (programRegisterSpan rationalChainTail₄ + 5 +
            rationalDenominatorLoweringFuel +
          (programRegisterSpan rationalChainTail₅ + 5 +
              denominatorCoefficient +
            (programRegisterSpan rationalChainTail₆ + 5 +
                rationalGcdLoweringFuel +
              (programRegisterSpan rationalChainTail₇ + 5 + gcdCoefficient +
                rationalValidationGateFuel))))))

/-- **The rational validator, dominated at degree `2d`.** -/
theorem rationalValidationFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded (natBitLength (rationalTupleOutput raw)) measure coefficient
        degree) :
    PolyBounded (rationalValidationFuel inputLength raw) measure
      (rationalValidationCoefficient
        (canonicalNatValidationCoefficient coefficient + 4)
        (canonicalNatValidationCoefficient coefficient + 4)
        ((2 * (2 * coefficient) + 2) *
            (19 + gcdCalleeSpan + 13 * (2 * coefficient)) + 5 + 4))
      (degree + degree) := by
  have hraise : degree ≤ degree + degree := by omega
  have hmagnitudeWidth :
      PolyBounded (natBitLength (rationalMagnitudeCode raw)) measure coefficient
        degree :=
    hwidth.mono (natBitLength_mono (rationalMagnitudeCode_le raw))
  have hdenominatorWidth :
      PolyBounded (natBitLength (rationalDenominatorCode raw)) measure
        coefficient degree :=
    hwidth.mono (natBitLength_mono (rationalDenominatorCode_le raw))
  have hmagnitude :
      PolyBounded (rationalMagnitudeStageFuel raw) measure
        (canonicalNatValidationCoefficient coefficient + 4)
        (degree + degree) :=
    (preserveRightFuel_polyBounded
      (canonicalNatValidationFuel_polyBounded hmagnitudeWidth)).degree_mono
      hraise
  have hdenominator :
      PolyBounded (rationalDenominatorStageFuel raw) measure
        (canonicalNatValidationCoefficient coefficient + 4)
        (degree + degree) :=
    (preserveRightFuel_polyBounded
      (canonicalNatValidationFuel_polyBounded hdenominatorWidth)).degree_mono
      hraise
  have hgcd := rationalGcdStageFuel_polyBounded hwidth
  have node₇ :=
    linkFuel_polyBounded (second := rationalChainTail₇) hgcd
      (polyBounded_const rationalValidationGateFuel measure (degree + degree))
  have node₆ :=
    linkFuel_polyBounded (second := rationalChainTail₆)
      (polyBounded_const rationalGcdLoweringFuel measure (degree + degree))
      node₇
  have node₅ :=
    linkFuel_polyBounded (second := rationalChainTail₅) hdenominator node₆
  have node₄ :=
    linkFuel_polyBounded (second := rationalChainTail₄)
      (polyBounded_const rationalDenominatorLoweringFuel measure
        (degree + degree))
      node₅
  have node₃ :=
    linkFuel_polyBounded (second := rationalChainTail₃) hmagnitude node₄
  have node₂ :=
    linkFuel_polyBounded (second := rationalChainTail₂)
      (polyBounded_const rationalProjectionFuel measure (degree + degree)) node₃
  exact linkFuel_polyBounded (second := rationalChainTail₁)
    (polyBounded_const rationalTupleFuel measure (degree + degree)) node₂

/-- **The deepest admissible path.**  Anchor degree `1`, guard degree `2`,
callee degree `3` — the counted summary lands at exactly `4`. -/
theorem balancedValidationSummaryFuel_degree_four
    {callee : NPOracleProgram} {calleeFuel output : ℕ → ℕ}
    {inputLength raw measure widthCoefficient calleeCoefficient bound : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure widthCoefficient 1)
    (hcallee : PolyBounded bound measure calleeCoefficient 3)
    (hbound : ∀ request ∈ balancedValidationMapRequests inputLength raw,
      calleeFuel request ≤ bound) :
    ∃ coefficient : ℕ,
      PolyBounded
        (balancedValidationSummaryFuel callee calleeFuel inputLength raw output)
        measure coefficient 4 := by
  obtain ⟨guardCoefficient, hguard⟩ :=
    balancedValidationMapGuardFuel_degree hraw
  have hguardFour :
      PolyBounded (balancedValidationMapGuardFuel raw) measure guardCoefficient
        4 := hguard.degree_mono (by omega)
  have hmap :=
    balancedValidationMapFuel_polyBounded_of_width (callee := callee)
      (calleeFuel := calleeFuel) (inputLength := inputLength) hraw hguardFour
      hcallee hbound (by omega) (by omega)
  have hcount :
      PolyBounded (balancedValidationMapCodes raw).length measure
        (2 * widthCoefficient) 4 :=
    (polyBounded_balancedValidationMapCodes_length hraw).degree_mono (by omega)
  exact ⟨_, balancedValidationSummaryFuel_polyBounded (output := output) hmap
    hcount⟩

/-- The same ledger for a counted *map*. -/
theorem balancedValidationMapFuel_degree_four
    {callee : NPOracleProgram} {calleeFuel : ℕ → ℕ}
    {inputLength raw measure widthCoefficient calleeCoefficient bound : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure widthCoefficient 1)
    (hcallee : PolyBounded bound measure calleeCoefficient 3)
    (hbound : ∀ request ∈ balancedValidationMapRequests inputLength raw,
      calleeFuel request ≤ bound) :
    ∃ coefficient : ℕ,
      PolyBounded (balancedValidationMapFuel callee calleeFuel inputLength raw)
        measure coefficient 4 := by
  obtain ⟨guardCoefficient, hguard⟩ :=
    balancedValidationMapGuardFuel_degree hraw
  exact ⟨_,
    balancedValidationMapFuel_polyBounded_of_width (callee := callee)
      (calleeFuel := calleeFuel) (inputLength := inputLength) hraw
      (hguard.degree_mono (by omega)) hcallee hbound (by omega) (by omega)⟩

/-- **The canonical natural validator sits at the anchor's degree.**  At the
anchor `d = 1` this is degree `1`: two counted combinators of headroom
remain. -/
theorem canonicalNatValidationFuel_degree_one
    {raw measure coefficient : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient 1) :
    PolyBounded (canonicalNatValidationFuel raw) measure
      (canonicalNatValidationCoefficient coefficient) 1 :=
  canonicalNatValidationFuel_polyBounded hraw

theorem rationalValidationFuel_degree_two
    {inputLength raw measure coefficient : ℕ}
    (hwidth :
      PolyBounded (natBitLength (rationalTupleOutput raw)) measure coefficient
        1) :
    ∃ validationCoefficient : ℕ,
      PolyBounded (rationalValidationFuel inputLength raw) measure
        validationCoefficient 2 :=
  ⟨_, rationalValidationFuel_polyBounded hwidth⟩

/-- The coefficient the validator's three-node spine produces from one uniform
stage coefficient.  Never evaluated: the three spans are closed naturals over
whole linked programs. -/
def recoveryValidatorSpineCoefficient (stageCoefficient : ℕ) : ℕ :=
  programRegisterSpan recoveryValidatorModeRawProgram + 5 +
      (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationProgram + 5 +
            stageCoefficient + stageCoefficient) +
        stageCoefficient) +
    stageCoefficient

/-- **Both validator premises, at `recoveryVerifierDegree`.**  This is exactly
the pair `RecoveryVerifierResourceEnvelope.executableRecoveryMachineOfComponents`
consumes, at one coefficient, with the degree numeral already the machine's
own. -/
theorem hvalidator_at_recoveryVerifierDegree
    (limitsOf : ℕ → RecoveryWitnessLimits) (frontier stageCoefficient : ℕ)
    (hcoefficientFuel :
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
    (hcoefficientBits :
      (max frontier <|
        max (max frontier (16 * frontier)) <|
          max (max (max frontier (4 * frontier)) frontier) <|
            max frontier (max frontier (2 * frontier))) ≤ stageCoefficient)
    (hcircuit : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness)))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier recoveryVerifierDegree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier recoveryVerifierDegree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hlength : ∀ request : WeakVerifierRequest,
      PolyBounded (natBitLength (WeakVerifierRequest.length request))
        request.measure frontier recoveryVerifierDegree)
    (hprefix : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorPrefixWidth (limitsOf request.inputArity)
          (encodeBitInput request.witness)) request.measure frontier
        recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeBits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request) (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree) :
    (∀ request : WeakVerifierRequest,
      recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
        polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
            (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
          polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure :=
  hvalidator_of_stageFrontier limitsOf stageCoefficient recoveryVerifierDegree
    le_rfl
    (fun request =>
      recoveryValidatorMaximumStageFuel_polyBounded_uniform hcoefficientFuel
        (hcircuit request) (hresult request) (hhandoff request)
        (henvelopeFuel request))
    (fun request =>
      recoveryValidatorMaximumStageBits_polyBounded_uniform hcoefficientBits
        (hlength request) (hprefix request) (hstage request) (hcall request)
        (henvelopeBits request) (hmode request))

/-! ## §9 The machine-level corollary

With both premises delivered at `recoveryVerifierDegree` and at one coefficient,
`executableRecoveryMachineOfComponents` is applicable: the validator side of the
machine's resource ledger is *supplied*, not assumed.  Only the limits front end
and the semantic stage remain as the caller's obligations, exactly as
`RecoveryVerifierResourceEnvelope` intends. -/

/-- **The executable recovery machine, with its validator budget discharged.**
`validatorCoefficient` is the validator spine's own coefficient and the degree
numeral is the machine's published `recoveryVerifierDegree`. -/
def executableRecoveryMachineOfValidatorFrontier
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode : ∀ request : WeakVerifierRequest,
      runNPOracleProgram limitsCodeProgram (limitsCodeBits request)
          (limitsCodeFuel request)
          (initialNPOracleState (WeakVerifierRequest.length request)
            (encodeBitInput request.witness)) =
        some (encodeRecoveryWitnessLimits (limitsOf request.inputArity)))
    (hsemanticStage : ∀ request : WeakVerifierRequest,
      runNPOracleProgram semanticStage (semanticBits request)
          (semanticFuel request)
          (initialNPOracleState (WeakVerifierRequest.length request)
            (recoveryWitnessValidatorRequestOutput
              (limitsOf request.inputArity) request)) =
        some (semanticOutput request))
    (hfrontEndBits : ∀ request : WeakVerifierRequest,
      recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          request.measure)
    (hsemanticBits : ∀ request : WeakVerifierRequest,
      semanticBits request ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          request.measure)
    (hfrontEndFuel : ∀ request : WeakVerifierRequest,
      recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
          request ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          request.measure)
    (hsemanticFuel : ∀ request : WeakVerifierRequest,
      semanticFuel request ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          request.measure)
    (hvalidator :
      (∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
            (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
          polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure) ∧
        ∀ request : WeakVerifierRequest,
          recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
              (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
            polynomialBudget
              (recoveryValidatorSpineCoefficient stageCoefficient)
              recoveryVerifierDegree request.measure)
    (hlimitsCodeFree : OracleFree limitsCodeProgram)
    (hsemanticFree : OracleFree semanticStage) :
    ExecutableWeakNondeterministicMachine :=
  executableRecoveryMachineOfComponents limitsOf limitsCodeProgram semanticStage
    limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput
    frontEndCoefficient (recoveryValidatorSpineCoefficient stageCoefficient)
    semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits hvalidator.1
    hsemanticBits hfrontEndFuel hvalidator.2 hsemanticFuel hlimitsCodeFree
    hsemanticFree

/-- The assembled machine charges at the published degree. -/
theorem executableRecoveryMachineOfValidatorFrontier_verifier_degree
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfValidatorFrontier limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient semanticCoefficient stageCoefficient
        hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
        hsemanticFuel hvalidator hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

/-- The assembled machine's witness shape is the recovery shape. -/
theorem executableRecoveryMachineOfValidatorFrontier_witnessShape
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfValidatorFrontier limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient semanticCoefficient stageCoefficient
        hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
        hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

theorem balancedFoldLeafSteps_le
    (step leafSteps : ℕ → ℕ → ℕ) (bound : ℕ)
    (hbound : ∀ accumulator atom, leafSteps accumulator atom ≤ bound) :
    ∀ (accumulator : ℕ) (atoms : List ℕ),
      balancedFoldLeafSteps step leafSteps accumulator atoms ≤
        atoms.length * bound := by
  intro accumulator atoms
  induction atoms generalizing accumulator with
  | nil => simp [balancedFoldLeafSteps]
  | cons atom rest inductionHypothesis =>
      have hhead := hbound accumulator atom
      have htail := inductionHypothesis (step accumulator atom)
      have hexpand : (rest.length + 1) * bound = rest.length * bound + bound := by
        ring
      simp only [balancedFoldLeafSteps, List.length_cons]
      omega

theorem rationalMassFoldFuel_le (summaries : List ℕ) (bound : ℕ)
    (hbound :
      ∀ accumulator summary,
        rationalMassFoldLeafBudget accumulator summary ≤ bound) :
    rationalMassFoldFuel summaries ≤
      70 * summaries.length + 37 + summaries.length * bound := by
  have hstructural := balancedTraversalStructuralSteps_le_linear summaries
  have hleaves :=
    balancedFoldLeafSteps_le rationalMassStep rationalMassFoldLeafBudget bound
      hbound rationalMassInitialAccumulator summaries
  unfold rationalMassFoldFuel
  omega

theorem rationalMassFoldFuel_polyBounded
    {summaries : List ℕ}
    {measure bound countCoefficient leafCoefficient countDegree
      leafDegree : ℕ}
    (hcount :
      PolyBounded summaries.length measure countCoefficient countDegree)
    (hleaf : PolyBounded bound measure leafCoefficient leafDegree)
    (hbound :
      ∀ accumulator summary,
        rationalMassFoldLeafBudget accumulator summary ≤ bound) :
    PolyBounded (rationalMassFoldFuel summaries) measure
      (70 * countCoefficient + 37 + countCoefficient * leafCoefficient)
      (countDegree + leafDegree) := by
  have hstructural :
      PolyBounded (70 * summaries.length + 37) measure
        (70 * countCoefficient + 37) (countDegree + leafDegree) :=
    ((hcount.const_mul 70).add
      (polyBounded_const 37 measure countDegree)).degree_mono (by omega)
  have hproduct := hcount.mul hleaf
  exact (hstructural.add hproduct).mono
    (rationalMassFoldFuel_le summaries bound hbound)

theorem encodeBalancedList_getD_le (code : ℕ) :
    encodeBalancedList ((decodeBalancedList code).getD []) ≤ code := by
  cases hdecode : decodeBalancedList code with
  | none => simp [encodeBalancedList]
  | some values => simp [encodeBalancedList_of_decode hdecode]

@[simp] theorem balancedValidationMapCodes_encodeBalancedList
    (values : List ℕ) :
    balancedValidationMapCodes (encodeBalancedList values) = values := by
  simp [balancedValidationMapCodes]

/-- A decoded balanced list's length, from the *code's* width. -/
theorem polyBounded_length_of_encodeBalancedList_width
    {values : List ℕ} {measure coefficient degree : ℕ}
    (hraw :
      PolyBounded (natBitLength (encodeBalancedList values)) measure coefficient
        degree) :
    PolyBounded values.length measure (2 * coefficient) degree := by
  have hcodes := polyBounded_balancedValidationMapCodes_length hraw
  rwa [balancedValidationMapCodes_encodeBalancedList] at hcodes

/-- **The wire-metric map, dominated.**  Its callee is the closed numeral `6`,
so the counted call contributes only the count's degree. -/
theorem normalizedGateWireMetricMapFuel_polyBounded
    {inputLength : ℕ} {summaries : List ℕ}
    {measure coefficient guardCoefficient degree : ℕ}
    (hraw :
      PolyBounded (natBitLength (encodeBalancedList summaries)) measure
        coefficient degree)
    (hguard :
      PolyBounded
        (balancedValidationMapGuardFuel (encodeBalancedList summaries)) measure
        guardCoefficient (degree + degree)) :
    PolyBounded (normalizedGateWireMetricMapFuel inputLength summaries) measure
      (programRegisterSpan normalizedGateWireMetricMapProjectionProgram + 5 +
          balancedValidationMapCoefficient normalizedGateWireMetricProgram
            coefficient guardCoefficient 6 +
        normalizedGateWireMetricMapProjectionFuel) (degree + degree) := by
  have hmap :=
    balancedValidationMapFuel_polyBounded_of_width
      (callee := normalizedGateWireMetricProgram)
      (calleeFuel := normalizedGateWireMetricFuel) (inputLength := inputLength)
      hraw hguard (polyBounded_const 6 measure 0)
      (fun _ _ => le_rfl) (by omega) (by omega)
  exact linkFuel_polyBounded
    (second := normalizedGateWireMetricMapProjectionProgram) hmap
    (polyBounded_const normalizedGateWireMetricMapProjectionFuel measure
      (degree + degree))

/-- **The symmetric wire metric, dominated at the guard's degree.** -/
theorem normalizedCircuitSymmetricWireFuel_polyBounded
    {inputLength : ℕ} {summaries : List ℕ}
    {measure coefficient guardCoefficient degree : ℕ}
    (hraw :
      PolyBounded (natBitLength (encodeBalancedList summaries)) measure
        coefficient degree)
    (hguard :
      PolyBounded
        (balancedValidationMapGuardFuel (encodeBalancedList summaries)) measure
        guardCoefficient (degree + degree)) :
    PolyBounded (normalizedCircuitSymmetricWireFuel inputLength summaries)
      measure
      (programRegisterSpan balancedNatSumProgram + 5 +
          (programRegisterSpan normalizedGateWireMetricMapProjectionProgram +
              5 +
              balancedValidationMapCoefficient normalizedGateWireMetricProgram
                coefficient guardCoefficient 6 +
            normalizedGateWireMetricMapProjectionFuel) +
        (71 * (2 * coefficient) + 37)) (degree + degree) := by
  have hlength :
      PolyBounded (normalizedGateWireMetrics summaries).length measure
        (2 * coefficient) (degree + degree) := by
    have hcount := polyBounded_length_of_encodeBalancedList_width hraw
    have hmetrics :
        (normalizedGateWireMetrics summaries).length = summaries.length := by
      simp [normalizedGateWireMetrics]
    rw [hmetrics]
    exact hcount.degree_mono (by omega)
  have hsum :
      PolyBounded (balancedNatSumFuel (normalizedGateWireMetrics summaries))
        measure (71 * (2 * coefficient) + 37) (degree + degree) :=
    ((hlength.const_mul 71).add
      (polyBounded_const 37 measure (degree + degree))).mono
      (balancedNatSumFuel_le_linear (normalizedGateWireMetrics summaries))
  exact linkFuel_polyBounded (second := balancedNatSumProgram)
    (normalizedGateWireMetricMapFuel_polyBounded hraw hguard) hsum

/-- **The symmetric resource metric, dominated.**  The decoded summary list is
read out of the summary code, so a width certificate for that code is the only
input. -/
theorem normalizedCircuitResourceFuel_polyBounded_symmetric
    {inputLength summary measure coefficient degree : ℕ}
    (htag : normalizedCircuitResourceBranchTag summary = 0)
    (hcode :
      PolyBounded
        (natBitLength (normalizedCircuitResourceBottomSummariesCode summary))
        measure coefficient degree) :
    ∃ resourceCoefficient : ℕ,
      PolyBounded (normalizedCircuitResourceFuel inputLength summary) measure
        resourceCoefficient (degree + degree) := by
  have hraw :
      PolyBounded
        (natBitLength
          (encodeBalancedList (normalizedCircuitResourceSummaries summary)))
        measure coefficient degree :=
    hcode.mono
      (natBitLength_mono
        (encodeBalancedList_getD_le
          (normalizedCircuitResourceBottomSummariesCode summary)))
  obtain ⟨guardCoefficient, hguard⟩ :=
    balancedValidationMapGuardFuel_degree hraw
  have hbranch :=
    normalizedCircuitSymmetricWireFuel_polyBounded (inputLength := inputLength)
      hraw hguard
  have hfamilyEq :
      normalizedCircuitResourceFamilyFuel inputLength summary =
        taggedProgramChoiceFuel
          (normalizedCircuitSymmetricWireFuel inputLength
            (normalizedCircuitResourceSummaries summary)) := by
    unfold normalizedCircuitResourceFamilyFuel
    rw [if_pos htag]
  have hfamily :=
    (taggedProgramChoiceFuel_polyBounded hbranch).mono (le_of_eq hfamilyEq)
  exact ⟨_,
    linkFuel_polyBounded (second := normalizedCircuitResourceFamilyProgram)
      (polyBounded_const normalizedCircuitResourcePrepareFuel measure
        (degree + degree))
      hfamily⟩

end NearCubicWires.ValidatorCompositeLeafBounds
