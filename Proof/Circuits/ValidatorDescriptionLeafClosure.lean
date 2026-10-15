import Proof.Circuits.ValidatorResidualLeafBudget

namespace NearCubicWires.ValidatorDescriptionLeafClosure

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The unit-budget idiom

`PolyBounded value width budget k` unfolds to `value ≤ budget * (width + 1) ^ k`.
Read with `width` in the *measure* slot this is a purely local statement about a
charge and the width of the code it runs on — no request, no measure, no
polynomial envelope — and every rule of the domination algebra is available for
it.  §§2–5 are written entirely in that reading, and the two lemmas below are
the only places where it meets the real measure. -/

/-- The anchor of the local reading: a width dominates itself, linearly. -/
theorem polyBounded_width_self (width : ℕ) : PolyBounded width width 1 1 :=
  polyBounded_measure width 0

/-- **The transport lemma.**  A local unit budget at degree `k` becomes a
certificate at the real measure, at `k` times the anchor's degree. -/
theorem polyBounded_unitBudget (budget k : ℕ) {width measure coefficient degree : ℕ}
    (hwidth : PolyBounded width measure coefficient degree) :
    PolyBounded (budget * (width + 1) ^ k) measure
      (budget * (coefficient + 1) ^ k) (k * degree) := by
  have hpow :
      ∀ exponent : ℕ,
        PolyBounded ((width + 1) ^ exponent) measure
          ((coefficient + 1) ^ exponent) (exponent * degree) := by
    intro exponent
    induction exponent with
    | zero =>
        simpa only [pow_zero, Nat.zero_mul] using
          (polyBounded_const 1 measure 0)
    | succ count inductionHypothesis =>
        have hstep :
            PolyBounded (width + 1) measure (coefficient + 1) degree :=
          hwidth.add (polyBounded_const 1 measure degree)
        have hproduct := inductionHypothesis.mul hstep
        have hexponent : count * degree + degree = (count + 1) * degree := by
          ring
        rw [pow_succ, pow_succ, ← hexponent]
        exact hproduct
  exact (hpow k).const_mul budget

/-- Unit budgets are monotone in the width they are read at. -/
theorem unitBudget_mono (budget k : ℕ) {width width' : ℕ} (hle : width ≤ width') :
    budget * (width + 1) ^ k ≤ budget * (width' + 1) ^ k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)

theorem unitBudget_of_decoded (budget k : ℕ) {inner outer : ℕ}
    (hle : inner ≤ 3 * outer) :
    budget * (inner + 1) ^ k ≤ budget * 3 ^ k * (outer + 1) ^ k := by
  have hbase : inner + 1 ≤ 3 * (outer + 1) := by omega
  have hpow : (inner + 1) ^ k ≤ (3 * (outer + 1)) ^ k :=
    Nat.pow_le_pow_left hbase k
  have hexpand : (3 * (outer + 1)) ^ k = 3 ^ k * (outer + 1) ^ k :=
    Nat.mul_pow 3 (outer + 1) k
  calc
    budget * (inner + 1) ^ k ≤ budget * (3 ^ k * (outer + 1) ^ k) := by
      rw [← hexpand]
      exact Nat.mul_le_mul_left _ hpow
    _ = budget * 3 ^ k * (outer + 1) ^ k := by ring

/-- Degree weakening inside the local reading. -/
theorem unitBudget_degree_mono (budget : ℕ) {width j k : ℕ} (hle : j ≤ k) :
    budget * (width + 1) ^ j ≤ budget * (width + 1) ^ k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hle)

theorem natBitLength_le_of_mem_atoms {raw code : ℕ}
    (hcode : code ∈ (rawBalancedTraversalTree raw).atoms) :
    natBitLength code ≤ 3 * natBitLength raw := by
  have hwidths := rawBalancedTraversalTree_atomWidth_le raw
  have hmem :
      natBitLength code ∈ (rawBalancedTraversalTree raw).atoms.map natBitLength :=
    List.mem_map_of_mem hcode
  have hsingle :=
    List.single_le_sum
      (l := (rawBalancedTraversalTree raw).atoms.map natBitLength)
      (fun _ _ => Nat.zero_le _) _ hmem
  omega

theorem mem_balancedValidationMapCodes_mem_atoms {raw code : ℕ}
    (hcode : code ∈ balancedValidationMapCodes raw) :
    code ∈ (rawBalancedTraversalTree raw).atoms := by
  unfold balancedValidationMapCodes at hcode
  cases hdecode : decodeBalancedList raw with
  | none =>
      rw [hdecode] at hcode
      simp at hcode
  | some codes =>
      have hcodeEq : encodeBalancedList codes = raw :=
        encodeBalancedList_of_decode hdecode
      have htree : (balancedTraversalTree codes).code = raw := by
        rw [balancedTraversalTree_code, hcodeEq]
      have hnormalized :
          (rawBalancedTraversalTree raw).normalized =
            balancedTraversalTree codes := by
        rw [← htree]
        exact rawBalancedTraversalTree_normalized_code _
      have hatoms : (rawBalancedTraversalTree raw).atoms = codes := by
        change (rawBalancedTraversalTree raw).normalized.atoms = codes
        rw [hnormalized, balancedTraversalTree_atoms]
      rw [hdecode] at hcode
      have hmember : code ∈ codes := by simpa only [Option.getD_some] using hcode
      simpa only [hatoms] using hmember

theorem natBitLength_le_of_mem_balancedValidationMapCodes {raw code : ℕ}
    (hcode : code ∈ balancedValidationMapCodes raw) :
    natBitLength code ≤ 3 * natBitLength raw :=
  natBitLength_le_of_mem_atoms (mem_balancedValidationMapCodes_mem_atoms hcode)

/-! ### The canonicality guard's closed unit budget

`ValidatorLeafFuelBounds` §5 dominates the guard with an explicit coefficient;
§6 states the *degree* result existentially, because a numeral there would
evaluate the canonicalization pipeline's register spans.  Naming the coefficient
expression as a `def` and instantiating it at the unit anchor gives the same
information without any evaluation. -/

def canonicalityCoefficient (coefficient reencodeCoefficient : ℕ) : ℕ :=
  programRegisterSpan nativeNatEqProgram + 5 +
      (programRegisterSpan (preserveRightProgram balancedRawCanonicalizeProgram) +
          5 + 2 +
        ((programRegisterSpan balancedCanonicalizeProgram + 5 +
              (35 * (2 * coefficient) + 2) +
            (programRegisterSpan taggedToBalancedProgram + 5 +
                (programRegisterSpan balancedClauseStreamFlattenProgram + 5 +
                    (39 * (2 * coefficient) + 2) +
                  (32 * (2 * coefficient) + 7)) +
              (42 * (2 * coefficient) + 14))) + 4)) +
    (programRegisterSpan nativeNatEqCoreProgram + 5 + 6 +
      (programRegisterSpan nativeNatEqGateProgram + 5 +
          (pairedCallOverhead nativeNatLeProgram +
              (36 * max reencodeCoefficient coefficient + 8) +
            (36 * max coefficient reencodeCoefficient + 8)) +
        6))

/-- The coefficient the validation-map guard produces, named. -/
def guardCoefficient (canonicalityCoefficient : ℕ) : ℕ :=
  programRegisterSpan balancedValidationMapGuardGateProgram + 5 +
      (programRegisterSpan (preserveRightProgram balancedCanonicalityProgram) +
        5 + 2 + (canonicalityCoefficient + 4)) +
    balancedValidationMapGuardGateFuel

def guardUnitBudget : ℕ :=
  guardCoefficient (canonicalityCoefficient 1 (16 * (8 * 1 * (3 * 1))))

theorem balancedValidationMapGuardFuel_le_unitBudget (raw : ℕ) :
    balancedValidationMapGuardFuel raw ≤
      guardUnitBudget * (natBitLength raw + 1) ^ 2 := by
  have hraw := polyBounded_width_self (natBitLength raw)
  have hreencode := polyBounded_natBitLength_encodeBalancedList_atoms hraw
  have hcanonicality :=
    balancedCanonicalityFuel_polyBounded (hraw.degree_mono (by omega)) hreencode
  exact balancedValidationMapGuardFuel_polyBounded hcanonicality

/-- The decoded code count, in the local reading: at most twice the width. -/
theorem balancedValidationMapCodes_length_le_unit (raw : ℕ) :
    (balancedValidationMapCodes raw).length ≤ 2 * (natBitLength raw + 1) ^ 1 := by
  have hcodes := balancedValidationMapCodes_length_succ_le raw
  rw [pow_one]
  omega

theorem mem_balancedValidationMapRequests_payload
    {inputLength raw request : ℕ}
    (hrequest : request ∈ balancedValidationMapRequests inputLength raw) :
    (Nat.unpair request).1 = inputLength ∧
      (Nat.unpair request).2 ∈ balancedValidationMapCodes raw := by
  rw [balancedValidationMapRequests, List.mem_map] at hrequest
  obtain ⟨code, hcode, rfl⟩ := hrequest
  refine ⟨by simp only [nativeInputRequest, Nat.unpair_pair], ?_⟩
  simpa only [nativeInputRequest, Nat.unpair_pair] using hcode

def intDescriptionUnitBudget : ℕ :=
  programRegisterSpan
      (linkPrograms balancedLengthProgram canonicalPositiveLengthProgram) + 5 +
    2 +
    (programRegisterSpan canonicalPositiveLengthProgram + 5 +
      balancedLengthCoefficient 2 + 3)

theorem canonicalIntDescriptionFuel_le_unitBudget (code : ℕ) :
    canonicalIntDescriptionFuel code ≤
      intDescriptionUnitBudget * (natBitLength code + 1) ^ 1 := by
  have hwidth := polyBounded_width_self (natBitLength code)
  have hlength :
      PolyBounded (canonicalIntMagnitudeBits code).length (natBitLength code) 2
        1 := by
    refine (hwidth.const_mul 2).mono ?_
    have hcodes :=
      balancedValidationMapCodes_length_succ_le (canonicalIntMagnitudeCode code)
    have hproject :
        natBitLength (canonicalIntMagnitudeCode code) ≤ natBitLength code :=
      natBitLength_mono (Nat.unpair_right_le code)
    have heq :
        canonicalIntMagnitudeBits code =
          balancedValidationMapCodes (canonicalIntMagnitudeCode code) := rfl
    rw [heq]
    omega
  have hbalanced := balancedLengthFuel_polyBounded' hlength
  have hpositive :
      PolyBounded
        (canonicalPositiveLengthFuel (canonicalIntMagnitudeBits code).length)
        (natBitLength code) 3 1 := by
    refine PolyBounded.of_le_coefficient ?_
    unfold canonicalPositiveLengthFuel
    split <;> omega
  have hinner :=
    linkFuel_polyBounded (second := canonicalPositiveLengthProgram) hbalanced
      hpositive
  exact linkFuel_polyBounded
    (second := linkPrograms balancedLengthProgram canonicalPositiveLengthProgram)
    (polyBounded_const 2 (natBitLength code) 1) hinner

/-- The signed-integer counted map's closed unit budget. -/
def intDescriptionMapUnitBudget : ℕ :=
  programRegisterSpan canonicalIntDescriptionMapProjectionProgram + 5 +
    balancedValidationMapCoefficient canonicalIntDescriptionProgram 1
      guardUnitBudget (intDescriptionUnitBudget * 3 ^ 1) + 2

theorem canonicalIntDescriptionMapFuel_le_unitBudget
    (inputLength : ℕ) (values : List ℤ) :
    canonicalIntDescriptionMapFuel inputLength values ≤
      intDescriptionMapUnitBudget *
        (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) ^ 2 := by
  have hwidth :=
    polyBounded_width_self
      (natBitLength (encodeBalancedList (values.map encodeInt)))
  have hguard :
      PolyBounded
        (balancedValidationMapGuardFuel
          (encodeBalancedList (values.map encodeInt)))
        (natBitLength (encodeBalancedList (values.map encodeInt)))
        guardUnitBudget 2 :=
    balancedValidationMapGuardFuel_le_unitBudget _
  have hcallee :
      PolyBounded
        (intDescriptionUnitBudget * 3 ^ 1 *
          (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) ^ 1)
        (natBitLength (encodeBalancedList (values.map encodeInt)))
        (intDescriptionUnitBudget * 3 ^ 1) 1 := le_rfl
  have hbound :
      ∀ request ∈ balancedValidationMapRequests inputLength
          (encodeBalancedList (values.map encodeInt)),
        canonicalIntDescriptionFuel (Nat.unpair request).2 ≤
          intDescriptionUnitBudget * 3 ^ 1 *
            (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) ^ 1 := by
    intro request hrequest
    obtain ⟨_, hcode⟩ := mem_balancedValidationMapRequests_payload hrequest
    refine (canonicalIntDescriptionFuel_le_unitBudget _).trans ?_
    exact unitBudget_of_decoded intDescriptionUnitBudget 1
      (natBitLength_le_of_mem_balancedValidationMapCodes hcode)
  have hmap :=
    balancedValidationMapFuel_polyBounded_of_width
      (callee := canonicalIntDescriptionProgram)
      (calleeFuel := fun request =>
        canonicalIntDescriptionFuel (Nat.unpair request).2)
      (inputLength := inputLength) hwidth hguard hcallee hbound (by omega)
      (by omega)
  exact linkFuel_polyBounded
    (second := canonicalIntDescriptionMapProjectionProgram) hmap
    (polyBounded_const 2 _ 2)

/-- The signed-integer sum's closed unit budget. -/
def intDescriptionSumUnitBudget : ℕ :=
  programRegisterSpan balancedNatSumProgram + 5 + intDescriptionMapUnitBudget +
    179

/-- **The signed-integer counted sum, at degree `2`.** -/
theorem canonicalIntDescriptionSumFuel_le_unitBudget
    (inputLength : ℕ) (values : List ℤ) :
    canonicalIntDescriptionSumFuel inputLength values ≤
      intDescriptionSumUnitBudget *
        (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) ^ 2 := by
  have hcount :
      (values.map encodeInt).length ≤
        2 * (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) := by
    have hcodes :=
      balancedValidationMapCodes_length_le_unit
        (encodeBalancedList (values.map encodeInt))
    rw [balancedValidationMapCodes_encodeBalancedList, pow_one] at hcodes
    exact hcodes
  have hmetrics :
      (canonicalIntDescriptionMetrics values).length =
        (values.map encodeInt).length := by
    simp [canonicalIntDescriptionMetrics]
  have hlinear :=
    balancedNatSumFuel_le_linear (canonicalIntDescriptionMetrics values)
  have hstep :
      balancedNatSumFuel (canonicalIntDescriptionMetrics values) ≤
        179 *
          (natBitLength (encodeBalancedList (values.map encodeInt)) + 1) ^ 1 := by
    rw [pow_one]
    omega
  have hsum :
      PolyBounded (balancedNatSumFuel (canonicalIntDescriptionMetrics values))
        (natBitLength (encodeBalancedList (values.map encodeInt))) 179 2 :=
    hstep.trans (unitBudget_degree_mono 179 (by omega))
  exact linkFuel_polyBounded (second := balancedNatSumProgram)
    (canonicalIntDescriptionMapFuel_le_unitBudget inputLength values) hsum

/-! ## §4 One normalized gate's description

A gate summary carries its threshold as a signed code and its selected weights
as a signed-code list, and the description stage re-encodes what it decodes.
The re-encoding is either the original code — the decoders are canonical — or,
on a rejected code, the closed numeral `0`; either way it is no wider than the
code.  That is the whole width argument, and it is what lets the two stages be
charged against the *summary's* width alone. -/

private theorem natBitLength_encodeInt_decoded_le (code : ℕ) :
    natBitLength (encodeInt ((decodeInt code).getD 0)) ≤ natBitLength code := by
  cases hdecode : decodeInt code with
  | none =>
      have hzero : encodeInt (0 : ℤ) = 0 := (encodeInt_eq_zero_iff 0).2 rfl
      simp only [Option.getD_none, hzero, natBitLength_zero]
      exact one_le_natBitLength code
  | some value =>
      simp only [Option.getD_some, encodeInt_of_decode hdecode]
      exact le_rfl

private theorem encodeIntList_of_decode
    {code : ℕ} {values : List ℤ} (hdecode : decodeIntList code = some values) :
    encodeIntList values = code := by
  unfold decodeIntList at hdecode
  generalize hcandidate : decodeIntListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeIntList decoded = code then some decoded else none) =
          some values at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst hdecode
        exact hcanonical
      · simp at hdecode

private theorem natBitLength_encodeIntList_decoded_le (code : ℕ) :
    natBitLength (encodeBalancedList
        (((decodeIntList code).getD []).map encodeInt)) ≤
      natBitLength code := by
  cases hdecode : decodeIntList code with
  | none =>
      have hempty :
          encodeBalancedList ((([] : List ℤ)).map encodeInt) = 0 := by
        simp [encodeBalancedList]
      simp only [Option.getD_none, hempty, natBitLength_zero]
      exact one_le_natBitLength code
  | some values =>
      have hcode : encodeIntList values = code := encodeIntList_of_decode hdecode
      have hshape :
          encodeBalancedList (values.map encodeInt) = code := hcode
      simp only [Option.getD_some, hshape]
      exact le_rfl

/-! ### The gate's two stages -/

/-- The threshold stage's closed unit budget. -/
def gateThresholdStageUnitBudget : ℕ :=
  programRegisterSpan (preserveRightProgram canonicalIntDescriptionProgram) +
    5 + 9 + (intDescriptionUnitBudget + 4)

theorem normalizedGateDescriptionThresholdStageFuel_le_unitBudget
    (summary : ℕ) :
    normalizedGateDescriptionThresholdStageFuel summary ≤
      gateThresholdStageUnitBudget * (natBitLength summary + 1) ^ 1 := by
  have hproject :
      normalizedGateDescriptionThresholdCode summary ≤ summary := by
    simp only [normalizedGateDescriptionThresholdCode]
    exact (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)
  have hwidth :
      natBitLength
          (encodeInt (normalizedGateDescriptionThreshold summary)) ≤
        natBitLength summary :=
    (natBitLength_encodeInt_decoded_le
      (normalizedGateDescriptionThresholdCode summary)).trans
      (natBitLength_mono hproject)
  have hleaf :
      PolyBounded
        (canonicalIntDescriptionFuel
          (encodeInt (normalizedGateDescriptionThreshold summary)))
        (natBitLength summary) intDescriptionUnitBudget 1 :=
    (canonicalIntDescriptionFuel_le_unitBudget _).trans
      (unitBudget_mono intDescriptionUnitBudget 1 hwidth)
  exact linkFuel_polyBounded
    (second := preserveRightProgram canonicalIntDescriptionProgram)
    (polyBounded_const 9 (natBitLength summary) 1)
    (preserveRightFuel_polyBounded hleaf)

/-- The weight stage's closed unit budget. -/
def gateWeightStageUnitBudget : ℕ :=
  programRegisterSpan (preserveRightProgram canonicalIntDescriptionSumProgram) +
    5 + 7 + (intDescriptionSumUnitBudget + 4)

theorem normalizedGateDescriptionWeightStageFuel_le_unitBudget
    (inputLength summary : ℕ) :
    normalizedGateDescriptionWeightStageFuel inputLength summary ≤
      gateWeightStageUnitBudget * (natBitLength summary + 1) ^ 2 := by
  have hproject :
      normalizedGateDescriptionSelectedWeightsCode summary ≤ summary := by
    simp only [normalizedGateDescriptionSelectedWeightsCode]
    exact (Nat.unpair_left_le _).trans
      ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
  have hwidth :
      natBitLength
          (encodeBalancedList
            ((normalizedGateDescriptionSelectedWeights summary).map
              encodeInt)) ≤
        natBitLength summary :=
    (natBitLength_encodeIntList_decoded_le
      (normalizedGateDescriptionSelectedWeightsCode summary)).trans
      (natBitLength_mono hproject)
  have hleaf :
      PolyBounded
        (canonicalIntDescriptionSumFuel inputLength
          (normalizedGateDescriptionSelectedWeights summary))
        (natBitLength summary) intDescriptionSumUnitBudget 2 :=
    (canonicalIntDescriptionSumFuel_le_unitBudget inputLength _).trans
      (unitBudget_mono intDescriptionSumUnitBudget 2 hwidth)
  exact linkFuel_polyBounded
    (second := preserveRightProgram canonicalIntDescriptionSumProgram)
    (polyBounded_const 7 (natBitLength summary) 2)
    (preserveRightFuel_polyBounded hleaf)

/-- **One gate's description, at degree `2`.**  Uniform in the public input
length: the stage charges read only the summary. -/
def gateDescriptionUnitBudget : ℕ :=
  programRegisterSpan
      (linkPrograms normalizedGateDescriptionWeightStageProgram
        normalizedGateDescriptionFinalProgram) + 5 +
    gateThresholdStageUnitBudget +
    (programRegisterSpan normalizedGateDescriptionFinalProgram + 5 +
      gateWeightStageUnitBudget + 9)

theorem normalizedGateDescriptionFuel_le_unitBudget
    (inputLength summary : ℕ) :
    normalizedGateDescriptionFuel inputLength summary ≤
      gateDescriptionUnitBudget * (natBitLength summary + 1) ^ 2 := by
  have hthreshold :
      PolyBounded (normalizedGateDescriptionThresholdStageFuel summary)
        (natBitLength summary) gateThresholdStageUnitBudget 2 :=
    (normalizedGateDescriptionThresholdStageFuel_le_unitBudget summary).trans
      (unitBudget_degree_mono gateThresholdStageUnitBudget (by omega))
  have hweight :
      PolyBounded (normalizedGateDescriptionWeightStageFuel inputLength summary)
        (natBitLength summary) gateWeightStageUnitBudget 2 :=
    normalizedGateDescriptionWeightStageFuel_le_unitBudget inputLength summary
  have hinner :=
    linkFuel_polyBounded (second := normalizedGateDescriptionFinalProgram)
      hweight (polyBounded_const 9 (natBitLength summary) 2)
  exact linkFuel_polyBounded
    (second :=
      linkPrograms normalizedGateDescriptionWeightStageProgram
        normalizedGateDescriptionFinalProgram)
    hthreshold hinner

/-! ### The bottom-gate counted map and sum

The second counted combinator on the path.  Its callee is the gate description
above — degree `2` — and the count is the decoded summary list's, so the map
lands at degree `3`.  With the guard at `2` and the anchor at `1` that is the
map's own degree, and it is the last degree this module spends: everything above
is a linker, a wrapper, a native call at a singleton, or a family choice. -/

/-- The bottom-gate map's closed unit budget. -/
def gateMapUnitBudget : ℕ :=
  programRegisterSpan normalizedGateDescriptionMapProjectionProgram + 5 +
    balancedValidationMapCoefficient normalizedGateDescriptionProgram 1
      guardUnitBudget (gateDescriptionUnitBudget * 3 ^ 2) + 2

theorem normalizedGateDescriptionMapFuel_le_unitBudget
    (inputLength : ℕ) (summaries : List ℕ) :
    normalizedGateDescriptionMapFuel inputLength summaries ≤
      gateMapUnitBudget * (natBitLength (encodeBalancedList summaries) + 1) ^ 3 := by
  have hwidth :=
    polyBounded_width_self (natBitLength (encodeBalancedList summaries))
  have hguard :
      PolyBounded
        (balancedValidationMapGuardFuel (encodeBalancedList summaries))
        (natBitLength (encodeBalancedList summaries)) guardUnitBudget 3 :=
    (balancedValidationMapGuardFuel_le_unitBudget _).trans
      (unitBudget_degree_mono guardUnitBudget (by omega))
  have hcallee :
      PolyBounded
        (gateDescriptionUnitBudget * 3 ^ 2 *
          (natBitLength (encodeBalancedList summaries) + 1) ^ 2)
        (natBitLength (encodeBalancedList summaries))
        (gateDescriptionUnitBudget * 3 ^ 2) 2 := le_rfl
  have hbound :
      ∀ request ∈ balancedValidationMapRequests inputLength
          (encodeBalancedList summaries),
        normalizedGateDescriptionFuel (Nat.unpair request).1
            (Nat.unpair request).2 ≤
          gateDescriptionUnitBudget * 3 ^ 2 *
            (natBitLength (encodeBalancedList summaries) + 1) ^ 2 := by
    intro request hrequest
    obtain ⟨_, hcode⟩ := mem_balancedValidationMapRequests_payload hrequest
    refine (normalizedGateDescriptionFuel_le_unitBudget _ _).trans ?_
    exact unitBudget_of_decoded gateDescriptionUnitBudget 2
      (natBitLength_le_of_mem_balancedValidationMapCodes hcode)
  have hmap :=
    balancedValidationMapFuel_polyBounded_of_width
      (callee := normalizedGateDescriptionProgram)
      (calleeFuel := fun request =>
        normalizedGateDescriptionFuel (Nat.unpair request).1
          (Nat.unpair request).2)
      (inputLength := inputLength) hwidth hguard hcallee hbound (by omega)
      (by omega)
  exact linkFuel_polyBounded
    (second := normalizedGateDescriptionMapProjectionProgram) hmap
    (polyBounded_const 2 _ 3)

/-- The bottom-gate sum's closed unit budget. -/
def gateSumUnitBudget : ℕ :=
  programRegisterSpan balancedNatSumProgram + 5 + gateMapUnitBudget + 179

theorem normalizedGateDescriptionSumFuel_le_unitBudget
    (inputLength : ℕ) (summaries : List ℕ) :
    normalizedGateDescriptionSumFuel inputLength summaries ≤
      gateSumUnitBudget * (natBitLength (encodeBalancedList summaries) + 1) ^ 3 := by
  have hcount :
      summaries.length ≤
        2 * (natBitLength (encodeBalancedList summaries) + 1) := by
    have hcodes :=
      balancedValidationMapCodes_length_le_unit (encodeBalancedList summaries)
    rw [balancedValidationMapCodes_encodeBalancedList, pow_one] at hcodes
    exact hcodes
  have hmetrics :
      (normalizedGateDescriptionMetrics inputLength summaries).length =
        summaries.length := by
    simp [normalizedGateDescriptionMetrics]
  have hlinear :=
    balancedNatSumFuel_le_linear
      (normalizedGateDescriptionMetrics inputLength summaries)
  have hstep :
      balancedNatSumFuel
          (normalizedGateDescriptionMetrics inputLength summaries) ≤
        179 * (natBitLength (encodeBalancedList summaries) + 1) ^ 1 := by
    rw [pow_one]
    omega
  have hsum :
      PolyBounded
        (balancedNatSumFuel
          (normalizedGateDescriptionMetrics inputLength summaries))
        (natBitLength (encodeBalancedList summaries)) 179 3 :=
    hstep.trans (unitBudget_degree_mono 179 (by omega))
  exact linkFuel_polyBounded (second := balancedNatSumProgram)
    (normalizedGateDescriptionMapFuel_le_unitBudget inputLength summaries) hsum

/-! ### The two family branches -/

/-- The symmetric branch's closed unit budget. -/
def symmetricDescriptionUnitBudget : ℕ :=
  programRegisterSpan normalizedCircuitSymmetricDescriptionFinalProgram + 5 +
    (gateSumUnitBudget + 4) + 5

theorem normalizedCircuitSymmetricDescriptionFuel_le_unitBudget
    (inputLength bottomCount : ℕ) (summaries : List ℕ) :
    normalizedCircuitSymmetricDescriptionFuel inputLength bottomCount
        summaries ≤
      symmetricDescriptionUnitBudget *
        (natBitLength (encodeBalancedList summaries) + 1) ^ 3 :=
  linkFuel_polyBounded
    (second := normalizedCircuitSymmetricDescriptionFinalProgram)
    (preserveRightFuel_polyBounded
      (normalizedGateDescriptionSumFuel_le_unitBudget inputLength summaries))
    (polyBounded_const 5 _ 3)

/-- The threshold branch's top call: one native contextual call into the gate
description, so it costs the gate's own budget at the *top* summary's width. -/
def thresholdTopCallUnitBudget : ℕ :=
  programRegisterSpan
      (nativeContextCallProgram normalizedGateDescriptionProgram) + 5 + 7 +
    (nativeContextCallOverhead normalizedGateDescriptionProgram +
      gateDescriptionUnitBudget)

theorem normalizedCircuitThresholdTopCallFuel_le_unitBudget
    (bottomMetric topSummary bottomCount : ℕ) :
    normalizedCircuitThresholdTopCallFuel bottomMetric topSummary bottomCount ≤
      thresholdTopCallUnitBudget * (natBitLength topSummary + 1) ^ 2 := by
  have hgate :
      PolyBounded (normalizedGateDescriptionFuel bottomCount topSummary)
        (natBitLength topSummary) gateDescriptionUnitBudget 2 :=
    normalizedGateDescriptionFuel_le_unitBudget bottomCount topSummary
  have hcall :
      PolyBounded
        (nativeContextCallFuel normalizedGateDescriptionProgram
          (normalizedGateDescriptionFuel bottomCount topSummary) bottomCount
          topSummary) (natBitLength topSummary)
        (nativeContextCallOverhead normalizedGateDescriptionProgram +
          gateDescriptionUnitBudget) 2 :=
    ((polyBounded_const
      (nativeContextCallOverhead normalizedGateDescriptionProgram)
      (natBitLength topSummary) 2).add hgate).mono
      (nativeContextCallFuel_le _ _ _ _)
  exact linkFuel_polyBounded
    (second := nativeContextCallProgram normalizedGateDescriptionProgram)
    (polyBounded_const 7 (natBitLength topSummary) 2) hcall

/-- The threshold branch's closed unit budget, read at the wider of the bottom
summaries' code and the top summary. -/
def thresholdDescriptionUnitBudget : ℕ :=
  programRegisterSpan
      (linkPrograms normalizedCircuitThresholdTopCallProgram
        normalizedCircuitThresholdDescriptionFinalProgram) + 5 +
    (gateSumUnitBudget + 4) +
    (programRegisterSpan normalizedCircuitThresholdDescriptionFinalProgram +
      5 + thresholdTopCallUnitBudget + 5)

set_option maxHeartbeats 1000000 in
-- The threshold branch links two opaque verified description programs.
theorem normalizedCircuitThresholdDescriptionFuel_le_unitBudget
    (inputLength topSummary : ℕ) (summaries : List ℕ) (width : ℕ)
    (hsummaries : natBitLength (encodeBalancedList summaries) ≤ width)
    (htop : natBitLength topSummary ≤ width) :
    normalizedCircuitThresholdDescriptionFuel inputLength topSummary
        summaries ≤
      thresholdDescriptionUnitBudget * (width + 1) ^ 3 := by
  have hsum :
      PolyBounded (normalizedGateDescriptionSumFuel inputLength summaries) width
        gateSumUnitBudget 3 :=
    (normalizedGateDescriptionSumFuel_le_unitBudget inputLength summaries).trans
      (unitBudget_mono gateSumUnitBudget 3 hsummaries)
  have htopCall :
      PolyBounded
        (normalizedCircuitThresholdTopCallFuel
          (normalizedGateDescriptionMetrics inputLength summaries).sum topSummary
          summaries.length) width thresholdTopCallUnitBudget 3 :=
    ((normalizedCircuitThresholdTopCallFuel_le_unitBudget _ _ _).trans
      (unitBudget_mono thresholdTopCallUnitBudget 2 htop)).trans
      (unitBudget_degree_mono thresholdTopCallUnitBudget (by omega))
  have hinner :=
    linkFuel_polyBounded
      (second := normalizedCircuitThresholdDescriptionFinalProgram) htopCall
      (polyBounded_const 5 width 3)
  exact linkFuel_polyBounded
    (second :=
      linkPrograms normalizedCircuitThresholdTopCallProgram
        normalizedCircuitThresholdDescriptionFinalProgram)
    (preserveRightFuel_polyBounded hsum) hinner

theorem normalizedCircuitResourceBottomSummariesCode_le (summary : ℕ) :
    normalizedCircuitResourceBottomSummariesCode summary ≤ summary := by
  simp only [normalizedCircuitResourceBottomSummariesCode,
    normalizedCircuitResourceBottomSummaryData,
    normalizedCircuitResourceBottomAndRaw, normalizedCircuitResourcePayload]
  exact (Nat.unpair_left_le _).trans
    ((Nat.unpair_left_le _).trans
      ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))

theorem normalizedCircuitResourceTopSummary_le (summary : ℕ) :
    normalizedCircuitResourceTopSummary summary ≤ summary := by
  simp only [normalizedCircuitResourceTopSummary,
    normalizedCircuitResourcePayload]
  exact (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)

/-- **The one reusable width certificate.**  The decoded bottom summaries
re-encode inside the summary's own width. -/
theorem natBitLength_encodeBalancedList_resourceSummaries_le (summary : ℕ) :
    natBitLength
        (encodeBalancedList (normalizedCircuitResourceSummaries summary)) ≤
      natBitLength summary :=
  (natBitLength_mono
    (encodeBalancedList_getD_le
      (normalizedCircuitResourceBottomSummariesCode summary))).trans
    (natBitLength_mono (normalizedCircuitResourceBottomSummariesCode_le summary))

/-- The family dispatcher's closed unit budget. -/
def descriptionFamilyUnitBudget : ℕ :=
  symmetricDescriptionUnitBudget + thresholdDescriptionUnitBudget + 5

/-- The two branch weakenings, stated over *variables*.  Both unit budgets are
closed naturals over composed programs, and `omega` normalises closed `Nat`
terms: instantiating these by `exact` is what keeps the family dispatcher's
weakening out of the kernel. -/
private theorem le_familyBudget_left (left right : ℕ) :
    left + 5 ≤ left + right + 5 := by omega

private theorem le_familyBudget_right (left right : ℕ) :
    right + 5 ≤ left + right + 5 := by omega

set_option maxHeartbeats 1000000 in
-- Family-choice normalization sees the two opaque verified branch programs.
theorem normalizedCircuitDescriptionFamilyFuel_le_unitBudget
    (inputLength summary : ℕ) :
    normalizedCircuitDescriptionFamilyFuel inputLength summary ≤
      descriptionFamilyUnitBudget * (natBitLength summary + 1) ^ 3 := by
  have hsummaries := natBitLength_encodeBalancedList_resourceSummaries_le summary
  have htop :
      natBitLength (normalizedCircuitResourceTopSummary summary) ≤
        natBitLength summary :=
    natBitLength_mono (normalizedCircuitResourceTopSummary_le summary)
  unfold normalizedCircuitDescriptionFamilyFuel
  split
  · have hbranch :
        PolyBounded
          (normalizedCircuitSymmetricDescriptionFuel inputLength
            (normalizedCircuitResourceBottomLength summary)
            (normalizedCircuitResourceSummaries summary))
          (natBitLength summary) symmetricDescriptionUnitBudget 3 :=
      (normalizedCircuitSymmetricDescriptionFuel_le_unitBudget _ _ _).trans
        (unitBudget_mono symmetricDescriptionUnitBudget 3 hsummaries)
    exact (taggedProgramChoiceFuel_polyBounded hbranch).coefficient_mono
      (le_familyBudget_left symmetricDescriptionUnitBudget
        thresholdDescriptionUnitBudget)
  · have hbranch :
        PolyBounded
          (normalizedCircuitThresholdDescriptionFuel inputLength
            (normalizedCircuitResourceTopSummary summary)
            (normalizedCircuitResourceSummaries summary))
          (natBitLength summary) thresholdDescriptionUnitBudget 3 :=
      normalizedCircuitThresholdDescriptionFuel_le_unitBudget _ _ _ _ hsummaries
        htop
    exact (taggedProgramChoiceFuel_polyBounded hbranch).coefficient_mono
      (le_familyBudget_right symmetricDescriptionUnitBudget
        thresholdDescriptionUnitBudget)

/-- **The description metric's closed unit budget.** -/
def normalizedCircuitDescriptionUnitBudget : ℕ :=
  programRegisterSpan normalizedCircuitDescriptionFamilyProgram + 5 + 15 +
    descriptionFamilyUnitBudget

set_option maxHeartbeats 1000000 in
-- One linker over the opaque family dispatcher.
set_option maxRecDepth 4000 in
theorem normalizedCircuitDescriptionFuel_le_unitBudget
    (inputLength summary : ℕ) :
    normalizedCircuitDescriptionFuel inputLength summary ≤
      normalizedCircuitDescriptionUnitBudget * (natBitLength summary + 1) ^ 3 :=
  linkFuel_polyBounded (second := normalizedCircuitDescriptionFamilyProgram)
    (polyBounded_const 15 (natBitLength summary) 3)
    (normalizedCircuitDescriptionFamilyFuel_le_unitBudget inputLength summary)

/-- The transport step, stated over *variables*.  The description metric's unit
budget is a closed natural whose definition chain reaches
`balancedCallLayout` on a composed callee; naming it in a statement forces the
elaborator to walk that chain, so it is only ever supplied as an explicit
argument here and never appears in a published type. -/
private theorem polyBounded_of_unitBudget_le
    {value width measure coefficient degree : ℕ} (budget k : ℕ)
    (hwidth : PolyBounded width measure coefficient degree)
    (hvalue : value ≤ budget * (width + 1) ^ k) :
    PolyBounded value measure (budget * (coefficient + 1) ^ k) (k * degree) :=
  (polyBounded_unitBudget budget k hwidth).mono hvalue

/-- **Residual 1, closed: the description metric is dominated at degree
`3 · d`.**  One width certificate for the validated summary is the whole input,
and the degree is exactly three times the anchor's — one for the signed-integer
count, one for the bottom-gate count, one for the canonicality guard's
re-encoding.

The coefficient is existential, exactly as `ValidatorLeafFuelBounds` §6 states
the guard's: it is a closed natural over the description cone's composed
programs, and writing it into a type would evaluate their register spans. -/
theorem normalizedCircuitDescriptionFuel_polyBounded
    {inputLength summary measure coefficient degree : ℕ}
    (hsummary : PolyBounded (natBitLength summary) measure coefficient degree) :
    ∃ descriptionCoefficient : ℕ,
      PolyBounded (normalizedCircuitDescriptionFuel inputLength summary) measure
        descriptionCoefficient (3 * degree) :=
  ⟨_,
    polyBounded_of_unitBudget_le normalizedCircuitDescriptionUnitBudget 3
      hsummary
      (normalizedCircuitDescriptionFuel_le_unitBudget inputLength summary)⟩

/-- **The description metric at the machine's anchor: degree exactly `3`.**
`ValidatorCompositeLeafBounds` §7 fixes `3` as the deepest admissible callee
degree for a counted summary landing at `recoveryVerifierDegree = 4`, so the
validator's description stage lands in its slot with zero headroom. -/
theorem normalizedCircuitDescriptionFuel_degree_three
    {inputLength summary measure coefficient : ℕ}
    (hsummary : PolyBounded (natBitLength summary) measure coefficient 1) :
    ∃ descriptionCoefficient : ℕ,
      PolyBounded (normalizedCircuitDescriptionFuel inputLength summary) measure
        descriptionCoefficient 3 := by
  obtain ⟨descriptionCoefficient, hbound⟩ :=
    normalizedCircuitDescriptionFuel_polyBounded (inputLength := inputLength)
      hsummary
  exact ⟨descriptionCoefficient, hbound.degree_mono (by omega)⟩

end NearCubicWires.ValidatorDescriptionLeafClosure
