import Proof.MachineModel.CanonicalBalancedValidationProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Total canonical-natural validation

The public natural codec is a canonical balanced list of little-endian bits.
This module gives arbitrary raw naturals one executable boundary: normalize
the traversed tree, fold its atoms to a native candidate, re-encode that
candidate with the canonical `encodeNat` instruction, and compare the result
with the untouched input.  Thus malformed tags, non-Boolean atoms, alternate
tree shapes, and high zeroes all follow the same rejection path.
-/

namespace NearCubicWires.CanonicalNatValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def canonicalNatCandidate (raw : ℕ) : ℕ :=
  taggedBitFoldValue (rawBalancedTraversalTree raw).atoms 0 1

/-! ## Total raw-to-candidate pass -/

def canonicalNatCandidateProgram : NPOracleProgram :=
  linkPrograms balancedRawCanonicalizeProgram canonicalNatDecodeProgram

@[simp] theorem canonicalNatCandidateProgram_oracleFree :
    OracleFree canonicalNatCandidateProgram := by
  exact oracleFree_linkPrograms
    balancedRawCanonicalizeProgram_oracleFree
    canonicalNatDecodeProgram_oracleFree

def canonicalNatCandidateFuel (raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  linkFuel canonicalNatDecodeProgram
    (balancedRawCanonicalizeFuel tree)
    (canonicalNatDecodeListFuel tree.atoms)

def canonicalNatCandidateBits (inputLength raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  max 1 <| max (natBitLength inputLength) <|
    max (balancedRawCanonicalizeBits inputLength tree)
      (canonicalNatDecodeListBits inputLength tree.atoms)

theorem run_canonicalNatCandidateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatCandidateProgram
        (canonicalNatCandidateBits inputLength raw)
        (canonicalNatCandidateFuel raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalNatCandidate raw) := by
  let tree := rawBalancedTraversalTree raw
  let maximumBits := canonicalNatCandidateBits inputLength raw
  have hvalid : tree.Valid := rawBalancedTraversalTree_valid raw
  have hcode : tree.rawCode = raw :=
    rawBalancedTraversalTree_rawCode raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateBits]
  have hnormalize :
      balancedRawCanonicalizeBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateBits, tree]
  have hdecode :
      canonicalNatDecodeListBits inputLength tree.atoms ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateBits, tree]
  apply run_linkPrograms hpositive hlength
  · simpa [hcode] using
      run_bits_mono
        (run_balancedRawCanonicalizeProgram inputLength tree hvalid)
        hnormalize
  · simpa [canonicalNatCandidate, tree] using
      run_bits_mono
        (run_canonicalNatDecodeProgram_fromList inputLength tree.atoms)
        hdecode

/-! ## Semantic canonicality -/

theorem canonicalNatCandidate_of_decode
    {raw value : ℕ} (hdecode : decodeNat raw = some value) :
    canonicalNatCandidate raw = value := by
  have hcode : encodeNat value = raw :=
    encodeNat_of_decode hdecode
  have hatoms :
      (rawBalancedTraversalTree raw).atoms =
        value.bits.map boolCode := by
    rw [← hcode]
    unfold encodeNat encodeBits encodeBoolList
    rw [← balancedTraversalTree_code]
    simp [RawBalancedTraversalTree.atoms,
      rawBalancedTraversalTree_normalized_code,
      balancedTraversalTree_atoms]
  rw [canonicalNatCandidate, hatoms,
    show value.bits.map boolCode = value.bits.map Bool.toNat by rfl,
    taggedBitFoldValue_boolBits, bitsValue_natBits]

def canonicalNatValidationOutput (raw : ℕ) : ℕ :=
  let candidate := canonicalNatCandidate raw
  if encodeNat candidate = raw then Nat.pair 1 candidate else 0

theorem canonicalNatValidationOutput_of_decode
    {raw value : ℕ} (hdecode : decodeNat raw = some value) :
    canonicalNatValidationOutput raw = Nat.pair 1 value := by
  have hcandidate := canonicalNatCandidate_of_decode hdecode
  have hcode := encodeNat_of_decode hdecode
  simp [canonicalNatValidationOutput, hcandidate, hcode]

@[simp] theorem canonicalNatValidationOutput_encodeNat (value : ℕ) :
    canonicalNatValidationOutput (encodeNat value) =
      Nat.pair 1 value :=
  canonicalNatValidationOutput_of_decode (decodeNat_encode value)

theorem canonicalNatValidationOutput_ne_zero_iff
    (raw : ℕ) :
    canonicalNatValidationOutput raw ≠ 0 ↔
      ∃ value, decodeNat raw = some value := by
  constructor
  · intro hnonzero
    by_cases hcanonical :
        encodeNat (canonicalNatCandidate raw) = raw
    · exact ⟨canonicalNatCandidate raw, by
        exact (congrArg decodeNat hcanonical.symm).trans
          (decodeNat_encode (canonicalNatCandidate raw))⟩
    · simp [canonicalNatValidationOutput, hcanonical] at hnonzero
  · rintro ⟨value, hdecode⟩
    rw [canonicalNatValidationOutput_of_decode hdecode]
    have hpositive : 0 < Nat.pair 1 value :=
      (show 0 < 1 by omega).trans_le (Nat.left_le_pair 1 value)
    exact hpositive.ne'

theorem canonicalNatValidationOutput_eq_zero_iff
    (raw : ℕ) :
    canonicalNatValidationOutput raw = 0 ↔ decodeNat raw = none := by
  constructor
  · intro hzero
    cases hdecode : decodeNat raw with
    | none => rfl
    | some value =>
        have hnonzero :=
          (canonicalNatValidationOutput_ne_zero_iff raw).2
            ⟨value, hdecode⟩
        exact False.elim (hnonzero hzero)
  · intro hdecode
    by_contra hnonzero
    obtain ⟨value, hvalue⟩ :=
      (canonicalNatValidationOutput_ne_zero_iff raw).1 hnonzero
    rw [hdecode] at hvalue
    contradiction

/-! ## Retain the untrusted word while computing its candidate -/

def duplicateRawProgram : NPOracleProgram :=
  [.pair 0 0 0 1, .halt 0]

private def duplicateRawBits (raw : ℕ) : ℕ :=
  max (natBitLength raw) (natBitLength (Nat.pair raw raw))

private theorem duplicateRawProgram_oracleFree :
    OracleFree duplicateRawProgram := by
  rfl

private theorem run_duplicateRawProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram duplicateRawProgram (duplicateRawBits raw) 2
        (initialNPOracleState inputLength raw) =
      some (Nat.pair raw raw) := by
  have houtput :
      natBitLength (Nat.pair raw raw) ≤ duplicateRawBits raw :=
    Nat.le_max_right _ _
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair raw raw)
    (by rfl) rfl (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def candidateWithRawProgram : NPOracleProgram :=
  linkPrograms duplicateRawProgram <|
    preserveRightProgram canonicalNatCandidateProgram

private theorem candidateWithRawProgram_oracleFree :
    OracleFree candidateWithRawProgram := by
  exact oracleFree_linkPrograms duplicateRawProgram_oracleFree <|
    preserveRightProgram_oracleFree canonicalNatCandidateProgram
      canonicalNatCandidateProgram_oracleFree

def candidateWithRawFuel (raw : ℕ) : ℕ :=
  linkFuel (preserveRightProgram canonicalNatCandidateProgram) 2 <|
    preserveRightFuel (canonicalNatCandidateFuel raw)

private def candidateWithRawBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (duplicateRawBits raw) <|
      preserveRightBits
        (canonicalNatCandidateBits inputLength raw)
        raw raw (canonicalNatCandidate raw)

private theorem run_candidateWithRawProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram candidateWithRawProgram
        (candidateWithRawBits inputLength raw)
        (candidateWithRawFuel raw)
        (initialNPOracleState inputLength raw) =
      some (Nat.pair (canonicalNatCandidate raw) raw) := by
  let maximumBits := candidateWithRawBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, candidateWithRawBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, candidateWithRawBits]
  have hduplicate : duplicateRawBits raw ≤ maximumBits := by
    simp [maximumBits, candidateWithRawBits]
  have hpreserve :
      preserveRightBits
          (canonicalNatCandidateBits inputLength raw)
          raw raw (canonicalNatCandidate raw) ≤ maximumBits := by
    simp [maximumBits, candidateWithRawBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_duplicateRawProgram inputLength raw) hduplicate
  · exact run_bits_mono
      (run_preserveRightProgram canonicalNatCandidateProgram inputLength
        (canonicalNatCandidateBits inputLength raw)
        (canonicalNatCandidateFuel raw)
        raw raw (canonicalNatCandidate raw)
        (run_canonicalNatCandidateProgram inputLength raw))
      hpreserve

/-! ## Re-encode and retain the candidate through equality -/

private def canonicalNatEqualityInput (raw : ℕ) : ℕ :=
  let candidate := canonicalNatCandidate raw
  Nat.pair
    (nativeNatEqInput (encodeNat candidate) raw)
    candidate

def canonicalNatEqualityPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .encodeNat 2 4 3
  , .pair 4 3 5 4
  , .pair 5 2 0 5
  , .halt 0
  ]

private def canonicalNatEqualityPrepareBits
    (inputLength raw : ℕ) : ℕ :=
  let candidate := canonicalNatCandidate raw
  max 1 <| max (natBitLength inputLength) <|
    max (natBitLength (Nat.pair candidate raw)) <|
      max (natBitLength candidate) <|
        max (natBitLength raw) <|
          max (natBitLength (encodeNat candidate)) <|
            max
              (natBitLength
                (nativeNatEqInput (encodeNat candidate) raw))
              (natBitLength (canonicalNatEqualityInput raw))

private theorem canonicalNatEqualityPrepareProgram_oracleFree :
    OracleFree canonicalNatEqualityPrepareProgram := by
  rfl

private theorem run_canonicalNatEqualityPrepareProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatEqualityPrepareProgram
        (canonicalNatEqualityPrepareBits inputLength raw) 6
        (initialNPOracleState inputLength
          (Nat.pair (canonicalNatCandidate raw) raw)) =
      some (canonicalNatEqualityInput raw) := by
  let candidate := canonicalNatCandidate raw
  let encoded := encodeNat candidate
  let equalityInput := nativeNatEqInput encoded raw
  let output := canonicalNatEqualityInput raw
  let maximumBits :=
    canonicalNatEqualityPrepareBits inputLength raw
  have hcandidate :
      natBitLength candidate ≤ maximumBits := by
    simp [maximumBits, canonicalNatEqualityPrepareBits, candidate]
  have hraw : natBitLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatEqualityPrepareBits]
  have hencoded : natBitLength encoded ≤ maximumBits := by
    simp [maximumBits, canonicalNatEqualityPrepareBits, encoded,
      candidate]
  have hequality : natBitLength equalityInput ≤ maximumBits := by
    simp [maximumBits, canonicalNatEqualityPrepareBits, equalityInput,
      encoded, candidate]
  have houtput : natBitLength output ≤ maximumBits := by
    simp [maximumBits, canonicalNatEqualityPrepareBits, output]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := candidate)
    (by rfl) rfl
    (by simp [initialNPOracleState, candidate]) hcandidate]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := raw)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, candidate]) hraw]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_encodeNat_instruction (value := candidate)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, candidate])
    hencoded]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := equalityInput)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, equalityInput, nativeNatEqInput,
      encoded, candidate])
    hequality]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, output, canonicalNatEqualityInput,
      equalityInput, encoded, candidate])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

private def canonicalNatEqualityFlag (raw : ℕ) : ℕ :=
  nativeNatEqOutput
    (encodeNat (canonicalNatCandidate raw)) raw

def canonicalNatEqualityProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

private theorem canonicalNatEqualityProgram_oracleFree :
    OracleFree canonicalNatEqualityProgram := by
  exact preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def canonicalNatEqualityFuel (raw : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel
      (encodeNat (canonicalNatCandidate raw)) raw

private def canonicalNatEqualityBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength
      (encodeNat (canonicalNatCandidate raw)) raw)
    (nativeNatEqInput
      (encodeNat (canonicalNatCandidate raw)) raw)
    (canonicalNatCandidate raw)
    (canonicalNatEqualityFlag raw)

private theorem run_canonicalNatEqualityProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatEqualityProgram
        (canonicalNatEqualityBits inputLength raw)
        (canonicalNatEqualityFuel raw)
        (initialNPOracleState inputLength
          (canonicalNatEqualityInput raw)) =
      some
        (Nat.pair
          (canonicalNatEqualityFlag raw)
          (canonicalNatCandidate raw)) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength
      (encodeNat (canonicalNatCandidate raw)) raw)
    (nativeNatEqFuel
      (encodeNat (canonicalNatCandidate raw)) raw)
    (nativeNatEqInput
      (encodeNat (canonicalNatCandidate raw)) raw)
    (canonicalNatCandidate raw)
    (canonicalNatEqualityFlag raw)
    (run_nativeNatEqProgram inputLength
      (encodeNat (canonicalNatCandidate raw)) raw)

/-! ## Collapse the equality flag to the public presence-tagged result -/

private def canonicalNatValidationGateOutput
    (flag candidate : ℕ) : ℕ :=
  if flag = 0 then 0 else Nat.pair 1 candidate

def canonicalNatValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 5 2
  , .unpairRight 0 3 3
  , .set 4 1 4
  , .pair 4 3 0 6
  , .set 0 0 6
  , .halt 0
  ]

private def canonicalNatValidationGateBits
    (flag candidate : ℕ) : ℕ :=
  max 1 <| max (natBitLength (Nat.pair flag candidate)) <|
    max (natBitLength candidate)
      (natBitLength (Nat.pair 1 candidate))

private theorem canonicalNatValidationGateProgram_oracleFree :
    OracleFree canonicalNatValidationGateProgram := by
  rfl

private theorem run_canonicalNatValidationGateProgram
    (inputLength flag candidate : ℕ) :
    runNPOracleProgram canonicalNatValidationGateProgram
        (canonicalNatValidationGateBits flag candidate) 6
        (initialNPOracleState inputLength
          (Nat.pair flag candidate)) =
      some (canonicalNatValidationGateOutput flag candidate) := by
  let maximumBits :=
    canonicalNatValidationGateBits flag candidate
  have hflag : natBitLength flag ≤ maximumBits := by
    apply
      (natBitLength_mono (Nat.left_le_pair flag candidate)).trans
    simp [maximumBits, canonicalNatValidationGateBits]
  have hcandidate : natBitLength candidate ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationGateBits]
  have hone : natBitLength 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationGateBits, natBitLength]
  have hzero : natBitLength 0 ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationGateBits, natBitLength]
  have hsuccess :
      natBitLength (Nat.pair 1 candidate) ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationGateBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := flag)
    (by rfl) rfl (by simp [initialNPOracleState]) hflag]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show
    (((initialNPOracleState inputLength
      (Nat.pair flag candidate)).write 2 flag).jump 1).registers 2 =
      flag by simp]
  by_cases hflagZero : flag = 0
  · rw [if_pos hflagZero]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_set_instruction (value := 0)
      (by rfl) rfl hzero]
    rw [show canonicalNatValidationGateOutput flag candidate = 0 by
      simp [canonicalNatValidationGateOutput, hflagZero]]
    exact run_halt_instruction (fuel := 2) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · rw [if_neg hflagZero]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_unpairRight_instruction (value := candidate)
      (by rfl) rfl
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hcandidate]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_set_instruction (value := 1)
      (by rfl) rfl hone]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_pair_instruction (value := Nat.pair 1 candidate)
      (by rfl) rfl
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hsuccess]
    rw [show canonicalNatValidationGateOutput flag candidate =
        Nat.pair 1 candidate by
      simp [canonicalNatValidationGateOutput, hflagZero]]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hsuccess

private theorem canonicalNatValidationGateOutput_eq
    (raw : ℕ) :
    canonicalNatValidationGateOutput
        (canonicalNatEqualityFlag raw)
        (canonicalNatCandidate raw) =
      canonicalNatValidationOutput raw := by
  unfold canonicalNatEqualityFlag nativeNatEqOutput
  unfold canonicalNatValidationGateOutput
  unfold canonicalNatValidationOutput
  by_cases hcanonical :
      encodeNat (canonicalNatCandidate raw) = raw
  · simp [hcanonical]
  · simp [hcanonical]

/-! ## Sole public total validator -/

def canonicalNatValidationProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms candidateWithRawProgram
        canonicalNatEqualityPrepareProgram)
      canonicalNatEqualityProgram)
    canonicalNatValidationGateProgram

@[simp] theorem canonicalNatValidationProgram_oracleFree :
    OracleFree canonicalNatValidationProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        candidateWithRawProgram_oracleFree
        canonicalNatEqualityPrepareProgram_oracleFree)
      canonicalNatEqualityProgram_oracleFree)
    canonicalNatValidationGateProgram_oracleFree

def canonicalNatValidationFuel (raw : ℕ) : ℕ :=
  linkFuel canonicalNatValidationGateProgram
    (linkFuel canonicalNatEqualityProgram
      (linkFuel canonicalNatEqualityPrepareProgram
        (candidateWithRawFuel raw) 6)
      (canonicalNatEqualityFuel raw))
    6

def canonicalNatValidationBits
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (candidateWithRawBits inputLength raw) <|
      max (canonicalNatEqualityPrepareBits inputLength raw) <|
        max (canonicalNatEqualityBits inputLength raw)
          (canonicalNatValidationGateBits
            (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw))

theorem run_canonicalNatValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatValidationProgram
        (canonicalNatValidationBits inputLength raw)
        (canonicalNatValidationFuel raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalNatValidationOutput raw) := by
  let maximumBits := canonicalNatValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hcandidate :
      candidateWithRawBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hprepare :
      canonicalNatEqualityPrepareBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hequality :
      canonicalNatEqualityBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hgate :
      canonicalNatValidationGateBits
          (canonicalNatEqualityFlag raw)
          (canonicalNatCandidate raw) ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationBits]
  have hfirst :
      runNPOracleProgram candidateWithRawProgram maximumBits
          (candidateWithRawFuel raw)
          (initialNPOracleState inputLength raw) =
        some (Nat.pair (canonicalNatCandidate raw) raw) := by
    exact run_bits_mono
      (run_candidateWithRawProgram inputLength raw) hcandidate
  have hsecond :
      runNPOracleProgram canonicalNatEqualityPrepareProgram
          maximumBits 6
          (initialNPOracleState inputLength
            (Nat.pair (canonicalNatCandidate raw) raw)) =
        some (canonicalNatEqualityInput raw) := by
    exact run_bits_mono
      (run_canonicalNatEqualityPrepareProgram inputLength raw) hprepare
  have hfirstSecond :
      runNPOracleProgram
          (linkPrograms candidateWithRawProgram
            canonicalNatEqualityPrepareProgram)
          maximumBits
          (linkFuel canonicalNatEqualityPrepareProgram
            (candidateWithRawFuel raw) 6)
          (initialNPOracleState inputLength raw) =
        some (canonicalNatEqualityInput raw) :=
    run_linkPrograms hpositive hlength hfirst hsecond
  have hthird :
      runNPOracleProgram canonicalNatEqualityProgram maximumBits
          (canonicalNatEqualityFuel raw)
          (initialNPOracleState inputLength
            (canonicalNatEqualityInput raw)) =
        some
          (Nat.pair
            (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw)) := by
    exact run_bits_mono
      (run_canonicalNatEqualityProgram inputLength raw) hequality
  have hfirstThird :
      runNPOracleProgram
          (linkPrograms
            (linkPrograms candidateWithRawProgram
              canonicalNatEqualityPrepareProgram)
            canonicalNatEqualityProgram)
          maximumBits
          (linkFuel canonicalNatEqualityProgram
            (linkFuel canonicalNatEqualityPrepareProgram
              (candidateWithRawFuel raw) 6)
            (canonicalNatEqualityFuel raw))
          (initialNPOracleState inputLength raw) =
        some
          (Nat.pair
            (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw)) :=
    run_linkPrograms hpositive hlength hfirstSecond hthird
  have hfourth :
      runNPOracleProgram canonicalNatValidationGateProgram
          maximumBits 6
          (initialNPOracleState inputLength
            (Nat.pair
              (canonicalNatEqualityFlag raw)
              (canonicalNatCandidate raw))) =
        some (canonicalNatValidationOutput raw) := by
    rw [← canonicalNatValidationGateOutput_eq raw]
    exact run_bits_mono
      (run_canonicalNatValidationGateProgram inputLength
        (canonicalNatEqualityFlag raw)
        (canonicalNatCandidate raw))
      hgate
  exact run_linkPrograms hpositive hlength hfirstThird hfourth

/-- Successful output carries the unique decoded natural, while zero is the
only malformed result. -/
theorem canonicalNatValidationOutput_eq_pair_iff
    (raw value : ℕ) :
    canonicalNatValidationOutput raw = Nat.pair 1 value ↔
      decodeNat raw = some value := by
  constructor
  · intro houtput
    have hpairPositive : 0 < Nat.pair 1 value :=
      (show 0 < 1 by omega).trans_le (Nat.left_le_pair 1 value)
    have hnonzero : canonicalNatValidationOutput raw ≠ 0 := by
      rw [houtput]
      exact hpairPositive.ne'
    obtain ⟨decoded, hdecode⟩ :=
      (canonicalNatValidationOutput_ne_zero_iff raw).1 hnonzero
    have hdecodedOutput :=
      canonicalNatValidationOutput_of_decode hdecode
    rw [houtput] at hdecodedOutput
    have hvalue : decoded = value := by
      simpa using
        congrArg (fun code => (Nat.unpair code).2)
          hdecodedOutput.symm
    simpa [hvalue] using hdecode
  · exact canonicalNatValidationOutput_of_decode

end NearCubicWires.CanonicalNatValidationProgram
