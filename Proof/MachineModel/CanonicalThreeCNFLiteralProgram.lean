import Proof.MachineModel.CanonicalEncodedListLookupProgram
import Proof.MachineModel.CanonicalLiteralDecodeProgram

/-!
# Fixed pointwise `ThreeCNF` literal decoder

This is the complete codec boundary for one decision-runner literal.  The first
fixed callee traverses the outer clause spine and inner literal spine; the
second fixed callee applies the exact public literal decoder.  Arity is carried
through the first stage with the shared preserving adapter, so no host decode
or duplicate list cursor appears between the two interpreters.
-/

namespace NearCubicWires.CanonicalThreeCNFLiteralProgram

open NearCubicWires
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalLiteralDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def threeCNFLiteralInput
    (arity code clauseIndex position : ℕ) : ℕ :=
  Nat.pair
    (encodedNestedListLookupInput code clauseIndex position 0)
    arity

def threeCNFLiteralRawCode
    (code clauseIndex position : ℕ) : ℕ :=
  encodedNestedListGetD code clauseIndex position 0

def threeCNFLiteralOutput
    (arity code clauseIndex position : ℕ) : ℕ :=
  literalDecodeOutput arity <|
    threeCNFLiteralRawCode code clauseIndex position

def threeCNFLiteralProgram : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram encodedNestedListLookupProgram)
    literalDecodeProgram

@[simp] theorem threeCNFLiteralProgram_oracleFree :
    OracleFree threeCNFLiteralProgram := by
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree encodedNestedListLookupProgram
      encodedNestedListLookupProgram_oracleFree)
    literalDecodeProgram_oracleFree

def threeCNFLiteralFuel
    (arity code clauseIndex position : ℕ) : ℕ :=
  let rawCode := threeCNFLiteralRawCode code clauseIndex position
  linkFuel literalDecodeProgram
    (preserveRightFuel <|
      encodedNestedListLookupFuel code clauseIndex position)
    (literalDecodeFuel arity rawCode)

theorem threeCNFLiteralFuel_le
    (arity code clauseIndex position : ℕ) :
    threeCNFLiteralFuel arity code clauseIndex position ≤
      7 *
          (clauseIndex + position +
            (Nat.unpair
              (threeCNFLiteralRawCode code clauseIndex position)).2) +
        139 := by
  let rawCode := threeCNFLiteralRawCode code clauseIndex position
  have hdecodeSpan :
      programRegisterSpan literalDecodeProgram = 23 := by
    set_option maxRecDepth 10000 in
      decide
  rw [threeCNFLiteralFuel, linkFuel_exact, hdecodeSpan]
  have hlookup :=
    encodedNestedListLookupFuel_le code clauseIndex position
  have hdecode := literalDecodeFuel_le arity rawCode
  dsimp only [rawCode] at hdecode
  simp only [PreserveRightProgram.preserveRightFuel] at *
  omega

def threeCNFLiteralBits
    (inputLength arity code clauseIndex position : ℕ) : ℕ :=
  let lookupInput :=
    encodedNestedListLookupInput code clauseIndex position 0
  let rawCode := threeCNFLiteralRawCode code clauseIndex position
  let lookupBits :=
    encodedNestedListLookupBits inputLength code clauseIndex position 0
  max (natBitLength inputLength) <|
    max
      (preserveRightBits lookupBits lookupInput arity rawCode)
      (literalDecodeBits inputLength arity rawCode)

theorem run_threeCNFLiteralProgram
    (inputLength arity code clauseIndex position : ℕ)
    (harity : 0 < arity) :
    runNPOracleProgram threeCNFLiteralProgram
        (threeCNFLiteralBits inputLength arity code clauseIndex position)
        (threeCNFLiteralFuel arity code clauseIndex position)
        (initialNPOracleState inputLength
          (threeCNFLiteralInput arity code clauseIndex position)) =
      some (threeCNFLiteralOutput arity code clauseIndex position) := by
  let lookupInput :=
    encodedNestedListLookupInput code clauseIndex position 0
  let rawCode := threeCNFLiteralRawCode code clauseIndex position
  let lookupBits :=
    encodedNestedListLookupBits inputLength code clauseIndex position 0
  let wrappedBits :=
    preserveRightBits lookupBits lookupInput arity rawCode
  let decodeBits := literalDecodeBits inputLength arity rawCode
  let maximumBits :=
    threeCNFLiteralBits inputLength arity code clauseIndex position
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hwrappedBits : wrappedBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdecodeBits : decodeBits ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hlookup :
      runNPOracleProgram encodedNestedListLookupProgram lookupBits
          (encodedNestedListLookupFuel code clauseIndex position)
          (initialNPOracleState inputLength lookupInput) =
        some rawCode := by
    simpa only [lookupBits, lookupInput, rawCode,
      threeCNFLiteralRawCode] using
        run_encodedNestedListLookupProgram inputLength code
          clauseIndex position 0
  have hwrappedAtOwnBits :
      runNPOracleProgram
          (preserveRightProgram encodedNestedListLookupProgram)
          wrappedBits
          (preserveRightFuel <|
            encodedNestedListLookupFuel code clauseIndex position)
          (initialNPOracleState inputLength
            (Nat.pair lookupInput arity)) =
        some (Nat.pair rawCode arity) := by
    exact run_preserveRightProgram encodedNestedListLookupProgram
      inputLength lookupBits
      (encodedNestedListLookupFuel code clauseIndex position)
      lookupInput arity rawCode hlookup
  have hwrapped :
      runNPOracleProgram
          (preserveRightProgram encodedNestedListLookupProgram)
          maximumBits
          (preserveRightFuel <|
            encodedNestedListLookupFuel code clauseIndex position)
          (initialNPOracleState inputLength
            (Nat.pair lookupInput arity)) =
        some (Nat.pair rawCode arity) :=
    run_bits_mono hwrappedAtOwnBits hwrappedBits
  have hdecodeAtOwnBits :
      runNPOracleProgram literalDecodeProgram decodeBits
          (literalDecodeFuel arity rawCode)
          (initialNPOracleState inputLength
            (Nat.pair rawCode arity)) =
        some (literalDecodeOutput arity rawCode) := by
    simpa only [decodeBits, literalDecodeInput] using
      run_literalDecodeProgram inputLength arity rawCode harity
  have hdecode :
      runNPOracleProgram literalDecodeProgram maximumBits
          (literalDecodeFuel arity rawCode)
          (initialNPOracleState inputLength
            (Nat.pair rawCode arity)) =
        some (literalDecodeOutput arity rawCode) :=
    run_bits_mono hdecodeAtOwnBits hdecodeBits
  change
    runNPOracleProgram
        (linkPrograms
          (preserveRightProgram encodedNestedListLookupProgram)
          literalDecodeProgram)
        maximumBits
        (linkFuel literalDecodeProgram
          (preserveRightFuel <|
            encodedNestedListLookupFuel code clauseIndex position)
          (literalDecodeFuel arity rawCode))
        (initialNPOracleState inputLength
          (Nat.pair lookupInput arity)) =
      some (literalDecodeOutput arity rawCode)
  exact run_linkPrograms hpositive hlengthBits hwrapped hdecode

/-- Pointwise semantic closure: the fixed program returns the canonical code of
the exact literal selected by `decodeThreeCNF`, with total fallbacks matching
the public decoder. -/
theorem threeCNFLiteralOutput_eq_decodeThreeCNF
    (arity code clauseIndex : ℕ) (position : Fin 3)
    (harity : 0 < arity) :
    threeCNFLiteralOutput arity code clauseIndex position.val =
      encodeLiteral
        (((decodeThreeCNF arity code).clauses.getD clauseIndex
          (fun _ => decodeLiteral harity 0)) position) := by
  unfold threeCNFLiteralOutput threeCNFLiteralRawCode
  rw [literalDecodeOutput_eq_encodeLiteral arity
    (encodedNestedListGetD code clauseIndex position.val 0) harity]
  congr 1
  exact decodeLiteral_encodedNestedListGetD
    arity code clauseIndex position harity

theorem run_threeCNFLiteralProgram_eq_decodeThreeCNF
    (inputLength arity code clauseIndex : ℕ) (position : Fin 3)
    (harity : 0 < arity) :
    runNPOracleProgram threeCNFLiteralProgram
        (threeCNFLiteralBits inputLength arity code
          clauseIndex position.val)
        (threeCNFLiteralFuel arity code clauseIndex position.val)
        (initialNPOracleState inputLength
          (threeCNFLiteralInput arity code clauseIndex position.val)) =
      some
        (encodeLiteral
          (((decodeThreeCNF arity code).clauses.getD clauseIndex
            (fun _ => decodeLiteral harity 0)) position)) := by
  rw [run_threeCNFLiteralProgram inputLength arity code clauseIndex
    position.val harity]
  exact congrArg some <|
    threeCNFLiteralOutput_eq_decodeThreeCNF
      arity code clauseIndex position harity

end NearCubicWires.CanonicalThreeCNFLiteralProgram
