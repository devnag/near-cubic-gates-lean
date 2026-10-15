import Proof.MachineModel.CanonicalNatDecodeFoldProgram
import Proof.Circuits.ValidatorTaggedIntermediateVerdict

namespace NearCubicWires.ValidatorDecodeFoldWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeFoldProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.ValidatorTaggedIntermediateVerdict
open NearCubicWires.ValidatorTraversalWidthLedger
open NearCubicWires.VerifiedLinker

/-! ## §1 The repaired candidate pass -/

/-- The same two-stage link `CanonicalNatValidationProgram` publishes, with the
traversal-driven decoder in place of the tagged one. -/
def canonicalNatCandidateFoldProgram : NPOracleProgram :=
  linkPrograms balancedRawCanonicalizeProgram canonicalNatDecodeFoldProgram

@[simp] theorem canonicalNatCandidateFoldProgram_oracleFree :
    OracleFree canonicalNatCandidateFoldProgram :=
  oracleFree_linkPrograms balancedRawCanonicalizeProgram_oracleFree
    canonicalNatDecodeFoldProgram_oracleFree

def canonicalNatCandidateFoldFuel (raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  linkFuel canonicalNatDecodeFoldProgram
    (balancedRawCanonicalizeFuel tree)
    (canonicalNatDecodeFoldListFuel tree.atoms)

def canonicalNatCandidateFoldBits (inputLength raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  max 1 <| max (natBitLength inputLength) <|
    max (balancedRawCanonicalizeBits inputLength tree)
      (canonicalNatDecodeFoldListBits inputLength tree.atoms)

/-- **The repaired candidate pass returns the published candidate.**  The
output contract is `CanonicalNatValidationProgram`'s own
`canonicalNatCandidate`, unchanged. -/
theorem run_canonicalNatCandidateFoldProgram (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatCandidateFoldProgram
        (canonicalNatCandidateFoldBits inputLength raw)
        (canonicalNatCandidateFoldFuel raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalNatCandidate raw) := by
  let tree := rawBalancedTraversalTree raw
  let maximumBits := canonicalNatCandidateFoldBits inputLength raw
  have hvalid : tree.Valid := rawBalancedTraversalTree_valid raw
  have hcode : tree.rawCode = raw := rawBalancedTraversalTree_rawCode raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateFoldBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateFoldBits]
  have hnormalize :
      balancedRawCanonicalizeBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateFoldBits, tree]
  have hdecode :
      canonicalNatDecodeFoldListBits inputLength tree.atoms ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateFoldBits, tree]
  apply run_linkPrograms hpositive hlength
  · simpa [hcode] using
      run_bits_mono
        (run_balancedRawCanonicalizeProgram inputLength tree hvalid)
        hnormalize
  · simpa [canonicalNatCandidate, tree] using
      run_bits_mono
        (run_canonicalNatDecodeFoldProgram_fromList inputLength tree.atoms)
        hdecode

theorem canonicalNatCandidateFoldBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound) :
    canonicalNatCandidateFoldBits inputLength raw ≤
      max
        (max
          (balancedRawCanonicalizeBits inputLength
            (rawBalancedTraversalTree raw))
          (canonicalNatDecodeFoldListBits inputLength
            (rawBalancedTraversalTree raw).atoms))
        bound := by
  simp only [canonicalNatCandidateFoldBits]
  omega

/-- **The decode summand is polynomial, at the raw code.**  Nothing in the
repaired candidate pass's decode leg is geometric in the atom count. -/
theorem canonicalNatDecodeFoldListBits_atoms_le_polynomial
    (inputLength raw : ℕ) :
    canonicalNatDecodeFoldListBits inputLength
        (rawBalancedTraversalTree raw).atoms ≤
      max (natBitLength inputLength)
        (max
          (balancedCallPolynomialBits (fun value => value)
            (rawBalancedTraversalTree raw).atoms)
          (2 * ((rawBalancedTraversalTree raw).atoms.length + 1))) :=
  canonicalNatDecodeFoldListBits_le_polynomial inputLength
    (rawBalancedTraversalTree raw).atoms

theorem canonicalNatCandidateFoldBits_le_canonicalizerFrontier
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound) :
    canonicalNatCandidateFoldBits inputLength raw ≤
      max
        (balancedRawCanonicalizeBits inputLength
          (rawBalancedTraversalTree raw))
        (max
          (max
            (balancedCallPolynomialBits (fun value => value)
              (rawBalancedTraversalTree raw).atoms)
            (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)))
          bound) := by
  have hstage := canonicalNatCandidateFoldBits_le (raw := raw) hpositive hlength
  have hdecode := canonicalNatDecodeFoldListBits_atoms_le_polynomial inputLength raw
  omega

/-! ## §3 The seam

§2 states the repaired candidate charge with one geometric summand left, and
`ValidatorTaggedIntermediateVerdict` §3 shows that summand really is geometric:
`two_pow_atoms_le_balancedRawCanonicalizeBits` floors it at `2 ^ atoms.length`
through the value `balancedClauseStreamFlattenProgram` returns.  So the route-2
repair — a traversal-driven midpoint canonicalizer, with no
`encodeTaggedList` of a public-length list in its width cone — is exactly what
remains before the candidate pass, and therefore the whole canonical natural
validator, is polynomially charged.

The statement below is the seam in one place: it is `hcall`'s domination
premise for the repaired candidate pass, reduced to a premise about the
canonicalizer alone. -/

/-- **The remaining obligation, isolated.**  Any bound on the canonicalizer's
charge lifts to the repaired candidate pass. -/
theorem canonicalNatCandidateFoldBits_le_of_canonicalizeBits_le
    {inputLength raw bound canonicalizeBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hcanonicalize :
      balancedRawCanonicalizeBits inputLength (rawBalancedTraversalTree raw) ≤
        canonicalizeBound) :
    canonicalNatCandidateFoldBits inputLength raw ≤
      max canonicalizeBound
        (max
          (max
            (balancedCallPolynomialBits (fun value => value)
              (rawBalancedTraversalTree raw).atoms)
            (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)))
          bound) := by
  have hstage :=
    canonicalNatCandidateFoldBits_le_canonicalizerFrontier (raw := raw)
      hpositive hlength
  omega

/-- **The canonical family separates the two decoders.**  On
`ValidatorTraversalWidthLedger`'s explicit family the old decode charge is at
least `2 ^ n` while the repaired one is bounded by the fixed balanced-call
polynomial plus a linear fold trace.  So `ValidatorTraversalWidthLedger` §2's
starting lower bound — and with it the decode leg of §6's obstruction — does
not hold of the repaired route. -/
theorem canonicalNatDecodeFoldListBits_canonicalAtomFamily_le
    (inputLength n : ℕ) :
    canonicalNatDecodeFoldListBits inputLength
        (rawBalancedTraversalTree (canonicalAtomFamily n)).atoms ≤
      max (natBitLength inputLength)
        (max
          (balancedCallPolynomialBits (fun value => value)
            (List.replicate n 1))
          (2 * (n + 1))) := by
  rw [atoms_canonicalAtomFamily]
  simpa using
    canonicalNatDecodeFoldListBits_le_polynomial inputLength
      (List.replicate n 1)

/-- The old decode charge on the same family, for comparison: geometric, and
`ValidatorTaggedIntermediateVerdict` derives it from a value the linked
programs actually return. -/
theorem two_pow_le_canonicalNatDecodeListBits_canonicalAtomFamily
    (inputLength n : ℕ) :
    2 ^ n ≤
      canonicalNatDecodeListBits inputLength
        (rawBalancedTraversalTree (canonicalAtomFamily n)).atoms := by
  rw [atoms_canonicalAtomFamily]
  simpa using
    two_pow_length_le_canonicalNatDecodeListBits_of_run inputLength
      (List.replicate n 1)

end NearCubicWires.ValidatorDecodeFoldWidthLedger
