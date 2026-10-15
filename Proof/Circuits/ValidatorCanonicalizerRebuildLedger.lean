import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBalancedMidpointRebuildProgram
import Proof.Circuits.ValidatorDecodeFoldWidthLedger

/-!
# The candidate pass, with both residual charges repaired

`ValidatorDecodeFoldWidthLedger` §3 leaves the canonical natural validator's
candidate route at exactly one geometric summand.  Its own §1 replaced the
decoder; its §3 named what remained:

> "a traversal-driven midpoint canonicalizer, with no `encodeTaggedList` of a
> public-length list in its width cone — is exactly what remains before the
> candidate pass, and therefore the whole canonical natural validator, is
> polynomially charged."

`CanonicalBalancedMidpointRebuildProgram` is that canonicalizer, at the same
output contract.  This module links it to the repaired decoder and re-walks the
candidate charge with **both** summands replaced.

What is eliminated:

* `ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_balancedCanonicalizeBits`
  and `…_le_balancedRawCanonicalizeBits` floor the *old* canonicalizer through
  `balancedClauseStreamFlattenProgram`'s returned value.  The rebuilt
  canonicalizer never runs that flattener, so §2's charge is not floored by
  either;

* `two_pow_length_le_taggedToBalancedRegisterBitsFor` floors the *old*
  midpoint builder through its input register.  The rebuilt canonicalizer never
  runs `taggedToBalancedProgram` either, so §4's honest floor is moot on this
  route.

* §1 the rebuilt candidate pass.

* §2 the candidate width, in balanced measurements only.

* §3 the seam that is left: what the charge still mentions, and where.

* §4 the validator's first link, restated over the rebuilt candidate pass.
-/

namespace NearCubicWires.ValidatorCanonicalizerRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalNatDecodeFoldProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

open private duplicateRawBits run_duplicateRawProgram
  duplicateRawProgram_oracleFree canonicalNatEqualityInput
  canonicalNatEqualityPrepareBits run_canonicalNatEqualityPrepareProgram
  canonicalNatEqualityPrepareProgram_oracleFree canonicalNatEqualityFlag
  canonicalNatEqualityBits run_canonicalNatEqualityProgram
  canonicalNatEqualityProgram_oracleFree canonicalNatValidationGateBits
  run_canonicalNatValidationGateProgram
  canonicalNatValidationGateProgram_oracleFree
  canonicalNatValidationGateOutput_eq from
  Proof.MachineModel.CanonicalNatValidationProgram

/-! ## §1 The rebuilt candidate pass -/

/-- The candidate pass with both stages repaired: the indexed midpoint
canonicalizer, then the traversal-driven decoder. -/
def canonicalNatCandidateRebuildProgram : NPOracleProgram :=
  linkPrograms balancedRawCanonicalizeFoldProgram
    canonicalNatDecodeFoldProgram

@[simp] theorem canonicalNatCandidateRebuildProgram_oracleFree :
    OracleFree canonicalNatCandidateRebuildProgram :=
  oracleFree_linkPrograms balancedRawCanonicalizeFoldProgram_oracleFree
    canonicalNatDecodeFoldProgram_oracleFree

def canonicalNatCandidateRebuildFuel (inputLength raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  linkFuel canonicalNatDecodeFoldProgram
    (balancedRawCanonicalizeFoldFuel inputLength tree)
    (canonicalNatDecodeFoldListFuel tree.atoms)

def canonicalNatCandidateRebuildBits (inputLength raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  max 1 <| max (natBitLength inputLength) <|
    max (balancedRawCanonicalizeFoldBits inputLength tree)
      (canonicalNatDecodeFoldListBits inputLength tree.atoms)

/-- **The rebuilt candidate pass returns the published candidate.**  The output
contract is `CanonicalNatValidationProgram`'s own `canonicalNatCandidate`,
unchanged — as is `ValidatorDecodeFoldWidthLedger`'s. -/
theorem run_canonicalNatCandidateRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatCandidateRebuildProgram
        (canonicalNatCandidateRebuildBits inputLength raw)
        (canonicalNatCandidateRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalNatCandidate raw) := by
  let tree := rawBalancedTraversalTree raw
  let maximumBits := canonicalNatCandidateRebuildBits inputLength raw
  have hvalid : tree.Valid := rawBalancedTraversalTree_valid raw
  have hcode : tree.rawCode = raw := rawBalancedTraversalTree_rawCode raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateRebuildBits]
  have hnormalize :
      balancedRawCanonicalizeFoldBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateRebuildBits, tree]
  have hdecode :
      canonicalNatDecodeFoldListBits inputLength tree.atoms ≤ maximumBits := by
    simp [maximumBits, canonicalNatCandidateRebuildBits, tree]
  apply run_linkPrograms hpositive hlength
  · simpa [hcode] using
      run_bits_mono
        (run_balancedRawCanonicalizeFoldProgram inputLength tree hvalid)
        hnormalize
  · simpa [canonicalNatCandidate, tree] using
      run_bits_mono
        (run_canonicalNatDecodeFoldProgram_fromList inputLength tree.atoms)
        hdecode

/-! ## §2 The candidate width, in balanced measurements only -/

/-- The two summands, isolated. -/
theorem canonicalNatCandidateRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound) :
    canonicalNatCandidateRebuildBits inputLength raw ≤
      max
        (max
          (balancedRawCanonicalizeFoldBits inputLength
            (rawBalancedTraversalTree raw))
          (canonicalNatDecodeFoldListBits inputLength
            (rawBalancedTraversalTree raw).atoms))
        bound := by
  simp only [canonicalNatCandidateRebuildBits]
  omega

/-- **The rebuilt candidate charge, in balanced measurements.**  Every summand
is one of the repository's standard traversal-shaped charges or one fixed
polynomial; none of them is `encodeTaggedList` of the public atom list, so
`ValidatorTaggedIntermediateVerdict`'s geometric floors do not apply to any of
them.

Read against
`ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_canonicalNatCandidateBits_of_run`,
which floors the *original* candidate charge at `2 ^ atoms.length`. -/
theorem canonicalNatCandidateRebuildBits_le_measurements
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound) :
    canonicalNatCandidateRebuildBits inputLength raw ≤
      max
        (max
          (balancedStructuralNormalizeBits inputLength
            (rawBalancedTraversalTree raw))
          (max
            (2 * balancedAtomCountBits inputLength
              (rawBalancedTraversalTree raw).normalized)
            (max
              (indexedAtomListBits inputLength
                (rawBalancedTraversalTree raw).atoms.length
                (rawBalancedTraversalTree raw).normalized.code
                (fun index =>
                  Nat.pair index
                    (rawBalancedTraversalTree raw).normalized.code))
              (max
                (balancedCallPolynomialBits
                  (atomIndexOutput (rawBalancedTraversalTree raw).normalized)
                  (atomIndexRequests
                    (rawBalancedTraversalTree raw).normalized))
                (atomIndexRequestBits
                  (rawBalancedTraversalTree raw).normalized)))))
        (max
          (max
            (balancedCallPolynomialBits (fun value => value)
              (rawBalancedTraversalTree raw).atoms)
            (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)))
          bound) := by
  have hstage :=
    canonicalNatCandidateRebuildBits_le (inputLength := inputLength)
      (raw := raw) hpositive hlength
  have hcanonicalize :=
    balancedRawCanonicalizeFoldBits_le inputLength (rawBalancedTraversalTree raw)
  have hdecode :=
    canonicalNatDecodeFoldListBits_le_polynomial inputLength
      (rawBalancedTraversalTree raw).atoms
  have hatoms :
      (rawBalancedTraversalTree raw).normalized.atoms =
        (rawBalancedTraversalTree raw).atoms := rfl
  rw [hatoms] at hcanonicalize
  omega

/-! ## §3 The seam that is left

§2 states the rebuilt candidate charge with **no** geometric summand.  What the
charge still mentions is exactly four things:

* `balancedStructuralNormalizeBits` — the raw front door's own traversal
  charge, which the candidate route already paid before this repair and which
  `ValidatorNatWidthLedger` §3 never listed as residual;

* `balancedAtomCountBits` — one balanced-traversal charge over the same tree,
  which is the shape `CanonicalBalancedCall` closes;

* `indexedAtomListBits` and `balancedCallPolynomialBits` — the generated
  request list and the balanced call over it, both of them midpoint-balanced
  and both already carrying the repository's fixed polynomial closure;

* `atomIndexRequestBits` — the width of one request `Nat.pair index code`.

The remaining chain to `hcall` is unchanged in shape: the candidate pass feeds
`canonicalNatValidationBits` through `candidateWithRawBits`, which feeds
`booleanCircuitValidationBits`, which
`ValidatorTraversalWidthLedger.booleanCircuitValidationBits_le_recoveryOracleCallBits`
feeds to `recoveryOracleCallBits`.  Two of those three links are decoder- and
canonicalizer-agnostic and restate verbatim over the programs of §1. -/

/-- **The canonicalizer summand is discharged.**  Any bound on the four
measurements of §2 lifts to the rebuilt candidate pass; this is the drop-in
analogue of
`ValidatorDecodeFoldWidthLedger.canonicalNatCandidateFoldBits_le_of_canonicalizeBits_le`
with its hypothesis now supplied rather than assumed. -/
theorem canonicalNatCandidateRebuildBits_le_of_measurements_le
    {inputLength raw bound canonicalizeBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hnormalize :
      balancedStructuralNormalizeBits inputLength
        (rawBalancedTraversalTree raw) ≤ canonicalizeBound)
    (hcount :
      2 * balancedAtomCountBits inputLength
        (rawBalancedTraversalTree raw).normalized ≤ canonicalizeBound)
    (hrange :
      indexedAtomListBits inputLength
        (rawBalancedTraversalTree raw).atoms.length
        (rawBalancedTraversalTree raw).normalized.code
        (fun index =>
          Nat.pair index (rawBalancedTraversalTree raw).normalized.code) ≤
        canonicalizeBound)
    (hcall :
      balancedCallPolynomialBits
        (atomIndexOutput (rawBalancedTraversalTree raw).normalized)
        (atomIndexRequests (rawBalancedTraversalTree raw).normalized) ≤
        canonicalizeBound)
    (hrequest :
      atomIndexRequestBits (rawBalancedTraversalTree raw).normalized ≤
        canonicalizeBound) :
    canonicalNatCandidateRebuildBits inputLength raw ≤
      max canonicalizeBound
        (max
          (max
            (balancedCallPolynomialBits (fun value => value)
              (rawBalancedTraversalTree raw).atoms)
            (2 * ((rawBalancedTraversalTree raw).atoms.length + 1)))
          bound) := by
  have hstage :=
    canonicalNatCandidateRebuildBits_le_measurements
      (inputLength := inputLength) (raw := raw) hpositive hlength
  omega

/-! ## §4 The validator's first link, restated

`CanonicalNatValidationProgram` links four stages, and only the first — the
candidate pass under `preserveRightProgram` — mentions the decoder or the
canonicalizer.  The other three are stated at the candidate's *value*, so they
reuse verbatim.  §4 restates the first link over §1's program and re-assembles
the same public validator at the same output. -/

/-- The rebuilt candidate pass, retaining the untrusted word. -/
def candidateWithRawRebuildProgram : NPOracleProgram :=
  linkPrograms duplicateRawProgram <|
    preserveRightProgram canonicalNatCandidateRebuildProgram

@[simp] theorem candidateWithRawRebuildProgram_oracleFree :
    OracleFree candidateWithRawRebuildProgram :=
  oracleFree_linkPrograms duplicateRawProgram_oracleFree <|
    preserveRightProgram_oracleFree canonicalNatCandidateRebuildProgram
      canonicalNatCandidateRebuildProgram_oracleFree

def candidateWithRawRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel (preserveRightProgram canonicalNatCandidateRebuildProgram) 2 <|
    preserveRightFuel (canonicalNatCandidateRebuildFuel inputLength raw)

def candidateWithRawRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (duplicateRawBits raw)
      (preserveRightBits (canonicalNatCandidateRebuildBits inputLength raw)
        raw raw (canonicalNatCandidate raw))

theorem run_candidateWithRawRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram candidateWithRawRebuildProgram
        (candidateWithRawRebuildBits inputLength raw)
        (candidateWithRawRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (Nat.pair (canonicalNatCandidate raw) raw) := by
  let maximumBits := candidateWithRawRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, candidateWithRawRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, candidateWithRawRebuildBits]
  have hduplicate : duplicateRawBits raw ≤ maximumBits := by
    simp [maximumBits, candidateWithRawRebuildBits]
  have hpreserve :
      preserveRightBits (canonicalNatCandidateRebuildBits inputLength raw)
          raw raw (canonicalNatCandidate raw) ≤ maximumBits := by
    simp [maximumBits, candidateWithRawRebuildBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono (run_duplicateRawProgram inputLength raw) hduplicate
  · exact run_bits_mono
      (run_preserveRightProgram canonicalNatCandidateRebuildProgram inputLength
        (canonicalNatCandidateRebuildBits inputLength raw)
        (canonicalNatCandidateRebuildFuel inputLength raw)
        raw raw (canonicalNatCandidate raw)
        (run_canonicalNatCandidateRebuildProgram inputLength raw))
      hpreserve

/-- **The public natural validator, over the rebuilt candidate pass.** -/
def canonicalNatValidationRebuildProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms candidateWithRawRebuildProgram
        canonicalNatEqualityPrepareProgram)
      canonicalNatEqualityProgram)
    canonicalNatValidationGateProgram

@[simp] theorem canonicalNatValidationRebuildProgram_oracleFree :
    OracleFree canonicalNatValidationRebuildProgram :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms candidateWithRawRebuildProgram_oracleFree
        canonicalNatEqualityPrepareProgram_oracleFree)
      canonicalNatEqualityProgram_oracleFree)
    canonicalNatValidationGateProgram_oracleFree

def canonicalNatValidationRebuildFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel canonicalNatValidationGateProgram
    (linkFuel canonicalNatEqualityProgram
      (linkFuel canonicalNatEqualityPrepareProgram
        (candidateWithRawRebuildFuel inputLength raw) 6)
      (canonicalNatEqualityFuel raw))
    6

/-- **The repaired validator's charge.**  Exactly `canonicalNatValidationBits`
with its first entry replaced; the other three entries are the frozen ones. -/
def canonicalNatValidationRebuildBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (candidateWithRawRebuildBits inputLength raw) <|
      max (canonicalNatEqualityPrepareBits inputLength raw) <|
        max (canonicalNatEqualityBits inputLength raw)
          (canonicalNatValidationGateBits (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw))

/-- **The repaired validator returns the published verdict.** -/
theorem run_canonicalNatValidationRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram canonicalNatValidationRebuildProgram
        (canonicalNatValidationRebuildBits inputLength raw)
        (canonicalNatValidationRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (canonicalNatValidationOutput raw) := by
  let maximumBits := canonicalNatValidationRebuildBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hcandidate :
      candidateWithRawRebuildBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hprepare :
      canonicalNatEqualityPrepareBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hequality :
      canonicalNatEqualityBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hgate :
      canonicalNatValidationGateBits (canonicalNatEqualityFlag raw)
          (canonicalNatCandidate raw) ≤ maximumBits := by
    simp [maximumBits, canonicalNatValidationRebuildBits]
  have hfirst :
      runNPOracleProgram candidateWithRawRebuildProgram maximumBits
          (candidateWithRawRebuildFuel inputLength raw)
          (initialNPOracleState inputLength raw) =
        some (Nat.pair (canonicalNatCandidate raw) raw) :=
    run_bits_mono (run_candidateWithRawRebuildProgram inputLength raw)
      hcandidate
  have hsecond :
      runNPOracleProgram canonicalNatEqualityPrepareProgram maximumBits 6
          (initialNPOracleState inputLength
            (Nat.pair (canonicalNatCandidate raw) raw)) =
        some (canonicalNatEqualityInput raw) :=
    run_bits_mono (run_canonicalNatEqualityPrepareProgram inputLength raw)
      hprepare
  have hfirstSecond :=
    run_linkPrograms hpositive hlength hfirst hsecond
  have hthird :
      runNPOracleProgram canonicalNatEqualityProgram maximumBits
          (canonicalNatEqualityFuel raw)
          (initialNPOracleState inputLength
            (canonicalNatEqualityInput raw)) =
        some
          (Nat.pair (canonicalNatEqualityFlag raw)
            (canonicalNatCandidate raw)) :=
    run_bits_mono (run_canonicalNatEqualityProgram inputLength raw) hequality
  have hfirstThird :=
    run_linkPrograms hpositive hlength hfirstSecond hthird
  have hfourth :
      runNPOracleProgram canonicalNatValidationGateProgram maximumBits 6
          (initialNPOracleState inputLength
            (Nat.pair (canonicalNatEqualityFlag raw)
              (canonicalNatCandidate raw))) =
        some (canonicalNatValidationOutput raw) := by
    rw [← canonicalNatValidationGateOutput_eq raw]
    exact run_bits_mono
      (run_canonicalNatValidationGateProgram inputLength
        (canonicalNatEqualityFlag raw) (canonicalNatCandidate raw))
      hgate
  exact run_linkPrograms hpositive hlength hfirstThird hfourth

theorem canonicalNatValidationRebuildBits_le_candidate
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hduplicate : duplicateRawBits raw ≤ bound)
    (hpreserve :
      preserveRightBits (canonicalNatCandidateRebuildBits inputLength raw)
        raw raw (canonicalNatCandidate raw) ≤
        max (canonicalNatCandidateRebuildBits inputLength raw) bound)
    (hprepare : canonicalNatEqualityPrepareBits inputLength raw ≤ bound)
    (hequality : canonicalNatEqualityBits inputLength raw ≤ bound)
    (hgate :
      canonicalNatValidationGateBits (canonicalNatEqualityFlag raw)
        (canonicalNatCandidate raw) ≤ bound) :
    canonicalNatValidationRebuildBits inputLength raw ≤
      max (canonicalNatCandidateRebuildBits inputLength raw) bound := by
  simp only [canonicalNatValidationRebuildBits, candidateWithRawRebuildBits]
  omega

end NearCubicWires.ValidatorCanonicalizerRebuildLedger
