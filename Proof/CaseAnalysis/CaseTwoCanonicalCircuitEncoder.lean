import Proof.MachineModel.CaseTwoDescriptionBitPoolProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# The recovered oracle's own code, from its canonical description

`CaseTwoDescriptionBitPoolProgram` emits the recovered oracle's canonical
bounded-circuit description as a balanced list of bits, from the emitter's atom
stream and the coordinate count alone.  What the Case-2 encoder of
`CaseTwoSubstitutedCircuitEncoder` still needs is that description *read back*
as `encodeBooleanCircuit`.

That last step is purely combinatorial: the description is `bound + 1` rows of
`6 + 2 · (n + bound + 1)` thermometer bits, every field of every row is the sum
of its own block, and the row tag selects between a node code, the output
address and a padding sentinel.  No SAT query, no public length and no schedule
enters it.

§1 names that decoder as one program with one run contract — a *closed*
statement about balanced bit lists, with no target, no branch and no oracle in
it.  §2 links the pool onto it through the canonical right-preserving frame and
proves the composite emits the recovered oracle's own circuit code.  Together
with `RuntimeCaseTwoSubstitutedEncodingClosure.inverseScheduledOccurrenceEncoding_ofRequestWord`
this is the whole circuit half of the Case-2 request word.
-/

namespace NearCubicWires.CaseTwoCanonicalCircuitEncoder

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseTwoDescriptionBitPoolProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The grouping decoder as a closed contract -/

/-- The decoder's request: the balanced list of the canonical description bits
beside the circuit's arity and its size bound. -/
def canonicalDescriptionRequest {n : ℕ} (bound : ℕ)
    (circuit : BooleanCircuit n) : ℕ :=
  Nat.pair
    (encodeBalancedList
      ((canonicalBoundedCircuitDescription bound circuit).map Bool.toNat))
    (Nat.pair n bound)

/-- **The grouping decoder.**  One program that groups a canonical
bounded-circuit description into its rows, decodes each thermometer field, and
returns the circuit's own public code.

The statement quantifies over every arity, every size bound and every circuit
within that bound; it mentions no PCP, no target, no branch and no oracle
query, so discharging it is a self-contained combinatorial obligation.

Every substrate the obligation needs is already published.  A row is
`orderedNatBits 6 tag ++ orderedNatBits limit first ++ orderedNatBits limit
second` with `limit = boundedCircuitFieldLimit n bound`, so each field is the
*sum* of its own block — `CanonicalBalancedNatSumProgram.balancedNatSumProgram`
— and no tagged accumulator is needed anywhere.  Indexing a block is one more
`CanonicalSymmetricRowTableRequestProgram.indexedPoolListProgram` at the offset
`row * rowWidth + start + j`, so the whole decoder is three nested pools.  The
row tag then selects: tags `0`--`4` emit `encodeBooleanNode`'s tagged list and
tags `5`--`6` emit the empty one, so
`BalancedClauseStreamFlattenProgram` concatenates exactly the node codes and no
truncation index is ever computed; and the output address is
`∑ rows (if tag = 5 then first else 0)`, one more balanced sum, because exactly
one row carries the output tag.  `CaseTwoSubstitutedCircuitEncoder.circuitCode`
closes the pair. -/
def CanonicalDescriptionDecoder
    (decoder : NPOracleProgram) (decoderBits decoderFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (inputLength bound n : ℕ) (circuit : BooleanCircuit n),
    circuit.size ≤ bound →
    runNPOracleProgram decoder
        (decoderBits inputLength (canonicalDescriptionRequest bound circuit))
        (decoderFuel inputLength (canonicalDescriptionRequest bound circuit))
        (initialNPOracleState inputLength
          (canonicalDescriptionRequest bound circuit)) =
      some (encodeBooleanCircuit circuit)

/-! ## 2. The encoder -/

/-- **The recovered-oracle encoder.**  The description pool under the canonical
right-preserving frame — so the arity and the size bound survive the pool — and
then the grouping decoder. -/
def canonicalCircuitEncoderProgram (decoder : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram descriptionBitPoolProgram) decoder

/-- The encoder's request: the pool's own range word beside the two numerals
the decoder reads. -/
def canonicalCircuitEncoderInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (sizeBound : ℕ → ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput
      (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
      (descriptionAtomContext pcp input (sizeBound (pcp.nativeWidth n))))
    (Nat.pair (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))

def canonicalCircuitEncoderFuel
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (decoder : NPOracleProgram) (decoderFuel : ℕ → ℕ → ℕ)
    (inputLength : ℕ) : ℕ :=
  linkFuel decoder
    (preserveRightFuel
      (descriptionBitPoolFuel pcp input (sizeBound (pcp.nativeWidth n))
        inputLength
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))))
    (decoderFuel inputLength
      (canonicalDescriptionRequest (sizeBound (pcp.nativeWidth n))
        canonical.circuit))

def canonicalCircuitEncoderBits
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (decoderBits : ℕ → ℕ → ℕ) (inputLength : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits
      (descriptionBitPoolBits pcp input (sizeBound (pcp.nativeWidth n))
        inputLength
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n))))
      (generatedBalancedRangeInput
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
        (descriptionAtomContext pcp input (sizeBound (pcp.nativeWidth n))))
      (Nat.pair (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
      (encodeBalancedList
        ((canonicalBoundedCircuitDescription (sizeBound (pcp.nativeWidth n))
          canonical.circuit).map Bool.toNat)))
    (decoderBits inputLength
      (canonicalDescriptionRequest (sizeBound (pcp.nativeWidth n))
        canonical.circuit))

set_option maxHeartbeats 400000 in
-- The statement carries the pool's own request word, both stage envelopes and
-- the decoder's request at one accepting oracle, so elaborating it alone
-- exceeds the default budget.
/-- **The recovered oracle's own code, executed.**  From the coordinate count,
the emitter's atom stream and the two numerals, the encoder returns exactly
`encodeBooleanCircuit` of the circuit the branch carries.  Every SAT query is
the published prefix-SAT reducer's; the only premise left is the oracle-free
grouping decoder of §1. -/
theorem run_canonicalCircuitEncoderProgram
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (decoder : NPOracleProgram) (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel)
    (inputLength : ℕ) :
    runNPOracleProgram (canonicalCircuitEncoderProgram decoder)
        (canonicalCircuitEncoderBits pcp input canonical decoderBits
          inputLength)
        (canonicalCircuitEncoderFuel pcp input canonical decoder decoderFuel
          inputLength)
        (initialNPOracleState inputLength
          (canonicalCircuitEncoderInput pcp input sizeBound)) =
      some (encodeBooleanCircuit canonical.circuit) := by
  have hpool :=
    run_descriptionBitPoolProgram_eq_canonical pcp input canonical inputLength
      (descriptionBitPoolBits pcp input (sizeBound (pcp.nativeWidth n))
        inputLength
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n))))
      (Nat.le_refl _)
  have hframe :=
    run_preserveRightProgram descriptionBitPoolProgram inputLength
      (descriptionBitPoolBits pcp input (sizeBound (pcp.nativeWidth n))
        inputLength
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n))))
      (descriptionBitPoolFuel pcp input (sizeBound (pcp.nativeWidth n))
        inputLength
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n))))
      (generatedBalancedRangeInput
        (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
        (descriptionAtomContext pcp input (sizeBound (pcp.nativeWidth n))))
      (Nat.pair (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
      (encodeBalancedList
        ((canonicalBoundedCircuitDescription (sizeBound (pcp.nativeWidth n))
          canonical.circuit).map Bool.toNat))
      hpool
  have hsecond :=
    hdecoder inputLength (sizeBound (pcp.nativeWidth n)) (pcp.nativeWidth n)
      canonical.circuit canonical.sizeBounded
  exact run_occurrenceStage hframe hsecond

end NearCubicWires.CaseTwoCanonicalCircuitEncoder
