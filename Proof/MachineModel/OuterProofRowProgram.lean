import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.Foundations.CanonicalEncodedListLengthProgram
import Proof.MachineModel.CanonicalProjectedRandomBitProgram
import Proof.MachineModel.CanonicalThreeCNFLiteralProgram
import Proof.MachineModel.OuterProofRecoveryFormulaSeedProgram

/-!
# The decision-row emitter of the C.12 recovery formula

`OuterProofRecoveryFormulaSeedProgram` reduces the whole Case-1 recovery seed
to one named row stage: from `pair code (pair width (encodeBitInput input))` it
must emit

```text
rawClauseStream (outerProofRowFormula pcp input (bitInputOfCode width code))
```

which is definitionally `encodeTaggedList (outerProofRowStream pcp input code)`.

This module owns that stage.

Section 1 is the semantic seam: one raw arithmetic normal form of the row
stream whose only imported data are

* the published query runner's projection code at every `(query, bit)`
  coordinate of the *native* width, folded into `binaryAddress`;
* the published decision runner's single output at the native prefix of the
  requested randomness, read through the canonical `ThreeCNF` codec.

Nothing else about the padded PCP enters: the padded width contributes only
the constant-zero high address bits, which the fold below never visits.

Sections 2 and 3 build the executable address side of that normal form.  One
published balanced range, one published balanced call and the published
balanced natural-number sum fold the coordinates of a single query index into
its proof-table address; a second published range and call apply that stage at
every query index, so one fixed oracle-free program emits the whole address
table of a row as a balanced list.  Both stages are stated modulo the single
named coordinate callee, whose contract is the hypothesis `hweight` of
`run_rowAddressProgram`: from `pair bit (rowWeightContext …)` it must emit
`rowAddressWeight native randomnessCode bit (projection bit)` — one
`pcp.query` call framed by `preserveRightProgram`, the published
`projectedRandomBitProgram`, and the published dyadic exponential.
-/
namespace NearCubicWires.OuterProofRowProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF
open NearCubicWires.VerifiedLinker

/-! ## 1. The raw-code specification of one decision row -/

/-- Native random string selected by a padded randomness code.  The padded
high bits are discarded exactly as `prefixBits` discards them. -/
def rowRandomnessCode (native code : ℕ) : ℕ :=
  code % 2 ^ native

/-- Raw projection code returned by the published query runner at one native
address coordinate.  Out-of-range coordinates are never requested by the fold
below; they are normalized to zero so the specification is total. -/
def rowProjectionCode
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query bit : ℕ) : ℕ :=
  if hquery : query < pcp.queryCount n then
    if hbit : bit < pcp.nativeWidth n then
      pcp.query.execute (pcp.queryRequest input ⟨query, hquery⟩ ⟨bit, hbit⟩)
    else 0
  else 0

/-- Weight contributed by one projected address coordinate. -/
def rowAddressWeight (native randomnessCode bit projectionCode : ℕ) : ℕ :=
  projectedRandomBitOutput native projectionCode randomnessCode * 2 ^ bit

/-- Raw proof-table address of one query index: the published projection codes
of its native coordinates, folded into `binaryAddress`. -/
def rowAddress (native randomnessCode : ℕ) (projection : ℕ → ℕ) : ℕ :=
  ((List.range native).map fun bit =>
    rowAddressWeight native randomnessCode bit (projection bit)).sum

/-- The complete address table of one decision row, as a function of the query
index. -/
def rowAddressOf
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code query : ℕ) : ℕ :=
  rowAddress (pcp.nativeWidth n)
    (rowRandomnessCode (pcp.nativeWidth n) code)
    (rowProjectionCode pcp input query)

/-- Raw decision code returned by the published decision runner at the native
prefix of the requested randomness. -/
def rowDecisionCode
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) : ℕ :=
  pcp.decisionRunner.execute
    (pcp.decisionRequest input
      (fun bit => (rowRandomnessCode (pcp.nativeWidth n) code).testBit bit.val))

/-- One emitted literal: the canonical literal code of the decision runner is
re-signed into the `EncodedLiteral` convention and its query index is replaced
by the proof-table address. -/
def rowLiteralCode (address : ℕ → ℕ) (literalCode : ℕ) : ℕ :=
  Nat.pair (1 - (Nat.unpair literalCode).1)
    (address (Nat.unpair literalCode).2)

/-- One emitted raw clause. -/
def rowClauseCode (count decisionCode : ℕ) (address : ℕ → ℕ)
    (clauseIndex : ℕ) : ℕ :=
  Nat.pair
    (rowLiteralCode address
      (threeCNFLiteralOutput count decisionCode clauseIndex 0))
    (Nat.pair
      (rowLiteralCode address
        (threeCNFLiteralOutput count decisionCode clauseIndex 1))
      (rowLiteralCode address
        (threeCNFLiteralOutput count decisionCode clauseIndex 2)))

/-- The whole emitted row, as a raw clause list. -/
def rowRawStream (count decisionCode : ℕ) (address : ℕ → ℕ) : List ℕ :=
  (List.range (encodedListLength decisionCode)).map
    (rowClauseCode count decisionCode address)

/-! ### The address fold is the padded query address -/

private theorem list_range_sum (count : ℕ) (term : ℕ → ℕ) :
    ((List.range count).map term).sum = ∑ index ∈ Finset.range count, term index := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.range_succ, List.map_append, List.sum_append,
        inductionHypothesis, Finset.sum_range_succ]
      simp

private theorem testBit_rowRandomnessCode {native code bit : ℕ}
    (hbit : bit < native) :
    (rowRandomnessCode native code).testBit bit = code.testBit bit := by
  unfold rowRandomnessCode
  rw [Nat.testBit_mod_two_pow]
  simp [hbit]

private theorem prefixBits_bitInputOfCode
    {native padded : ℕ} (hwidth : native ≤ padded) (code : ℕ) :
    prefixBits hwidth (bitInputOfCode padded code) =
      bitInputOfCode native code := by
  funext index
  rfl

private theorem bitInputOfCode_rowRandomnessCode (native code : ℕ) :
    (fun bit : Fin native =>
      (rowRandomnessCode native code).testBit bit.val) =
      bitInputOfCode native code := by
  funext bit
  exact testBit_rowRandomnessCode bit.isLt

/-- The published projection codes of one query index fold to exactly the
native query address. -/
theorem rowAddress_eq_nativeQueryAddress
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ)
    (query : Fin (pcp.queryCount n)) :
    rowAddressOf pcp input code query.val =
      (pcp.toSemantic.queryAddress input
        (bitInputOfCode (pcp.nativeWidth n) code) query).val := by
  have hterm :
      ∀ bit : Fin (pcp.nativeWidth n),
        rowAddressWeight (pcp.nativeWidth n)
            (rowRandomnessCode (pcp.nativeWidth n) code) bit.val
            (rowProjectionCode pcp input query.val bit.val) =
          if (pcp.queryAddressBits input query bit).eval
              (bitInputOfCode (pcp.nativeWidth n) code)
          then 2 ^ bit.val else 0 := by
    intro bit
    unfold rowAddressWeight projectedRandomBitOutput rowProjectionCode
    rw [dif_pos query.isLt, dif_pos bit.isLt, bitInputOfCode_rowRandomnessCode]
    have hbits :
        decodeProjectedRandomBit (pcp.nativeWidth n)
            (pcp.query.execute
              (pcp.queryRequest input ⟨query.val, query.isLt⟩
                ⟨bit.val, bit.isLt⟩)) =
          pcp.queryAddressBits input query bit := by
      rfl
    rw [hbits]
    generalize (pcp.queryAddressBits input query bit).eval
      (bitInputOfCode (pcp.nativeWidth n) code) = value
    cases value <;> simp
  have hsum :
      ((List.range (pcp.nativeWidth n)).map fun bit =>
          rowAddressWeight (pcp.nativeWidth n)
            (rowRandomnessCode (pcp.nativeWidth n) code) bit
            (rowProjectionCode pcp input query.val bit)).sum =
        ∑ bit : Fin (pcp.nativeWidth n),
          if (pcp.queryAddressBits input query bit).eval
              (bitInputOfCode (pcp.nativeWidth n) code)
          then 2 ^ bit.val else 0 := by
    rw [list_range_sum, ← Fin.sum_univ_eq_sum_range
      (fun bit => rowAddressWeight (pcp.nativeWidth n)
        (rowRandomnessCode (pcp.nativeWidth n) code) bit
        (rowProjectionCode pcp input query.val bit)) (pcp.nativeWidth n)]
    exact Finset.sum_congr rfl fun bit _ => hterm bit
  unfold rowAddressOf rowAddress
  rw [hsum]
  have haddress :
      (pcp.toSemantic.queryAddress input
          (bitInputOfCode (pcp.nativeWidth n) code) query).val =
        encodeBitInput (fun bit : Fin (pcp.nativeWidth n) =>
          (pcp.queryAddressBits input query bit).eval
            (bitInputOfCode (pcp.nativeWidth n) code)) %
          2 ^ pcp.nativeWidth n :=
    rfl
  rw [haddress, Nat.mod_eq_of_lt (encodeBitInput_lt_pow _)]
  rfl

/-- The same fold is the padded query address: the padded coordinates above the
native width are constant zero and contribute nothing. -/
theorem rowAddress_eq_paddedQueryAddress
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) {n : ℕ}
    (input : BitInput n) (code : ℕ)
    (query : Fin (pcp.queryCount n)) :
    rowAddressOf pcp input code query.val =
      ((padProjectionPCP pcp.toSemantic paddedWidth hwidth).queryAddress input
        (bitInputOfCode (paddedWidth n) code) query).val := by
  rw [rowAddress_eq_nativeQueryAddress pcp input code query]
  exact (padProjectionPCP_queryAddress_val pcp.toSemantic paddedWidth hwidth
    input (bitInputOfCode (paddedWidth n) code) query).symm

/-! ### The decision code is the padded decision row -/

theorem decodeThreeCNF_rowDecisionCode
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    decodeThreeCNF (pcp.queryCount n) (rowDecisionCode pcp input code) =
      (padProjectionPCP pcp.toSemantic paddedWidth hwidth).decision input
        (bitInputOfCode (paddedWidth n) code) := by
  unfold rowDecisionCode
  rw [bitInputOfCode_rowRandomnessCode]
  rfl

/-! ### The raw stream is the padded decision row -/

/-- One emitted literal, at the semantic level: the decision runner's literal
keeps its sign and exchanges its query index for the proof-table address. -/
def rowLiteralOf {arity : ℕ} (address : ℕ → ℕ) :
    Literal arity → EncodedLiteral
  | .positive index => positive (address index.val)
  | .negative index => negative (address index.val)

private theorem encode_positive (index : ℕ) :
    Encodable.encode (positive index) = Nat.pair 1 index := by
  rfl

private theorem encode_negative (index : ℕ) :
    Encodable.encode (negative index) = Nat.pair 0 index := by
  rfl

private theorem rowLiteralCode_encodeLiteral {arity : ℕ}
    (address : ℕ → ℕ) (literal : Literal arity) :
    rowLiteralCode address (encodeLiteral literal) =
      Encodable.encode (rowLiteralOf address literal) := by
  cases literal with
  | positive index =>
      rw [rowLiteralOf, encode_positive]
      simp [rowLiteralCode, encodeLiteral]
  | negative index =>
      rw [rowLiteralOf, encode_negative]
      simp [rowLiteralCode, encodeLiteral]

private theorem outerProofLiteral_eq_rowLiteralOf
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) {n : ℕ}
    (input : BitInput n) (code : ℕ)
    (literal : Literal (pcp.queryCount n)) :
    outerProofLiteral (padProjectionPCP pcp.toSemantic paddedWidth hwidth)
        input (bitInputOfCode (paddedWidth n) code) literal =
      rowLiteralOf (rowAddressOf pcp input code) literal := by
  cases literal with
  | positive index =>
      rw [rowLiteralOf,
        rowAddress_eq_paddedQueryAddress pcp paddedWidth hwidth input code
          index]
      rfl
  | negative index =>
      rw [rowLiteralOf,
        rowAddress_eq_paddedQueryAddress pcp paddedWidth hwidth input code
          index]
      rfl

private theorem map_eq_range_map_getD {α β : Type}
    (values : List α) (fallback : α) (function : α → β) :
    values.map function =
      (List.range values.length).map fun index =>
        function (values.getD index fallback) := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hindex : index < values.length := by
      simpa using hleft
    simp [List.getElem?_eq_getElem hindex]

private theorem rawEncodedClause_outerProofClause
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (semantic : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (semantic.nativeWidth n))
    (clause : Fin 3 → Literal (semantic.queryCount n)) :
    rawEncodedClause (outerProofClause semantic input randomness clause) =
      Nat.pair
        (Encodable.encode (outerProofLiteral semantic input randomness
          (clause 0)))
        (Nat.pair
          (Encodable.encode (outerProofLiteral semantic input randomness
            (clause 1)))
          (Encodable.encode (outerProofLiteral semantic input randomness
            (clause 2)))) := by
  rfl

private theorem rowClauseCode_eq_rawEncodedClause
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) {n : ℕ}
    (input : BitInput n) (code : ℕ)
    (hcount : 0 < pcp.queryCount n) (index : ℕ)
    (clause : Fin 3 → Literal (pcp.queryCount n))
    (hclause :
      (decodeThreeCNF (pcp.queryCount n)
        (rowDecisionCode pcp input code)).clauses.getD index
          (fun _ => decodeLiteral hcount 0) = clause) :
    rowClauseCode (pcp.queryCount n) (rowDecisionCode pcp input code)
        (rowAddressOf pcp input code) index =
      rawEncodedClause
        (outerProofClause (padProjectionPCP pcp.toSemantic paddedWidth hwidth)
          input (bitInputOfCode (paddedWidth n) code) clause) := by
  have hliteral :
      ∀ position : Fin 3,
        rowLiteralCode (rowAddressOf pcp input code)
            (threeCNFLiteralOutput (pcp.queryCount n)
              (rowDecisionCode pcp input code) index position.val) =
          Encodable.encode
            (outerProofLiteral
              (padProjectionPCP pcp.toSemantic paddedWidth hwidth) input
              (bitInputOfCode (paddedWidth n) code) (clause position)) := by
    intro position
    rw [threeCNFLiteralOutput_eq_decodeThreeCNF (pcp.queryCount n)
      (rowDecisionCode pcp input code) index position hcount, hclause,
      rowLiteralCode_encodeLiteral,
      outerProofLiteral_eq_rowLiteralOf pcp paddedWidth hwidth input code]
  rw [rowClauseCode, hliteral ⟨0, by omega⟩, hliteral ⟨1, by omega⟩,
    hliteral ⟨2, by omega⟩,
    rawEncodedClause_outerProofClause
      (padProjectionPCP pcp.toSemantic paddedWidth hwidth) input
      (bitInputOfCode (paddedWidth n) code) clause]
  rfl

/-- Structural half of the seam: the raw stream is a clause-indexed map over
the decoded decision list.  The clause emitter stays abstract so that no
interpreter output is unfolded here. -/
private theorem rowRawStream_eq_clauseMap
    (count decisionCode : ℕ) (address : ℕ → ℕ) (hcount : 0 < count)
    (clauseEmitter : (Fin 3 → Literal count) → ℕ)
    (hemitter :
      ∀ index : ℕ,
        rowClauseCode count decisionCode address index =
          clauseEmitter
            ((decodeThreeCNF count decisionCode).clauses.getD index
              (fun _ => decodeLiteral hcount 0))) :
    rowRawStream count decisionCode address =
      (decodeThreeCNF count decisionCode).clauses.map clauseEmitter := by
  unfold rowRawStream
  rw [map_eq_range_map_getD (decodeThreeCNF count decisionCode).clauses
      (fun _ => decodeLiteral hcount 0) clauseEmitter,
    ← encodedListLength_eq_decodeThreeCNF_clauses count decisionCode hcount]
  exact List.map_congr_left fun index _ => hemitter index

/-- Semantic seam of the row emitter: the raw clause list built from the two
published runner outputs is literally the padded decision row. -/
theorem rowRawStream_eq_outerProofRowStream
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) {n : ℕ}
    (input : BitInput n) (code : ℕ)
    (hcount : 0 < pcp.queryCount n) :
    rowRawStream (pcp.queryCount n) (rowDecisionCode pcp input code)
        (rowAddressOf pcp input code) =
      outerProofRowStream (padProjectionPCP pcp.toSemantic paddedWidth hwidth)
        input code := by
  rw [rowRawStream_eq_clauseMap (pcp.queryCount n)
      (rowDecisionCode pcp input code) (rowAddressOf pcp input code) hcount
      (fun clause =>
        rawEncodedClause
          (outerProofClause (padProjectionPCP pcp.toSemantic paddedWidth hwidth)
            input (bitInputOfCode (paddedWidth n) code) clause))
      (fun index =>
        rowClauseCode_eq_rawEncodedClause pcp paddedWidth hwidth input code
          hcount index
          ((decodeThreeCNF (pcp.queryCount n)
            (rowDecisionCode pcp input code)).clauses.getD index
              (fun _ => decodeLiteral hcount 0)) rfl),
    decodeThreeCNF_rowDecisionCode pcp paddedWidth hwidth input code]
  unfold outerProofRowStream outerProofRowFormula
  symm
  apply List.map_map

/-! ### The scheduled instance of the seam -/

/-- The scheduled Case-1 row: the raw clause list built from the two published
runner outputs of the hierarchy PCP is literally the padded decision row that
`OuterProofRecoveryFormulaSeedProgram` consumes. -/
theorem rowRawStream_eq_scheduledOuterProofRowStream
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (code : ℕ)
    (hcount : 0 < outer.pcp.queryCount (sourceLength sourceIndex)) :
    rowRawStream (outer.pcp.queryCount (sourceLength sourceIndex))
        (rowDecisionCode outer.pcp input code)
        (rowAddressOf outer.pcp input code) =
      outerProofRowStream (paddedOuterPCP outer) input code :=
  rowRawStream_eq_outerProofRowStream outer.pcp (widthEnvelope outer)
    (nativeWidth_le_widthEnvelope outer) input code hcount

/-! ## 2. The address stage of one query index

One published balanced range, one published balanced call, and the published
balanced natural-number sum turn the coordinate callee of a single query index
into its complete proof-table address. -/

/-- Context handed to every address coordinate of one query index. -/
def rowWeightContext
    (inputLength native randomnessCode query inputCode : ℕ) : ℕ :=
  Nat.pair native
    (Nat.pair randomnessCode (Nat.pair query (Nat.pair inputLength inputCode)))

/-- Coordinate atoms of the address fold at one query index. -/
def rowAddressAtoms
    (inputLength native randomnessCode query inputCode : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength
    (rowWeightContext inputLength native randomnessCode query inputCode) 0
    native

/-- Range coordinate carried by one generated atom. -/
def rowAtomIndex (atom : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair atom).2).1

/-- Exact weight emitted by the coordinate callee at one atom. -/
def rowAtomWeight (native randomnessCode : ℕ) (projection : ℕ → ℕ)
    (atom : ℕ) : ℕ :=
  rowAddressWeight native randomnessCode (rowAtomIndex atom)
    (projection (rowAtomIndex atom))

def rowAtomCalleeFuel (weightFuel : ℕ → ℕ) (atom : ℕ) : ℕ :=
  weightFuel (rowAtomIndex atom)

def rowAtomCalleeBits (weightBits : ℕ → ℕ) (atom : ℕ) : ℕ :=
  weightBits (rowAtomIndex atom)

@[simp] theorem rowAtomIndex_balancedRangeRequestAtom
    (inputLength bit context : ℕ) :
    rowAtomIndex (balancedRangeRequestAtom inputLength bit context) = bit := by
  simp [rowAtomIndex, balancedRangeRequestAtom]

/-- The coordinate weights of the published range are exactly the summands of
`rowAddress`. -/
theorem rowAddressAtoms_weights
    (inputLength native randomnessCode query inputCode : ℕ)
    (projection : ℕ → ℕ) :
    ((rowAddressAtoms inputLength native randomnessCode query inputCode).map
        (rowAtomWeight native randomnessCode projection)).sum =
      rowAddress native randomnessCode projection := by
  unfold rowAddressAtoms rowAddress
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun offset _ => ?_)
  simp [rowAtomWeight]

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmember : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmember
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmember
      simp only [List.foldr_cons]
      rcases hmember with rfl | hmember
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmember).trans (Nat.le_max_right _ _)

private def rowTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] private theorem rowTakeLeftProgram_oracleFree :
    OracleFree rowTakeLeftProgram := by
  rfl

private theorem run_rowTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleftBits : natBitLength left ≤ maximumBits) :
    runNPOracleProgram rowTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleftBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleftBits

/-- One fixed program computing the whole proof-table address of a single
query index from the named coordinate callee. -/
def rowAddressProgram (weight : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms rowTakeLeftProgram
      (linkPrograms (balancedCallProgram weight) balancedNatSumProgram))

theorem rowAddressProgram_oracleFree
    {weight : NPOracleProgram} (hweight : OracleFree weight) :
    OracleFree (rowAddressProgram weight) := by
  apply oracleFree_linkPrograms
  · exact generatedBalancedRangeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact rowTakeLeftProgram_oracleFree
    · apply oracleFree_linkPrograms
      · exact balancedCallProgram_oracleFree hweight
      · exact balancedNatSumProgram_oracleFree

def rowAddressFuel (weight : NPOracleProgram) (weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode query inputCode : ℕ)
    (projection : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms rowTakeLeftProgram
      (linkPrograms (balancedCallProgram weight) balancedNatSumProgram))
    (generatedBalancedRangeFuel inputLength native
      (rowWeightContext inputLength native randomnessCode query inputCode))
    (linkFuel
      (linkPrograms (balancedCallProgram weight) balancedNatSumProgram)
      2
      (linkFuel balancedNatSumProgram
        (balancedCallFuel weight (rowAtomCalleeFuel weightFuel)
          (rowAddressAtoms inputLength native randomnessCode query inputCode))
        (balancedNatSumFuel
          ((rowAddressAtoms inputLength native randomnessCode query
            inputCode).map
              (rowAtomWeight native randomnessCode projection)))))

def rowAddressBits (weightBits : ℕ → ℕ)
    (inputLength native randomnessCode query inputCode : ℕ)
    (projection : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (generatedBalancedRangeRequiredBits inputLength native
          (rowWeightContext inputLength native randomnessCode query
            inputCode)) <|
        max
          (natBitLength
            (encodeBalancedList
              (rowAddressAtoms inputLength native randomnessCode query
                inputCode))) <|
          max
            (balancedCallRequiredBits
              (rowAtomWeight native randomnessCode projection)
              (rowAddressAtoms inputLength native randomnessCode query
                inputCode)) <|
            max
              (((rowAddressAtoms inputLength native randomnessCode query
                inputCode).map (rowAtomCalleeBits weightBits)).foldr max 0)
              (balancedNatSumBits inputLength
                ((rowAddressAtoms inputLength native randomnessCode query
                  inputCode).map
                    (rowAtomWeight native randomnessCode projection)))

/-- Exact address construction.  Modulo the single named coordinate callee, one
fixed oracle-free program emits the complete proof-table address of one query
index from the schedule parameters. -/
theorem run_rowAddressProgram
    (weight : NPOracleProgram) (weightBits weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode query inputCode : ℕ)
    (projection : ℕ → ℕ)
    (hweight : ∀ bit, bit < native →
      runNPOracleProgram weight (weightBits bit) (weightFuel bit)
          (initialNPOracleState inputLength
            (Nat.pair bit
              (rowWeightContext inputLength native randomnessCode query
                inputCode))) =
        some (rowAddressWeight native randomnessCode bit (projection bit))) :
    runNPOracleProgram (rowAddressProgram weight)
        (rowAddressBits weightBits inputLength native randomnessCode query
          inputCode projection)
        (rowAddressFuel weight weightFuel inputLength native randomnessCode
          query inputCode projection)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput native
            (rowWeightContext inputLength native randomnessCode query
              inputCode))) =
      some (rowAddress native randomnessCode projection) := by
  set context :=
    rowWeightContext inputLength native randomnessCode query inputCode
    with hcontext
  set atoms :=
    rowAddressAtoms inputLength native randomnessCode query inputCode
    with hatoms
  set output := rowAtomWeight native randomnessCode projection with houtput
  set maximumBits :=
    rowAddressBits weightBits inputLength native randomnessCode query inputCode
      projection with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength native context ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength (encodeBalancedList atoms) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits output atoms ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      (atoms.map (rowAtomCalleeBits weightBits)).foldr max 0 ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsumBits :
      balancedNatSumBits inputLength (atoms.map output) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength native context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput native context)) =
        some (Nat.pair (encodeBalancedList atoms) context) :=
    run_bits_mono
      (run_generatedBalancedRangeProgram inputLength native context)
      hrangeBits
  have htake :
      runNPOracleProgram rowTakeLeftProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList atoms) context)) =
        some (encodeBalancedList atoms) :=
    run_rowTakeLeftProgram inputLength (encodeBalancedList atoms) context
      hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram weight) maximumBits
          (balancedCallFuel weight (rowAtomCalleeFuel weightFuel) atoms)
          (initialNPOracleState inputLength (encodeBalancedList atoms)) =
        some (encodeBalancedList (atoms.map output)) := by
    refine run_balancedCallProgram_from inputLength atoms
      (rowAtomCalleeFuel weightFuel) output hcallBits ?_
    intro atom hatom
    have hcalleeBits : rowAtomCalleeBits weightBits atom ≤ maximumBits :=
      (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hatomBits
    rw [hatoms, rowAddressAtoms, balancedRangeRequestAtoms_eq_map_range,
      List.mem_map] at hatom
    obtain ⟨offset, hoffset, hatomEq⟩ := hatom
    have hbit : offset < native := List.mem_range.mp hoffset
    rw [← hatomEq] at hcalleeBits ⊢
    have hleft :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).1 =
          inputLength := by
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).2 =
          Nat.pair (0 + offset) context := by
      simp [balancedRangeRequestAtom]
    rw [hleft, hright]
    simp only [houtput, rowAtomWeight, rowAtomCalleeFuel, rowAtomCalleeBits,
      rowAtomIndex_balancedRangeRequestAtom] at hcalleeBits ⊢
    exact run_bits_mono (hweight (0 + offset) (by omega)) hcalleeBits
  have hsum :
      runNPOracleProgram balancedNatSumProgram maximumBits
          (balancedNatSumFuel (atoms.map output))
          (initialNPOracleState inputLength
            (encodeBalancedList (atoms.map output))) =
        some (atoms.map output).sum :=
    run_bits_mono
      (run_balancedNatSumProgram inputLength (atoms.map output)) hsumBits
  have hthird := run_linkPrograms hpositive hlengthBits hcall hsum
  have hsecond := run_linkPrograms hpositive hlengthBits htake hthird
  have hrun := run_linkPrograms hpositive hlengthBits hrange hsecond
  rw [← rowAddressAtoms_weights inputLength native randomnessCode query
    inputCode projection]
  exact hrun

/-! ## 3. The address table of one decision row

A second published range and call apply the address stage at every query index,
so one fixed program emits the whole address table of a row as a balanced list.
-/

/-- Public context of the whole address table of one decision row. -/
def rowTableContext (inputLength native randomnessCode inputCode : ℕ) : ℕ :=
  Nat.pair native (Nat.pair randomnessCode (Nat.pair inputLength inputCode))

/-- The exact address-stage request of one query index. -/
def rowQueryFrameOutput
    (inputLength native randomnessCode query inputCode : ℕ) : ℕ :=
  generatedBalancedRangeInput native
    (rowWeightContext inputLength native randomnessCode query inputCode)

/-- Fixed adapter from the generated query atom to the address-stage request. -/
private def rowQueryFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 7 8 7
  , .pair 6 8 9 8
  , .pair 4 9 10 9
  , .pair 4 10 0 10
  , .halt 0
  ]

@[simp] private theorem rowQueryFrameProgram_oracleFree :
    OracleFree rowQueryFrameProgram := by
  rfl

def rowQueryFrameBits
    (inputLength native randomnessCode query inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair query
        (rowTableContext inputLength native randomnessCode inputCode))
      (rowQueryFrameOutput inputLength native randomnessCode query inputCode))

private theorem run_rowQueryFrameProgram
    (inputLength native randomnessCode query inputCode : ℕ) :
    runNPOracleProgram rowQueryFrameProgram
        (rowQueryFrameBits inputLength native randomnessCode query inputCode)
        11
        (initialNPOracleState inputLength
          (Nat.pair query
            (rowTableContext inputLength native randomnessCode inputCode))) =
      some
        (rowQueryFrameOutput inputLength native randomnessCode query
          inputCode) := by
  have hinputBits :
      natBitLength
          (Nat.pair query
            (rowTableContext inputLength native randomnessCode inputCode)) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtputBits :
      natBitLength
          (rowQueryFrameOutput inputLength native randomnessCode query
            inputCode) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hqueryBits :
      natBitLength query ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair query
        (rowTableContext inputLength native randomnessCode
          inputCode))).trans hinputBits
  have hcontextBits :
      natBitLength (rowTableContext inputLength native randomnessCode
          inputCode) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair query
        (rowTableContext inputLength native randomnessCode
          inputCode))).trans hinputBits
  have hnativeBits :
      natBitLength native ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair native
        (Nat.pair randomnessCode
          (Nat.pair inputLength inputCode)))).trans hcontextBits
  have hfirstTailBits :
      natBitLength
          (Nat.pair randomnessCode (Nat.pair inputLength inputCode)) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (Nat.pair randomnessCode
          (Nat.pair inputLength inputCode)))).trans hcontextBits
  have hrandomnessBits :
      natBitLength randomnessCode ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.left_le_pair randomnessCode
        (Nat.pair inputLength inputCode))).trans hfirstTailBits
  have hsecondTailBits :
      natBitLength (Nat.pair inputLength inputCode) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair randomnessCode
        (Nat.pair inputLength inputCode))).trans hfirstTailBits
  have hweightContextBits :
      natBitLength
          (rowWeightContext inputLength native randomnessCode query
            inputCode) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (rowWeightContext inputLength native randomnessCode query
          inputCode))).trans houtputBits
  have hinnerBits :
      natBitLength
          (Nat.pair randomnessCode
            (Nat.pair query (Nat.pair inputLength inputCode))) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair native
        (Nat.pair randomnessCode
          (Nat.pair query
            (Nat.pair inputLength inputCode))))).trans hweightContextBits
  have hcoreBits :
      natBitLength (Nat.pair query (Nat.pair inputLength inputCode)) ≤
        rowQueryFrameBits inputLength native randomnessCode query inputCode :=
    (natBitLength_mono
      (Nat.right_le_pair randomnessCode
        (Nat.pair query (Nat.pair inputLength inputCode)))).trans hinnerBits
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := query)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hqueryBits]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := rowTableContext inputLength native randomnessCode inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := native)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowTableContext])
    hnativeBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair randomnessCode (Nat.pair inputLength inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowTableContext])
    hfirstTailBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrandomnessBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair inputLength inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondTailBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair query (Nat.pair inputLength inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcoreBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair randomnessCode
        (Nat.pair query (Nat.pair inputLength inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := rowWeightContext inputLength native randomnessCode query
      inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rowWeightContext])
    hweightContextBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      rowQueryFrameOutput inputLength native randomnessCode query inputCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rowQueryFrameOutput,
        generatedBalancedRangeInput])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The complete address table of one decision row. -/
def rowAddressTable (count native randomnessCode : ℕ)
    (projection : ℕ → ℕ → ℕ) : List ℕ :=
  (List.range count).map fun query =>
    rowAddress native randomnessCode (projection query)

/-- Query atoms of the address table. -/
def rowTableAtoms
    (inputLength native randomnessCode count inputCode : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength
    (rowTableContext inputLength native randomnessCode inputCode) 0 count

def rowTableOutput (native randomnessCode : ℕ) (projection : ℕ → ℕ → ℕ)
    (atom : ℕ) : ℕ :=
  rowAddress native randomnessCode (projection (rowAtomIndex atom))

theorem rowTableAtoms_outputs
    (inputLength native randomnessCode count inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) :
    (rowTableAtoms inputLength native randomnessCode count inputCode).map
        (rowTableOutput native randomnessCode projection) =
      rowAddressTable count native randomnessCode projection := by
  unfold rowTableAtoms rowAddressTable
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
  refine List.map_congr_left fun offset _ => ?_
  simp [rowTableOutput]

/-- The address-table callee: the fixed adapter followed by the address stage. -/
def rowTableCalleeProgram (weight : NPOracleProgram) : NPOracleProgram :=
  linkPrograms rowQueryFrameProgram (rowAddressProgram weight)

theorem rowTableCalleeProgram_oracleFree
    {weight : NPOracleProgram} (hweight : OracleFree weight) :
    OracleFree (rowTableCalleeProgram weight) := by
  apply oracleFree_linkPrograms
  · exact rowQueryFrameProgram_oracleFree
  · exact rowAddressProgram_oracleFree hweight

def rowTableCalleeFuel (weight : NPOracleProgram) (weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) (query : ℕ) : ℕ :=
  linkFuel (rowAddressProgram weight) 11
    (rowAddressFuel weight weightFuel inputLength native randomnessCode query
      inputCode (projection query))

def rowTableCalleeBits (weightBits : ℕ → ℕ)
    (inputLength native randomnessCode inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) (query : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (rowQueryFrameBits inputLength native randomnessCode query inputCode)
        (rowAddressBits weightBits inputLength native randomnessCode query
          inputCode (projection query))

def rowTableAtomFuel (weight : NPOracleProgram) (weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) (atom : ℕ) : ℕ :=
  rowTableCalleeFuel weight weightFuel inputLength native randomnessCode
    inputCode projection (rowAtomIndex atom)

def rowTableAtomBits (weightBits : ℕ → ℕ)
    (inputLength native randomnessCode inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) (atom : ℕ) : ℕ :=
  rowTableCalleeBits weightBits inputLength native randomnessCode inputCode
    projection (rowAtomIndex atom)

private theorem run_rowTableCalleeProgram
    (weight : NPOracleProgram) (weightBits weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode inputCode query : ℕ)
    (projection : ℕ → ℕ → ℕ)
    (hweight : ∀ bit, bit < native →
      runNPOracleProgram weight (weightBits bit) (weightFuel bit)
          (initialNPOracleState inputLength
            (Nat.pair bit
              (rowWeightContext inputLength native randomnessCode query
                inputCode))) =
        some
          (rowAddressWeight native randomnessCode bit
            (projection query bit))) :
    runNPOracleProgram (rowTableCalleeProgram weight)
        (rowTableCalleeBits weightBits inputLength native randomnessCode
          inputCode projection query)
        (rowTableCalleeFuel weight weightFuel inputLength native randomnessCode
          inputCode projection query)
        (initialNPOracleState inputLength
          (Nat.pair query
            (rowTableContext inputLength native randomnessCode inputCode))) =
      some (rowAddress native randomnessCode (projection query)) := by
  have hpositive :
      1 ≤ rowTableCalleeBits weightBits inputLength native randomnessCode
        inputCode projection query :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength inputLength ≤
        rowTableCalleeBits weightBits inputLength native randomnessCode
          inputCode projection query :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      rowQueryFrameBits inputLength native randomnessCode query inputCode ≤
        rowTableCalleeBits weightBits inputLength native randomnessCode
          inputCode projection query :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have haddressBits :
      rowAddressBits weightBits inputLength native randomnessCode query
          inputCode (projection query) ≤
        rowTableCalleeBits weightBits inputLength native randomnessCode
          inputCode projection query :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframe :=
    run_bits_mono
      (run_rowQueryFrameProgram inputLength native randomnessCode query
        inputCode)
      hframeBits
  have haddress :=
    run_bits_mono
      (run_rowAddressProgram weight weightBits weightFuel inputLength native
        randomnessCode query inputCode (projection query) hweight)
      haddressBits
  exact run_linkPrograms hpositive hlengthBits hframe haddress

/-- One fixed program emitting the whole proof-table address list of a decision
row, modulo the single named coordinate callee. -/
def rowAddressTableProgram (weight : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms rowTakeLeftProgram
      (balancedCallProgram (rowTableCalleeProgram weight)))

theorem rowAddressTableProgram_oracleFree
    {weight : NPOracleProgram} (hweight : OracleFree weight) :
    OracleFree (rowAddressTableProgram weight) := by
  apply oracleFree_linkPrograms
  · exact generatedBalancedRangeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact rowTakeLeftProgram_oracleFree
    · exact balancedCallProgram_oracleFree
        (rowTableCalleeProgram_oracleFree hweight)

def rowAddressTableFuel (weight : NPOracleProgram) (weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode count inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms rowTakeLeftProgram
      (balancedCallProgram (rowTableCalleeProgram weight)))
    (generatedBalancedRangeFuel inputLength count
      (rowTableContext inputLength native randomnessCode inputCode))
    (linkFuel (balancedCallProgram (rowTableCalleeProgram weight)) 2
      (balancedCallFuel (rowTableCalleeProgram weight)
        (rowTableAtomFuel weight weightFuel inputLength native randomnessCode
          inputCode projection)
        (rowTableAtoms inputLength native randomnessCode count inputCode)))

def rowAddressTableBits (weightBits : ℕ → ℕ)
    (inputLength native randomnessCode count inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (generatedBalancedRangeRequiredBits inputLength count
          (rowTableContext inputLength native randomnessCode inputCode)) <|
        max
          (natBitLength
            (encodeBalancedList
              (rowTableAtoms inputLength native randomnessCode count
                inputCode))) <|
          max
            (balancedCallRequiredBits
              (rowTableOutput native randomnessCode projection)
              (rowTableAtoms inputLength native randomnessCode count
                inputCode))
            (((rowTableAtoms inputLength native randomnessCode count
              inputCode).map
                (rowTableAtomBits weightBits inputLength native randomnessCode
                  inputCode projection)).foldr max 0)

/-- Exact address-table construction.  Modulo the single named coordinate
callee, one fixed oracle-free program emits the balanced list of every
proof-table address of one decision row. -/
theorem run_rowAddressTableProgram
    (weight : NPOracleProgram) (weightBits weightFuel : ℕ → ℕ)
    (inputLength native randomnessCode count inputCode : ℕ)
    (projection : ℕ → ℕ → ℕ)
    (hweight : ∀ query, query < count → ∀ bit, bit < native →
      runNPOracleProgram weight (weightBits bit) (weightFuel bit)
          (initialNPOracleState inputLength
            (Nat.pair bit
              (rowWeightContext inputLength native randomnessCode query
                inputCode))) =
        some
          (rowAddressWeight native randomnessCode bit
            (projection query bit))) :
    runNPOracleProgram (rowAddressTableProgram weight)
        (rowAddressTableBits weightBits inputLength native randomnessCode count
          inputCode projection)
        (rowAddressTableFuel weight weightFuel inputLength native
          randomnessCode count inputCode projection)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count
            (rowTableContext inputLength native randomnessCode inputCode))) =
      some
        (encodeBalancedList
          (rowAddressTable count native randomnessCode projection)) := by
  set context := rowTableContext inputLength native randomnessCode inputCode
    with hcontext
  set atoms := rowTableAtoms inputLength native randomnessCode count inputCode
    with hatoms
  set output := rowTableOutput native randomnessCode projection with houtput
  set maximumBits :=
    rowAddressTableBits weightBits inputLength native randomnessCode count
      inputCode projection with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count context ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength (encodeBalancedList atoms) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits output atoms ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcalleeBits :
      (atoms.map
          (rowTableAtomBits weightBits inputLength native randomnessCode
            inputCode projection)).foldr max 0 ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength count context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some (Nat.pair (encodeBalancedList atoms) context) :=
    run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count context)
      hrangeBits
  have htake :
      runNPOracleProgram rowTakeLeftProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList atoms) context)) =
        some (encodeBalancedList atoms) :=
    run_rowTakeLeftProgram inputLength (encodeBalancedList atoms) context
      hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram (rowTableCalleeProgram weight))
          maximumBits
          (balancedCallFuel (rowTableCalleeProgram weight)
            (rowTableAtomFuel weight weightFuel inputLength native
              randomnessCode inputCode projection)
            atoms)
          (initialNPOracleState inputLength (encodeBalancedList atoms)) =
        some (encodeBalancedList (atoms.map output)) := by
    refine run_balancedCallProgram_from inputLength atoms
      (rowTableAtomFuel weight weightFuel inputLength native randomnessCode
        inputCode projection)
      output hcallBits ?_
    intro atom hatom
    have hatomBits :
        rowTableAtomBits weightBits inputLength native randomnessCode
            inputCode projection atom ≤ maximumBits :=
      (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hcalleeBits
    rw [hatoms, rowTableAtoms, balancedRangeRequestAtoms_eq_map_range,
      List.mem_map] at hatom
    obtain ⟨offset, hoffset, hatomEq⟩ := hatom
    have hquery : offset < count := List.mem_range.mp hoffset
    rw [← hatomEq] at hatomBits ⊢
    have hleft :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).1 =
          inputLength := by
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength (0 + offset) context)).2 =
          Nat.pair (0 + offset) context := by
      simp [balancedRangeRequestAtom]
    rw [hleft, hright]
    simp only [houtput, rowTableOutput, rowTableAtomBits, rowTableAtomFuel,
      rowAtomIndex_balancedRangeRequestAtom] at hatomBits ⊢
    exact run_bits_mono
      (run_rowTableCalleeProgram weight weightBits weightFuel inputLength
        native randomnessCode inputCode (0 + offset) projection
        (fun bit hbit => hweight (0 + offset) (by omega) bit hbit))
      hatomBits
  have hsecond := run_linkPrograms hpositive hlengthBits htake hcall
  have hrun := run_linkPrograms hpositive hlengthBits hrange hsecond
  rw [← rowTableAtoms_outputs inputLength native randomnessCode count inputCode
    projection]
  exact hrun

/-- The emitted address table is exactly the address function consumed by the
semantic seam of §1. -/
theorem rowAddressTable_eq_rowAddressOf
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (code : ℕ) :
    rowAddressTable (pcp.queryCount n) (pcp.nativeWidth n)
        (rowRandomnessCode (pcp.nativeWidth n) code)
        (rowProjectionCode pcp input) =
      (List.range (pcp.queryCount n)).map (rowAddressOf pcp input code) := by
  rfl

end NearCubicWires.OuterProofRowProgram
