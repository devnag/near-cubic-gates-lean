import Proof.Foundations.NestedBalancedCNFCodec
import Proof.Foundations.BalancedCNFSATEncodingConservativeExtension

/-!
# Semantic promotion for nested balanced CNF queries

This module keeps the historical and flat-balanced SAT interfaces frozen and
specifies the additive semantics of the false-tagged, two-level balanced
marker.  The outer payload is a balanced list of chunk codes; each chunk is a
balanced list of canonical clause codes.  Flattening occurs only after both
levels have decoded successfully.
-/

namespace NearCubicWires.NestedBalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.BalancedCNFSATEncodingConservativeExtension
open NearCubicWires.CanonicalBinary
open NearCubicWires.NestedBalancedCNFCodec

open private decodeClauseCodes from StatementSupport
open private legacyDecodeCNF from StatementSupport

/-! ## Public canonical-clause decoding boundary -/

/-- Decode each ordinary canonical clause code, failing closed to the empty
clause exactly as the frozen flat-balanced decoder does. -/
def decodeCanonicalClauseCodes (clauses : List ℕ) : EncodedCNF :=
  clauses.map fun clauseCode =>
    (Encodable.decode (α := List (Bool × ℕ)) clauseCode).getD []

private theorem decodeCanonicalClauseCodes_eq_decodeClauseCodes (clauses : List ℕ) :
    decodeCanonicalClauseCodes clauses = decodeClauseCodes clauses := by
  rfl

private theorem decodeCNF_eq_getD (code : ℕ) :
    decodeCNF code =
      (Encodable.decode (α := EncodedCNF) code).getD [] := by
  unfold decodeCNF
  cases Encodable.decode (α := EncodedCNF) code <;> rfl

/-- Exact base-marker decoding, exposed without the draft decoder's private
helper in the theorem statement. -/
@[simp] theorem decodeNestedBalancedCNF_encodeCanonicalChunks
    (chunks : List (List ℕ)) :
    decodeNestedBalancedCNF
        (encodeNestedBalancedCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks)) =
      some (decodeCanonicalClauseCodes chunks.flatten) := by
  rw [decodeCanonicalClauseCodes_eq_decodeClauseCodes]
  exact decodeNestedBalancedCNF_base chunks

/-- Exact prefix-marker decoding. -/
@[simp] theorem decodeNestedBalancedCNF_encodeCanonicalChunksPrefix
    (chunks : List (List ℕ)) (assignment count : ℕ) :
    decodeNestedBalancedCNF
        (encodeNestedBalancedPrefixCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks) assignment count) =
      some (balancedPrefixClauses count assignment ++
        decodeCanonicalClauseCodes chunks.flatten) := by
  rw [decodeCanonicalClauseCodes_eq_decodeClauseCodes]
  exact decodeNestedBalancedCNF_prefix chunks assignment count

/-! ## Marker separation and historical rejection -/

@[simp] theorem decodeCNF_encodeNestedBalancedCNFPayloadMarker
    (payload : ℕ) :
    decodeCNF (encodeNestedBalancedCNFPayloadMarker payload) =
      nestedBalancedCNFMarkerOfPayload payload := by
  simp [decodeCNF, encodeNestedBalancedCNFPayloadMarker,
    Encodable.encodek]

@[simp] theorem decodeCNF_encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) :
    decodeCNF
        (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count) =
      nestedBalancedPrefixCNFMarkerOfPayload payload assignment count := by
  simp [decodeCNF, encodeNestedBalancedPrefixCNFPayloadMarker,
    Encodable.encodek]

/-- The false payload tag separates a nested base marker from every flat
balanced marker, independently of payload contents. -/
theorem nestedBaseMarker_ne_flatBaseMarker
    (nestedPayload : ℕ) (formula : EncodedCNF) :
    nestedBalancedCNFMarkerOfPayload nestedPayload ≠
      balancedCNFMarker formula := by
  simp [nestedBalancedCNFMarkerOfPayload, balancedCNFMarker,
    balancedCNFPayload]

theorem nestedBaseMarker_ne_flatPrefixMarker
    (nestedPayload flatPayload assignment count : ℕ) :
    nestedBalancedCNFMarkerOfPayload nestedPayload ≠
      balancedPrefixCNFMarkerOfPayload flatPayload assignment count := by
  simp [nestedBalancedCNFMarkerOfPayload,
    balancedPrefixCNFMarkerOfPayload]

theorem nestedPrefixMarker_ne_flatBaseMarker
    (nestedPayload assignment count : ℕ) (formula : EncodedCNF) :
    nestedBalancedPrefixCNFMarkerOfPayload nestedPayload assignment count ≠
      balancedCNFMarker formula := by
  simp [nestedBalancedPrefixCNFMarkerOfPayload, balancedCNFMarker,
    balancedCNFPayload]

theorem nestedPrefixMarker_ne_flatPrefixMarker
    (nestedPayload flatPayload assignment count : ℕ) :
    nestedBalancedPrefixCNFMarkerOfPayload nestedPayload assignment count ≠
      balancedPrefixCNFMarkerOfPayload flatPayload assignment count := by
  simp [nestedBalancedPrefixCNFMarkerOfPayload,
    balancedPrefixCNFMarkerOfPayload]

/-- Any successfully decoded nested marker is rejected by the historical
well-sizedness gate because its first decoded clause is empty. -/
theorem wellSizedCNFEncoding_false_of_decodeNestedBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeNestedBalancedCNF code = some formula) :
    wellSizedCNFEncoding code (decodeCNF code) = false := by
  unfold decodeNestedBalancedCNF at hdecode
  generalize hlegacy :
      (Encodable.decode (α := EncodedCNF) code).getD [] = legacy at hdecode
  have hdecodeCNF : decodeCNF code = legacy :=
    (decodeCNF_eq_getD code).trans hlegacy
  dsimp only at hdecode
  split at hdecode <;> simp_all [wellSizedCNFEncoding]

/-- A query accepted by the historical gate cannot be a nested marker. -/
theorem decodeNestedBalancedCNF_eq_none_of_wellSized
    {code : ℕ}
    (hwell : wellSizedCNFEncoding code (decodeCNF code) = true) :
    decodeNestedBalancedCNF code = none := by
  cases hdecode : decodeNestedBalancedCNF code with
  | none => rfl
  | some formula =>
      have hfalse :=
        wellSizedCNFEncoding_false_of_decodeNestedBalancedCNF hdecode
      rw [hwell] at hfalse
      contradiction

/-- The established flat marker decoder and the nested marker decoder have
disjoint successful regions. -/
theorem decodeBalancedCNF_eq_none_of_decodeNestedBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeNestedBalancedCNF code = some formula) :
    decodeBalancedCNF code = none := by
  unfold decodeNestedBalancedCNF at hdecode
  unfold decodeBalancedCNF legacyDecodeCNF
  cases hlegacy : Encodable.decode (α := EncodedCNF) code with
  | none => simp [hlegacy] at hdecode
  | some legacy =>
      simp only [hlegacy, Option.getD_some] at hdecode ⊢
      split at hdecode <;> simp_all

@[simp] theorem decodeBalancedCNF_encodeNestedBalancedCNFPayloadMarker
    (payload : ℕ) :
    decodeBalancedCNF (encodeNestedBalancedCNFPayloadMarker payload) = none := by
  simp [decodeBalancedCNF, legacyDecodeCNF,
    encodeNestedBalancedCNFPayloadMarker,
    nestedBalancedCNFMarkerOfPayload]

@[simp] theorem decodeBalancedCNF_encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) :
    decodeBalancedCNF
        (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count) =
      none := by
  simp [decodeBalancedCNF, legacyDecodeCNF,
    encodeNestedBalancedPrefixCNFPayloadMarker,
    nestedBalancedPrefixCNFMarkerOfPayload]

@[simp] theorem wellSizedCNFEncoding_encodeNestedBalancedCNFPayloadMarker
    (payload : ℕ) :
    wellSizedCNFEncoding (encodeNestedBalancedCNFPayloadMarker payload)
        (decodeCNF (encodeNestedBalancedCNFPayloadMarker payload)) = false := by
  rw [decodeCNF_encodeNestedBalancedCNFPayloadMarker]
  simp [wellSizedCNFEncoding, nestedBalancedCNFMarkerOfPayload]

@[simp] theorem
    wellSizedCNFEncoding_encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) :
    wellSizedCNFEncoding
        (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count)
        (decodeCNF
          (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment
            count)) = false := by
  rw [decodeCNF_encodeNestedBalancedPrefixCNFPayloadMarker]
  simp [wellSizedCNFEncoding, nestedBalancedPrefixCNFMarkerOfPayload]

/-! ## Additive SAT semantics -/

/-- Promotion target for `encodedSat`: preserve both existing branches and
consult the nested decoder only after the flat decoder rejects. -/
def nestedEncodedSat (code : ℕ) : Bool :=
  let formula := decodeCNF code
  if wellSizedCNFEncoding code formula then
    legacyEncodedSat code
  else
    match decodeBalancedCNF code with
    | some balancedFormula =>
        legacyEncodedSat (Encodable.encode balancedFormula)
    | none =>
        match decodeNestedBalancedCNF code with
        | some nestedFormula =>
            legacyEncodedSat (Encodable.encode nestedFormula)
        | none => false

/-- Every decoded nested query receives exactly the historical SAT answer on
the ordinary canonical encoding of its decoded formula. -/
theorem nestedEncodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeNestedBalancedCNF code = some formula) :
    nestedEncodedSat code = legacyEncodedSat (Encodable.encode formula) := by
  have hfalse :=
    wellSizedCNFEncoding_false_of_decodeNestedBalancedCNF hdecode
  have hflat :=
    decodeBalancedCNF_eq_none_of_decodeNestedBalancedCNF hdecode
  simp [nestedEncodedSat, hfalse, hflat, hdecode]

/-- Base nested canonical chunks have exactly their historical SAT answer. -/
@[simp] theorem nestedEncodedSat_encodeNestedBalancedCanonicalChunks
    (chunks : List (List ℕ)) :
    nestedEncodedSat
        (encodeNestedBalancedCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks)) =
      legacyEncodedSat
        (Encodable.encode (decodeCanonicalClauseCodes chunks.flatten)) := by
  exact nestedEncodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF
    (decodeNestedBalancedCNF_encodeCanonicalChunks chunks)

/-- Prefix nested canonical chunks have exactly the historical SAT answer
after the committed prefix clauses are prepended. -/
@[simp] theorem nestedEncodedSat_encodeNestedBalancedCanonicalChunksPrefix
    (chunks : List (List ℕ)) (assignment count : ℕ) :
    nestedEncodedSat
        (encodeNestedBalancedPrefixCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks) assignment count) =
      legacyEncodedSat
        (Encodable.encode
          (balancedPrefixClauses count assignment ++
            decodeCanonicalClauseCodes chunks.flatten)) := by
  exact nestedEncodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF
    (decodeNestedBalancedCNF_encodeCanonicalChunksPrefix chunks assignment
      count)

/-- The promoted function is definitionally the frozen `encodedSat` on every
query outside the nested decoder's successful region. -/
theorem nestedEncodedSat_eq_encodedSat_of_decodeNestedBalancedCNF_eq_none
    {code : ℕ} (_hdecode : decodeNestedBalancedCNF code = none) :
    nestedEncodedSat code = encodedSat code := rfl

/-! ## Old-rejection of both nested markers by the *historical* semantics

Conservativity of the nested extension is the statement that the historical
`.sat` semantics — `legacyEncodedSat`, which the splice preserves verbatim on
its own branch — already rejects every nested marker.  Both facts below are
unconditional, so nothing the nested branch adds can disturb a query the
historical semantics already answered. -/

/-- The historical semantics rejects every nested base marker. -/
@[simp] theorem legacyEncodedSat_encodeNestedBalancedCNFPayloadMarker
    (payload : ℕ) :
    legacyEncodedSat (encodeNestedBalancedCNFPayloadMarker payload) = false := by
  simp only [legacyEncodedSat,
    wellSizedCNFEncoding_encodeNestedBalancedCNFPayloadMarker,
    Bool.false_eq_true, if_false]

/-- The historical semantics rejects every nested prefix marker. -/
@[simp] theorem legacyEncodedSat_encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) :
    legacyEncodedSat
        (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count) =
      false := by
  simp only [legacyEncodedSat,
    wellSizedCNFEncoding_encodeNestedBalancedPrefixCNFPayloadMarker,
    Bool.false_eq_true, if_false]

/-! ## The core splice, landed

`Semantics.encodedSat` now consults `decodeNestedBalancedCNF` on exactly the
branch both earlier decoders reject, so the promotion below is definitional.
The `…Promotion` predicate and the `_of_promotion` lemmas are kept so that
consumers written against the pre-splice interface continue to elaborate. -/

/-- The frozen `.sat` semantics has been promoted to `nestedEncodedSat`. -/
def NestedEncodedSatPromotion : Prop :=
  ∀ code, encodedSat code = nestedEncodedSat code

/-- The splice is in place: the promotion holds definitionally. -/
theorem nestedEncodedSatPromotion : NestedEncodedSatPromotion := fun _ => rfl

/-- Every decoded nested query receives exactly the historical SAT answer on
the ordinary canonical encoding of its decoded formula. -/
theorem encodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeNestedBalancedCNF code = some formula) :
    encodedSat code = legacyEncodedSat (Encodable.encode formula) :=
  nestedEncodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF hdecode

/-- Acceptance equation for the nested base marker. -/
@[simp] theorem encodedSat_encodeNestedBalancedCanonicalChunks
    (chunks : List (List ℕ)) :
    encodedSat
        (encodeNestedBalancedCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks)) =
      legacyEncodedSat
        (Encodable.encode (decodeCanonicalClauseCodes chunks.flatten)) :=
  nestedEncodedSat_encodeNestedBalancedCanonicalChunks chunks

/-- Acceptance equation for the nested prefix marker. -/
@[simp] theorem encodedSat_encodeNestedBalancedCanonicalChunksPrefix
    (chunks : List (List ℕ)) (assignment count : ℕ) :
    encodedSat
        (encodeNestedBalancedPrefixCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks) assignment count) =
      legacyEncodedSat
        (Encodable.encode
          (balancedPrefixClauses count assignment ++
            decodeCanonicalClauseCodes chunks.flatten)) :=
  nestedEncodedSat_encodeNestedBalancedCanonicalChunksPrefix chunks assignment
    count

/-- Pre-splice compatibility form of the acceptance equation. -/
theorem encodedSat_encodeNestedBalancedCanonicalChunksPrefix_of_promotion
    (_hpromotion : NestedEncodedSatPromotion) (chunks : List (List ℕ))
    (assignment count : ℕ) :
    encodedSat
        (encodeNestedBalancedPrefixCNFPayloadMarker
          (encodeNestedBalancedCNFPayload chunks) assignment count) =
      legacyEncodedSat
        (Encodable.encode
          (balancedPrefixClauses count assignment ++
            decodeCanonicalClauseCodes chunks.flatten)) :=
  encodedSat_encodeNestedBalancedCanonicalChunksPrefix chunks assignment count

end NearCubicWires.NestedBalancedCNFSATEncoding
