import Proof.Foundations.CanonicalBalanced
import StatementSupport

/-!
# Canonical structural binary syntax

The weak register machine has pairing, unpairing, and zero tests, but no
primitive integer arithmetic or trusted decoder opcode.  This module therefore
owns the one raw syntax used at executable validation boundaries: lists are
zero terminated, every nonempty node has the exact tag `1`, and integers are
canonical little-endian bit lists.  Partial decoders reject malformed tags,
non-bits, negative zero, and noncanonical high zeroes.

The definitions are intentionally independent of any circuit family.  Gate,
Fourfold, legal-sum, and recovery-witness codecs share these primitives rather
than maintaining family-specific numeric encodings.
-/

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

/-- Mathlib's canonical `Encodable (List α)` spine, exposed for the fixed CNF
builder that must feed the SAT opcode's historical formula codec.  General
machine data uses `encodeBalancedList`; this linked form is intentionally
confined to SAT syntax whose full width is charged by the exponential runner. -/
def encodeCodeList : List ℕ → ℕ
  | [] => 0
  | value :: rest => Nat.pair value (encodeCodeList rest) + 1

/-! ## A finite machine signature for the constructor tag -/

/-- The tag `1` has a finite signature in the pairing algebra.  This exact
test uses only zero branches, unpairing, and one increment, so the executable
parser never needs an equality opcode or a depth-dependent approximation. -/
def IsOneCode (code : ℕ) : Prop :=
  code ≠ 0 ∧
    (Nat.unpair code).1 = 0 ∧
    (Nat.unpair (code + 1)).2 = 0

theorem isOneCode_iff {code : ℕ} :
    IsOneCode code ↔ code = 1 := by
  constructor
  · rintro ⟨hnonzero, hleft, hright⟩
    let root := (Nat.unpair code).2
    let successorRoot := (Nat.unpair (code + 1)).1
    have hcodePair := Nat.pair_unpair code
    have hsuccessorPair := Nat.pair_unpair (code + 1)
    have hcode : code = root * root := by
      rw [hleft] at hcodePair
      have hroot : 0 < root := by
        by_contra hnot
        have : root = 0 := by omega
        simp [root, this] at hcodePair
        exact hnonzero hcodePair.symm
      simpa [root, Nat.pair, hroot] using hcodePair.symm
    have hsuccessor :
        code + 1 = successorRoot * successorRoot + successorRoot := by
      rw [hright] at hsuccessorPair
      change Nat.pair successorRoot 0 = code + 1 at hsuccessorPair
      simpa [Nat.pair] using hsuccessorPair.symm
    have hrootPositive : 0 < root := by
      by_contra hnot
      have : root = 0 := by omega
      rw [this] at hcode
      exact hnonzero (by omega)
    have hsame : successorRoot = root := by
      rcases lt_trichotomy successorRoot root with hlt | heq | hgt
      · have hle : successorRoot + 1 ≤ root := by omega
        have hproduct :
            successorRoot * successorRoot + successorRoot ≤
              (root - 1) * (root - 1) + (root - 1) := by
          nlinarith
        rw [hcode] at hsuccessor
        nlinarith
      · exact heq
      · rw [hcode] at hsuccessor
        nlinarith
    rw [hsame, hcode] at hsuccessor
    nlinarith
  · rintro rfl
    norm_num [IsOneCode, Nat.unpair]

def isOneCode (code : ℕ) : Bool :=
  code != 0 &&
    (Nat.unpair code).1 == 0 &&
    (Nat.unpair (code + 1)).2 == 0

@[simp] theorem isOneCode_eq_true_iff {code : ℕ} :
    isOneCode code = true ↔ code = 1 := by
  rw [← isOneCode_iff]
  simp [isOneCode, IsOneCode, and_assoc]

/-! ## Structural lists and unary control data -/

def decodeTaggedListAux : ℕ → ℕ → Option (List ℕ)
  | 0, code => if code = 0 then some [] else none
  | fuel + 1, code =>
      if code = 0 then
        some []
      else
        let outer := Nat.unpair code
        if outer.1 = 1 then
          let payload := Nat.unpair outer.2
          (decodeTaggedListAux fuel payload.2).map (payload.1 :: ·)
        else
          none

/-- The code itself is a sufficient termination bound: each valid cell is at
least one larger than its remaining list. -/
def decodeTaggedListCandidate (code : ℕ) : Option (List ℕ) :=
  decodeTaggedListAux code code

theorem encodeTaggedList_length_le (values : List ℕ) :
    values.length ≤ encodeTaggedList values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.length_cons, encodeTaggedList]
      have hinner :
          encodeTaggedList rest ≤
            Nat.pair value (encodeTaggedList rest) :=
        Nat.right_le_pair value (encodeTaggedList rest)
      have houter :=
        Nat.add_le_pair 1
          (Nat.pair value (encodeTaggedList rest))
      omega

theorem decodeTaggedListAux_encode
    (values : List ℕ) (fuel : ℕ) (hfuel : values.length ≤ fuel) :
    decodeTaggedListAux fuel (encodeTaggedList values) = some values := by
  induction values generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons value rest ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hnonzero :
              Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) ≠ 0 := by
            have hleft :=
              Nat.left_le_pair 1
                (Nat.pair value (encodeTaggedList rest))
            omega
          simp only [encodeTaggedList, decodeTaggedListAux,
            if_neg hnonzero, Nat.unpair_pair]
          rw [if_pos trivial]
          rw [ih fuel (by simpa using hfuel)]
          rfl

@[simp] theorem decodeTaggedListCandidate_encode (values : List ℕ) :
    decodeTaggedListCandidate (encodeTaggedList values) = some values := by
  unfold decodeTaggedListCandidate
  exact decodeTaggedListAux_encode values
    (encodeTaggedList values) (encodeTaggedList_length_le values)

/-- Exact re-encoding turns the structural parser into a canonical codec. -/
def decodeTaggedList (code : ℕ) : Option (List ℕ) := do
  let values ← decodeTaggedListCandidate code
  if encodeTaggedList values = code then some values else none

@[simp] theorem decodeTaggedList_encode (values : List ℕ) :
    decodeTaggedList (encodeTaggedList values) = some values := by
  unfold decodeTaggedList
  rw [decodeTaggedListCandidate_encode]
  simp

theorem encodeTaggedList_of_decode
    {code : ℕ} {values : List ℕ}
    (hdecode : decodeTaggedList code = some values) :
    encodeTaggedList values = code := by
  unfold decodeTaggedList at hdecode
  generalize hcandidate :
    decodeTaggedListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeTaggedList decoded = code then some decoded else none) =
          some values at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

/-- Unary values are used only as structural loop bounds.  Their exact cell
tag matters at an untrusted boundary, so decoding is partial. -/
def encodeUnary : ℕ → ℕ
  | 0 => 0
  | count + 1 => Nat.pair 1 (encodeUnary count)

def decodeUnaryAux : ℕ → ℕ → Option ℕ
  | 0, code => if code = 0 then some 0 else none
  | fuel + 1, code =>
      if code = 0 then
        some 0
      else if (Nat.unpair code).1 = 1 then
        (decodeUnaryAux fuel (Nat.unpair code).2).map (· + 1)
      else
        none

def decodeUnary (code : ℕ) : Option ℕ :=
  decodeUnaryAux code code

theorem encodeUnary_le (count : ℕ) :
    count ≤ encodeUnary count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [encodeUnary]
      have hpair := Nat.add_le_pair 1 (encodeUnary count)
      omega

theorem decodeUnaryAux_encode
    (count fuel : ℕ) (hfuel : count ≤ fuel) :
    decodeUnaryAux fuel (encodeUnary count) = some count := by
  induction count generalizing fuel with
  | zero =>
      cases fuel <;> rfl
  | succ count ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hnonzero : Nat.pair 1 (encodeUnary count) ≠ 0 := by
            have hleft := Nat.left_le_pair 1 (encodeUnary count)
            omega
          simp only [encodeUnary, decodeUnaryAux, if_neg hnonzero,
            Nat.unpair_pair, if_pos]
          rw [ih fuel (by omega)]
          rfl

@[simp] theorem decodeUnary_encode (count : ℕ) :
    decodeUnary (encodeUnary count) = some count := by
  unfold decodeUnary
  exact decodeUnaryAux_encode count (encodeUnary count)
    (encodeUnary_le count)

/-! ## Canonical finite binary integers -/

@[simp] theorem encodeCodeList_map_boolCode (values : List Bool) :
    encodeCodeList (values.map boolCode) = Encodable.encode values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> simp [encodeCodeList, boolCode, ih]

def decodeBoolCode (code : ℕ) : Option Bool :=
  if code = 0 then some false
  else if code = 1 then some true
  else none

@[simp] theorem decodeBoolCode_boolCode (value : Bool) :
    decodeBoolCode (boolCode value) = some value := by
  cases value <;> rfl

def decodeBoolCodes : List ℕ → Option (List Bool)
  | [] => some []
  | code :: codes => do
      let value ← decodeBoolCode code
      let values ← decodeBoolCodes codes
      pure (value :: values)

@[simp] theorem decodeBoolCodes_map_boolCode (values : List Bool) :
    decodeBoolCodes (values.map boolCode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [decodeBoolCodes, ih]

def decodeBoolListCandidate (code : ℕ) : Option (List Bool) := do
  let raw ← decodeBalancedList code
  decodeBoolCodes raw

/-- Boolean vectors do not impose a high-bit convention; their length is
provided by the surrounding typed circuit. -/
def decodeBoolList (code : ℕ) : Option (List Bool) :=
  (decodeBoolListCandidate code).bind fun values =>
    if encodeBoolList values = code then some values else none

@[simp] theorem decodeBoolList_encode (values : List Bool) :
    decodeBoolList (encodeBoolList values) = some values := by
  have hcandidate :
      decodeBoolListCandidate (encodeBoolList values) = some values := by
    unfold decodeBoolListCandidate encodeBoolList
    rw [decodeBalancedList_encode]
    exact decodeBoolCodes_map_boolCode values
  unfold decodeBoolList
  rw [hcandidate]
  simp

theorem encodeBoolList_of_decode
    {code : ℕ} {values : List Bool}
    (hdecode : decodeBoolList code = some values) :
    encodeBoolList values = code := by
  unfold decodeBoolList at hdecode
  generalize hcandidate :
    decodeBoolListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

def decodeBitsCandidate (code : ℕ) : Option (List Bool) :=
  decodeBoolList code

/-- A bit list is canonical when it is empty or its most significant bit is
`true`.  Exact re-encoding also rules out every alternate structural code. -/
def decodeBits (code : ℕ) : Option (List Bool) := do
  let values ← decodeBitsCandidate code
  if values = [] ∨ values.getLast? = some true then
    if encodeBits values = code then some values else none
  else
    none

theorem encodeBits_of_decode
    {code : ℕ} {values : List Bool}
    (hdecode : decodeBits code = some values) :
    encodeBits values = code := by
  unfold decodeBits at hdecode
  generalize hcandidate : decodeBitsCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if decoded = [] ∨ decoded.getLast? = some true then
          if encodeBits decoded = code then some decoded else none
        else none) = some values at hdecode
      split at hdecode
      · split at hdecode
        · rename_i hcanonical
          simp only [Option.some.injEq] at hdecode
          subst decoded
          exact hcanonical
        · simp at hdecode
      · simp at hdecode

theorem Nat.bits_canonical (value : ℕ) :
    value.bits = [] ∨ value.bits.getLast? = some true := by
  induction value using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue]
      cases hbits : value.bits with
      | nil =>
          have hvalueZero : value = 0 := by
            have hlength :
                value.bits.length = value.size :=
              Nat.size_eq_bits_len value
            rw [hbits] at hlength
            exact Nat.size_eq_zero.mp (by simpa using hlength.symm)
          have hbit : bit = true := hvalue hvalueZero
          subst bit
          simp
      | cons head tail =>
          right
          rcases ih with hempty | hlast
          · simp [hbits] at hempty
          · simpa [hbits] using hlast

@[simp] theorem decodeBits_encode_natBits (value : ℕ) :
    decodeBits (encodeBits value.bits) = some value.bits := by
  have hcandidate :
      decodeBitsCandidate (encodeBits value.bits) = some value.bits := by
    exact decodeBoolList_encode value.bits
  unfold decodeBits
  rw [hcandidate]
  change
    (if value.bits = [] ∨ value.bits.getLast? = some true then
      if encodeBits value.bits = encodeBits value.bits then
        some value.bits
      else none
    else none) = some value.bits
  rw [if_pos (Nat.bits_canonical value)]
  rw [if_pos rfl]

theorem bitsValue_natBits (value : ℕ) :
    bitsValue value.bits = value := by
  induction value using Nat.binaryRec' with
  | zero => rfl
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue]
      simp only [bitsValue, ih]
      cases bit
      · simp [Nat.bit]
      · simp [Nat.bit]
        omega

/-- Polynomial register-width charge for the total `encodeNat` machine
instruction. -/
def encodeNatBitsBound (sourceBits : ℕ) : ℕ :=
  1 + 2 * sourceBits ^ 4 * (sourceBits + 1)

theorem encodeNat_bits_le (value : ℕ) :
    natBitLength (encodeNat value) ≤
      encodeNatBitsBound (natBitLength value) := by
  have hlength : value.bits.length ≤ natBitLength value := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    simpa [natBitLength, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)
  have hboolBits (bit : Bool) :
      natBitLength (boolCode bit) = 1 := by
    cases bit <;> rfl
  have hsum (bits : List Bool) :
      (bits.map (natBitLength ∘ boolCode)).sum = bits.length := by
    induction bits with
    | nil => rfl
    | cons bit bits ih =>
        simp [hboolBits, ih, Nat.add_comm]
  have hatom :
      balancedListAtomBits (value.bits.map boolCode) =
        value.bits.length + 1 := by
    unfold balancedListAtomBits
    rw [List.map_map, hsum]
  calc
    natBitLength (encodeNat value) ≤
        1 + 2 * value.bits.length ^ 4 *
          balancedListAtomBits (value.bits.map boolCode) := by
      simpa [encodeNat, encodeBits, encodeBoolList] using
        balancedListCodeBits_le (value.bits.map boolCode)
    _ = 1 + 2 * value.bits.length ^ 4 *
          (value.bits.length + 1) := by rw [hatom]
    _ ≤ encodeNatBitsBound (natBitLength value) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlength 4)
      · exact Nat.add_le_add_right hlength 1

def decodeNat (code : ℕ) : Option ℕ := do
  let bits ← decodeBits code
  let value := bitsValue bits
  if encodeNat value = code then some value else none

@[simp] theorem decodeNat_encode (value : ℕ) :
    decodeNat (encodeNat value) = some value := by
  unfold decodeNat encodeNat
  rw [decodeBits_encode_natBits]
  change
    (if encodeNat (bitsValue value.bits) = encodeBits value.bits then
      some (bitsValue value.bits)
    else none) = some value
  rw [bitsValue_natBits]
  simp [encodeNat]

theorem encodeNat_of_decode
    {code value : ℕ} (hdecode : decodeNat code = some value) :
    encodeNat value = code := by
  unfold decodeNat at hdecode
  generalize hbits : decodeBits code = bitsOption at hdecode
  cases bitsOption with
  | none => simp at hdecode
  | some bits =>
      change
        (if encodeNat (bitsValue bits) = code then
          some (bitsValue bits)
        else none) = some value at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst value
        exact hcanonical
      · simp at hdecode

def encodeInt (value : ℤ) : ℕ :=
  Nat.pair (if value < 0 then 1 else 0) (encodeNat value.natAbs)

def decodeIntCandidate (code : ℕ) : Option ℤ := do
  let sign ← decodeBoolCode (Nat.unpair code).1
  let magnitude ← decodeNat (Nat.unpair code).2
  if sign ∧ magnitude = 0 then
    none
  else
    pure (if sign then -(magnitude : ℤ) else (magnitude : ℤ))

def decodeInt (code : ℕ) : Option ℤ := do
  let value ← decodeIntCandidate code
  if encodeInt value = code then some value else none

theorem encodeInt_of_decode
    {code : ℕ} {value : ℤ}
    (hdecode : decodeInt code = some value) :
    encodeInt value = code := by
  unfold decodeInt at hdecode
  generalize hcandidate : decodeIntCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeInt decoded = code then some decoded else none) =
          some value at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

@[simp] theorem decodeInt_encode (value : ℤ) :
    decodeInt (encodeInt value) = some value := by
  unfold decodeInt decodeIntCandidate encodeInt
  rw [Nat.unpair_pair]
  dsimp only
  cases value with
  | ofNat magnitude =>
      simp [decodeBoolCode]
  | negSucc magnitude =>
      have hrepr :
          -1 + -(magnitude : ℤ) = Int.negSucc magnitude := by
        omega
      simp [decodeBoolCode, hrepr]

@[simp] theorem encodeInt_eq_zero_iff (value : ℤ) :
    encodeInt value = 0 ↔ value = 0 := by
  have hzero : encodeInt (0 : ℤ) = 0 := by
    simp [encodeInt, encodeNat, encodeBits, encodeBoolList,
      encodeBalancedList, Nat.pair]
  constructor
  · intro hequal
    have hdecode :=
      congrArg decodeInt (hequal.trans hzero.symm)
    simpa using hdecode
  · rintro rfl
    exact hzero

/-! ## Canonical lists of binary atoms -/

def encodeNatList (values : List ℕ) : ℕ :=
  encodeBalancedList (values.map encodeNat)

def decodeNatCodes : List ℕ → Option (List ℕ)
  | [] => some []
  | code :: codes => do
      let value ← decodeNat code
      let values ← decodeNatCodes codes
      pure (value :: values)

def decodeNatListCandidate (code : ℕ) : Option (List ℕ) := do
  let codes ← decodeBalancedList code
  decodeNatCodes codes

def decodeNatList (code : ℕ) : Option (List ℕ) :=
  (decodeNatListCandidate code).bind fun values =>
    if encodeNatList values = code then some values else none

@[simp] theorem decodeNatCodes_map_encodeNat (values : List ℕ) :
    decodeNatCodes (values.map encodeNat) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [decodeNatCodes, ih]

@[simp] theorem decodeNatList_encode (values : List ℕ) :
    decodeNatList (encodeNatList values) = some values := by
  have hcandidate :
      decodeNatListCandidate (encodeNatList values) = some values := by
    unfold decodeNatListCandidate encodeNatList
    rw [decodeBalancedList_encode]
    exact decodeNatCodes_map_encodeNat values
  unfold decodeNatList
  rw [hcandidate]
  simp

def encodeIntList (values : List ℤ) : ℕ :=
  encodeBalancedList (values.map encodeInt)

def decodeIntCodes : List ℕ → Option (List ℤ)
  | [] => some []
  | code :: codes => do
      let value ← decodeInt code
      let values ← decodeIntCodes codes
      pure (value :: values)

def decodeIntListCandidate (code : ℕ) : Option (List ℤ) := do
  let codes ← decodeBalancedList code
  decodeIntCodes codes

def decodeIntList (code : ℕ) : Option (List ℤ) :=
  (decodeIntListCandidate code).bind fun values =>
    if encodeIntList values = code then some values else none

@[simp] theorem decodeIntCodes_map_encodeInt (values : List ℤ) :
    decodeIntCodes (values.map encodeInt) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [decodeIntCodes, ih]

@[simp] theorem decodeIntList_encode (values : List ℤ) :
    decodeIntList (encodeIntList values) = some values := by
  have hcandidate :
      decodeIntListCandidate (encodeIntList values) = some values := by
    unfold decodeIntListCandidate encodeIntList
    rw [decodeBalancedList_encode]
    exact decodeIntCodes_map_encodeInt values
  unfold decodeIntList
  rw [hcandidate]
  simp

theorem encodeIntList_of_decode
    {code : ℕ} {values : List ℤ}
    (hdecode : decodeIntList code = some values) :
    encodeIntList values = code := by
  unfold decodeIntList at hdecode
  generalize hcandidate :
    decodeIntListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst values
        exact hcanonical
      · simp at hdecode

/-! ## Shared binary arithmetic certificates -/

/-- Addition certificates expose the operands and result in the same canonical
binary syntax.  The equality is executable and uniquely determines the result;
later machine validation refines this predicate to a ripple-carry trace. -/
structure AddCertificate where
  left : ℕ
  right : ℕ
  result : ℕ

def AddCertificate.code (certificate : AddCertificate) : ℕ :=
  encodeTaggedList
    [encodeNat certificate.left, encodeNat certificate.right,
      encodeNat certificate.result]

def decodeAddCertificateCandidate (code : ℕ) : Option AddCertificate := do
  let fields ← decodeTaggedList code
  match fields with
  | [leftCode, rightCode, resultCode] =>
      let left ← decodeNat leftCode
      let right ← decodeNat rightCode
      let result ← decodeNat resultCode
      if result = left + right then
        pure ⟨left, right, result⟩
      else
        none
  | _ => none

def decodeAddCertificate (code : ℕ) : Option AddCertificate :=
  (decodeAddCertificateCandidate code).bind fun certificate =>
    if certificate.code = code then some certificate else none

theorem AddCertificate.code_of_decode
    {code : ℕ} {certificate : AddCertificate}
    (hdecode : decodeAddCertificate code = some certificate) :
    certificate.code = code := by
  unfold decodeAddCertificate at hdecode
  generalize hcandidate :
    decodeAddCertificateCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

def canonicalAddCertificate (left right : ℕ) : AddCertificate :=
  ⟨left, right, left + right⟩

@[simp] theorem decodeAddCertificate_encode (left right : ℕ) :
    decodeAddCertificate (canonicalAddCertificate left right).code =
      some (canonicalAddCertificate left right) := by
  have hcandidate :
      decodeAddCertificateCandidate
          (canonicalAddCertificate left right).code =
        some (canonicalAddCertificate left right) := by
    unfold decodeAddCertificateCandidate AddCertificate.code
      canonicalAddCertificate
    rw [decodeTaggedList_encode]
    change
      (do
        let decodedLeft ← decodeNat (encodeNat left)
        let decodedRight ← decodeNat (encodeNat right)
        let decodedResult ← decodeNat (encodeNat (left + right))
        if decodedResult = decodedLeft + decodedRight then
          pure ⟨decodedLeft, decodedRight, decodedResult⟩
        else none) =
          some (canonicalAddCertificate left right)
    simp [canonicalAddCertificate]
  unfold decodeAddCertificate
  rw [hcandidate]
  simp

/-- Multiplication uses the same canonical operand/result boundary. -/
structure MulCertificate where
  left : ℕ
  right : ℕ
  result : ℕ

def MulCertificate.code (certificate : MulCertificate) : ℕ :=
  encodeTaggedList
    [encodeNat certificate.left, encodeNat certificate.right,
      encodeNat certificate.result]

def decodeMulCertificateCandidate (code : ℕ) : Option MulCertificate := do
  let fields ← decodeTaggedList code
  match fields with
  | [leftCode, rightCode, resultCode] =>
      let left ← decodeNat leftCode
      let right ← decodeNat rightCode
      let result ← decodeNat resultCode
      if result = left * right then
        pure ⟨left, right, result⟩
      else
        none
  | _ => none

def decodeMulCertificate (code : ℕ) : Option MulCertificate :=
  (decodeMulCertificateCandidate code).bind fun certificate =>
    if certificate.code = code then some certificate else none

theorem MulCertificate.code_of_decode
    {code : ℕ} {certificate : MulCertificate}
    (hdecode : decodeMulCertificate code = some certificate) :
    certificate.code = code := by
  unfold decodeMulCertificate at hdecode
  generalize hcandidate :
    decodeMulCertificateCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

def canonicalMulCertificate (left right : ℕ) : MulCertificate :=
  ⟨left, right, left * right⟩

@[simp] theorem decodeMulCertificate_encode (left right : ℕ) :
    decodeMulCertificate (canonicalMulCertificate left right).code =
      some (canonicalMulCertificate left right) := by
  have hcandidate :
      decodeMulCertificateCandidate
          (canonicalMulCertificate left right).code =
        some (canonicalMulCertificate left right) := by
    unfold decodeMulCertificateCandidate MulCertificate.code
      canonicalMulCertificate
    rw [decodeTaggedList_encode]
    change
      (do
        let decodedLeft ← decodeNat (encodeNat left)
        let decodedRight ← decodeNat (encodeNat right)
        let decodedResult ← decodeNat (encodeNat (left * right))
        if decodedResult = decodedLeft * decodedRight then
          pure ⟨decodedLeft, decodedRight, decodedResult⟩
        else none) =
          some (canonicalMulCertificate left right)
    simp [canonicalMulCertificate]
  unfold decodeMulCertificate
  rw [hcandidate]
  simp

end NearCubicWires.CanonicalBinary
