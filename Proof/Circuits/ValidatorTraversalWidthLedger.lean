import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorNatWidthLedger

namespace NearCubicWires.ValidatorTraversalWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination

open private taggedBitFoldWorkingValues taggedBitFoldWorkBound from
  Proof.MachineModel.CanonicalNatDecodeProgram

open private candidateWithRawBits from Proof.MachineModel.CanonicalNatValidationProgram

open private forkPairedBits forkSecondChoiceBits from
  Proof.Circuits.CanonicalForkCall

/-! ## §1 The tagged-cell codec's geometric width -/

/-- One tagged cell is at least two: the cell's tag is `1`, and a pairing on a
nonzero tag never collapses. -/
theorem two_le_encodeTaggedList_cons (value : ℕ) (rest : List ℕ) :
    2 ≤ encodeTaggedList (value :: rest) := by
  have hcell : ∀ payload : ℕ, 2 ≤ Nat.pair 1 payload := by
    intro payload
    unfold Nat.pair
    rcases Nat.lt_or_ge 1 payload with hlt | hle
    · rw [if_pos hlt]
      nlinarith
    · rw [if_neg (by omega)]
      omega
  simpa only [encodeTaggedList] using
    hcell (Nat.pair value (encodeTaggedList rest))

/-- **One cell at least doubles the width twice.**  A tagged cell is two
pairings over its tail, and a pairing at least squares, so the cell's width is
at least four times the tail's, up to the codec's three-bit slack. -/
theorem four_mul_natBitLength_encodeTaggedList_le_succ
    (value : ℕ) (rest : List ℕ) :
    4 * natBitLength (encodeTaggedList rest) ≤
      natBitLength (encodeTaggedList (value :: rest)) + 3 := by
  have hinner :=
    two_mul_natBitLength_max_le_natBitLength_pair value (encodeTaggedList rest)
  have houter :=
    two_mul_natBitLength_max_le_natBitLength_pair 1
      (Nat.pair value (encodeTaggedList rest))
  have htail :
      natBitLength (encodeTaggedList rest) ≤
        natBitLength (max value (encodeTaggedList rest)) :=
    ValidatorLeafWidthCore.natBitLength_mono (le_max_right _ _)
  have hcell :
      natBitLength (Nat.pair value (encodeTaggedList rest)) ≤
        natBitLength (max 1 (Nat.pair value (encodeTaggedList rest))) :=
    ValidatorLeafWidthCore.natBitLength_mono (le_max_right _ _)
  simp only [encodeTaggedList]
  omega

/-- **The codec's geometric width.**  A tagged list of `n` public values is at
least `2 ^ n` bits wide.  This is the fact the whole module rests on: it is a
*lower* bound, and it is charged per public element. -/
theorem two_pow_length_le_natBitLength_encodeTaggedList (values : List ℕ) :
    2 ^ values.length ≤ natBitLength (encodeTaggedList values) := by
  induction values with
  | nil =>
      have hzero : natBitLength 0 = 1 := natBitLength_zero
      simpa [encodeTaggedList] using hzero.ge
  | cons value rest inductionHypothesis =>
      cases rest with
      | nil =>
          have hcell := two_le_encodeTaggedList_cons value ([] : List ℕ)
          have hwidth := two_le_natBitLength hcell
          simpa using hwidth
      | cons second tail =>
          have hstep :=
            four_mul_natBitLength_encodeTaggedList_le_succ value (second :: tail)
          obtain ⟨tailPower, htailPower⟩ :
              ∃ power : ℕ, (2 : ℕ) ^ (second :: tail).length = power := ⟨_, rfl⟩
          have htwo : 2 ≤ tailPower := by
            rw [← htailPower]
            have : (2 : ℕ) ^ 1 ≤ 2 ^ (second :: tail).length :=
              Nat.pow_le_pow_right (by omega) (by simp)
            simpa using this
          have hsucc :
              (2 : ℕ) ^ (value :: second :: tail).length = 2 * tailPower := by
            rw [← htailPower]
            simp only [List.length_cons]
            rw [pow_succ]
            ring
          rw [htailPower] at inductionHypothesis
          rw [hsucc]
          omega

/-! ## §2 The decode-list width -/

/-- The bit fold's working set opens with the whole tagged bit list. -/
theorem natBitLength_encodeTaggedList_le_taggedBitFoldBits (bits : List ℕ) :
    natBitLength (encodeTaggedList bits) ≤ taggedBitFoldBits bits := by
  cases bits with
  | nil =>
      have hzero : natBitLength 0 = 1 := natBitLength_zero
      have hpositive :=
        one_le_natBitLength (taggedBitFoldWorkBound ([] : List ℕ))
      simp only [encodeTaggedList, taggedBitFoldBits]
      omega
  | cons bit rest =>
      have hmember :
          encodeTaggedList (bit :: rest) ≤ taggedBitFoldWorkBound (bit :: rest) := by
        simp only [taggedBitFoldWorkBound, taggedBitFoldWorkingValues,
          List.cons_append, List.foldr_cons]
        exact Nat.le_max_left _ _
      exact ValidatorLeafWidthCore.natBitLength_mono hmember

/-- **The decoded bit fold's width, from below.** -/
theorem two_pow_length_le_taggedBitFoldBits (bits : List ℕ) :
    2 ^ bits.length ≤ taggedBitFoldBits bits :=
  (two_pow_length_le_natBitLength_encodeTaggedList bits).trans
    (natBitLength_encodeTaggedList_le_taggedBitFoldBits bits)

/-- **The first residual width, from below.**  `canonicalNatDecodeListBits` is
at least `2 ^ bits.length`: the decoder's fold materializes the whole tagged
bit list in one register. -/
theorem two_pow_length_le_canonicalNatDecodeListBits
    (inputLength : ℕ) (bits : List ℕ) :
    2 ^ bits.length ≤ canonicalNatDecodeListBits inputLength bits := by
  have hfold := two_pow_length_le_taggedBitFoldBits bits
  obtain ⟨power, hpower⟩ : ∃ power : ℕ, (2 : ℕ) ^ bits.length = power := ⟨_, rfl⟩
  rw [hpower] at hfold ⊢
  simp only [canonicalNatDecodeListBits, taggedBitFoldMaximumBits]
  omega

/-! ## §3 The builder's clock width -/

/-- A `pairIter` clock at depth `d` over a base of at least two is at least
`2 ^ d` bits wide. -/
theorem two_pow_le_natBitLength_pairIter {base : ℕ} (hbase : 2 ≤ base)
    (depth : ℕ) : 2 ^ depth ≤ natBitLength (pairIter depth base) := by
  have hpower : (2 : ℕ) ^ 2 ^ depth ≤ base ^ 2 ^ depth :=
    Nat.pow_le_pow_left hbase _
  have hclock : base ^ 2 ^ depth ≤ pairIter depth base :=
    pow_twoPow_le_pairIter depth base
  have hlog : 2 ^ depth ≤ Nat.log 2 (pairIter depth base) := by
    refine Nat.le_log_of_pow_le (by omega) ?_
    omega
  simp only [natBitLength]
  omega

/-- **The builder's register charge, from below.**  The canonical midpoint
builder is charged at a `pairIter` clock whose depth is its own fuel, and that
fuel is linear in the list length. -/
theorem two_pow_taggedToBalancedFuel_le_taggedToBalancedRegisterBitsFor
    (inputLength : ℕ) (values : List ℕ) :
    2 ^ taggedToBalancedFuel values ≤
      taggedToBalancedRegisterBitsFor inputLength values := by
  have hbase :
      2 ≤ taggedToBalancedInitialBoundFor inputLength values := by
    simp only [taggedToBalancedInitialBoundFor]
    omega
  simpa only [taggedToBalancedRegisterBitsFor] using
    two_pow_le_natBitLength_pairIter hbase (taggedToBalancedFuel values)

/-- **The second residual width, from below.**  `balancedRawCanonicalizeBits`
carries the builder's clock, so it is at least `2 ^ (5 · atoms.length)`. -/
theorem two_pow_le_balancedRawCanonicalizeBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) :
    2 ^ (5 * tree.atoms.length) ≤
      balancedRawCanonicalizeBits inputLength tree := by
  have hbuilder :=
    two_pow_taggedToBalancedFuel_le_taggedToBalancedRegisterBitsFor inputLength
      tree.normalized.atoms
  have hfuel : 5 * tree.atoms.length ≤ taggedToBalancedFuel tree.normalized.atoms := by
    simp only [taggedToBalancedFuel, RawBalancedTraversalTree.atoms]
    omega
  have hmonotone :
      (2 : ℕ) ^ (5 * tree.atoms.length) ≤ 2 ^ taggedToBalancedFuel tree.normalized.atoms :=
    Nat.pow_le_pow_right (by omega) hfuel
  obtain ⟨small, hsmall⟩ :
      ∃ value : ℕ, (2 : ℕ) ^ (5 * tree.atoms.length) = value := ⟨_, rfl⟩
  obtain ⟨large, hlarge⟩ :
      ∃ value : ℕ, (2 : ℕ) ^ taggedToBalancedFuel tree.normalized.atoms = value :=
    ⟨_, rfl⟩
  rw [hsmall] at hmonotone ⊢
  rw [hlarge] at hmonotone hbuilder
  simp only [balancedRawCanonicalizeBits, balancedCanonicalizeBits]
  omega

/-! ## §4 The three residual widths, and the circuit validator

`ValidatorNatWidthLedger` §4 lists three residual charges.  §2 and §3 close two
of them from below; this section transports both up through the wrapper
combinators — every one of which is a `max` over its callee — to the Boolean
circuit validator's own width, the charge `hcall` consumes. -/

/-- **The context-preserving wrapper's width, from below.**  Every wrapper on
the validator's width cone is a `max` over its callee. -/
theorem le_preserveRightBits (sourceBits left right output : ℕ) :
    sourceBits ≤ preserveRightBits sourceBits left right output := by
  simp only [preserveRightBits]
  omega

/-- **The fork call's width, from below**, at its second callee. -/
theorem le_forkCallBits_second
    (inputLength raw firstBits secondBits firstOutput secondOutput : ℕ) :
    secondBits ≤
      forkCallBits inputLength raw firstBits secondBits firstOutput
        secondOutput := by
  simp only [forkCallBits, forkPairedBits, pairedCallBits, preserveRightBits,
    forkSecondChoiceBits]
  omega

/-- The candidate pass carries the decoder's charge. -/
theorem two_pow_atoms_le_canonicalNatCandidateBits (inputLength raw : ℕ) :
    2 ^ (rawBalancedTraversalTree raw).atoms.length ≤
      canonicalNatCandidateBits inputLength raw := by
  have hdecode :=
    two_pow_length_le_canonicalNatDecodeListBits inputLength
      (rawBalancedTraversalTree raw).atoms
  obtain ⟨power, hpower⟩ :
      ∃ value : ℕ,
        (2 : ℕ) ^ (rawBalancedTraversalTree raw).atoms.length = value :=
    ⟨_, rfl⟩
  rw [hpower] at hdecode ⊢
  simp only [canonicalNatCandidateBits]
  omega

/-- **The canonical natural validator's width, from below.** -/
theorem two_pow_atoms_le_canonicalNatValidationBits (inputLength raw : ℕ) :
    2 ^ (rawBalancedTraversalTree raw).atoms.length ≤
      canonicalNatValidationBits inputLength raw := by
  have hcandidate := two_pow_atoms_le_canonicalNatCandidateBits inputLength raw
  obtain ⟨power, hpower⟩ :
      ∃ value : ℕ,
        (2 : ℕ) ^ (rawBalancedTraversalTree raw).atoms.length = value :=
    ⟨_, rfl⟩
  rw [hpower] at hcandidate ⊢
  have hwrapper :=
    le_preserveRightBits (canonicalNatCandidateBits inputLength raw) raw raw
      (canonicalNatCandidate raw)
  simp only [canonicalNatValidationBits, candidateWithRawBits]
  omega

/-- **The Boolean circuit validator's width, from below.**  This is exactly the
charge `ValidatorOracleCallWidth` §3 consumes on the way to `hcall`. -/
theorem two_pow_atoms_le_booleanCircuitValidationBits (inputLength raw : ℕ) :
    2 ^ (rawBalancedTraversalTree (booleanCircuitOutputCode raw)).atoms.length ≤
      booleanCircuitValidationBits inputLength raw := by
  have hnat :=
    two_pow_atoms_le_canonicalNatValidationBits inputLength
      (booleanCircuitOutputCode raw)
  obtain ⟨power, hpower⟩ :
      ∃ value : ℕ,
        (2 : ℕ) ^
            (rawBalancedTraversalTree
              (booleanCircuitOutputCode raw)).atoms.length = value :=
    ⟨_, rfl⟩
  rw [hpower] at hnat ⊢
  have hwrapper :=
    le_preserveRightBits
      (canonicalNatValidationBits inputLength (booleanCircuitOutputCode raw))
      (booleanCircuitOutputCode raw)
      (Nat.pair
        (booleanNodeListValidationOutput inputLength
          (booleanCircuitNodesCode raw))
        (booleanCircuitTupleFlag raw))
      (canonicalNatValidationOutput (booleanCircuitOutputCode raw))
  simp only [booleanCircuitValidationBits, booleanCircuitNatStageBits]
  omega

/-- **The node-list validator's width, from below.**  The third residual: the
normalizer's fork carries the builder's clock. -/
theorem two_pow_le_booleanNodeListValidationBits (inputLength raw : ℕ) :
    2 ^ (5 * (rawBalancedTraversalTree raw).atoms.length) ≤
      booleanNodeListValidationBits inputLength raw := by
  have hnormalize :=
    two_pow_le_balancedRawCanonicalizeBits inputLength
      (rawBalancedTraversalTree raw)
  obtain ⟨power, hpower⟩ :
      ∃ value : ℕ,
        (2 : ℕ) ^ (5 * (rawBalancedTraversalTree raw).atoms.length) = value :=
    ⟨_, rfl⟩
  have hfork :=
    le_forkCallBits_second inputLength raw
      (balancedCanonicalityBits inputLength raw)
      (balancedRawCanonicalizeBits inputLength (rawBalancedTraversalTree raw))
      (balancedCanonicalityOutput raw) (booleanNodeListNormalizedCode raw)
  rw [hpower] at hnormalize ⊢
  simp only [booleanNodeListValidationBits, booleanNodeListNormalizeBits]
  omega

/-- **`hcall`'s own charge carries the circuit validator's width.**  The
oracle call's register requirement is a native contextual call whose callee
width *is* `booleanCircuitValidationBits` at the handoff's two projections. -/
theorem booleanCircuitValidationBits_le_recoveryOracleCallBits
    (inputLength handoff : ℕ) :
    booleanCircuitValidationBits (handoffOracleArity handoff)
        (handoffOracleCode handoff) ≤
      recoveryOracleCallBits inputLength handoff := by
  simp only [recoveryOracleCallBits, nativeContextCallBits, preserveRightBits,
    nativeCallBits]
  omega

/-- **The charge `hcall` asks to dominate, from below.** -/
theorem two_pow_atoms_le_recoveryOracleCallBits (inputLength handoff : ℕ) :
    2 ^
        (rawBalancedTraversalTree
          (booleanCircuitOutputCode
            (handoffOracleCode handoff))).atoms.length ≤
      recoveryOracleCallBits inputLength handoff :=
  (two_pow_atoms_le_booleanCircuitValidationBits (handoffOracleArity handoff)
    (handoffOracleCode handoff)).trans
    (booleanCircuitValidationBits_le_recoveryOracleCallBits inputLength handoff)

/-! ## §5 An explicit canonical family

Nothing above says the atom count is ever large.  This section exhibits a
family of *canonical* balanced codes on which the atom count is `n` while the
code's own width stays quadratic in `n` — so the validator's width outruns
every fixed polynomial in the code's width, and the domination judgement
`hcall` asks for cannot hold at any coefficient and any degree. -/

/-- The canonical balanced code of `n` unit atoms. -/
def canonicalAtomFamily (n : ℕ) : ℕ :=
  encodeBalancedList (List.replicate n 1)

/-- The structural parse recovers the family's atoms exactly. -/
theorem atoms_canonicalAtomFamily (n : ℕ) :
    (rawBalancedTraversalTree (canonicalAtomFamily n)).atoms =
      List.replicate n 1 := by
  have hcode :
      canonicalAtomFamily n =
        (balancedTraversalTree (List.replicate n 1)).code := by
    simp only [canonicalAtomFamily, balancedTraversalTree_code]
  rw [hcode]
  simp only [RawBalancedTraversalTree.atoms,
    rawBalancedTraversalTree_normalized_code, balancedTraversalTree_atoms]

/-- The family's own width is quadratic in its atom count. -/
theorem natBitLength_canonicalAtomFamily_le (n : ℕ) :
    natBitLength (canonicalAtomFamily n) ≤ 16 * (n + 1) ^ 2 := by
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hmembers :
      ∀ value ∈ List.replicate n 1, natBitLength value ≤ 1 := by
    intro value hvalue
    rw [List.eq_of_mem_replicate hvalue]
    omega
  have hbound :=
    natBitLength_encodeBalancedList_le_quadratic (List.replicate n 1) 1
      (by omega) hmembers
  simpa [canonicalAtomFamily] using hbound

/-- **The family's validator width.**  Exponential in the atom count. -/
theorem two_pow_le_canonicalNatValidationBits_canonicalAtomFamily
    (inputLength n : ℕ) :
    2 ^ n ≤ canonicalNatValidationBits inputLength (canonicalAtomFamily n) := by
  have hbound :=
    two_pow_atoms_le_canonicalNatValidationBits inputLength
      (canonicalAtomFamily n)
  rwa [atoms_canonicalAtomFamily, List.length_replicate] at hbound

/-- Any uniform domination certificate for the family — even one anchored on
the *code's own width*, the most generous anchor there is — forces an
exponential below a fixed polynomial. -/
theorem two_pow_le_budget_of_polyBounded_canonicalAtomFamily
    (inputLength coefficient degree : ℕ)
    (hbudget : ∀ n : ℕ,
      PolyBounded
        (canonicalNatValidationBits inputLength (canonicalAtomFamily n))
        (natBitLength (canonicalAtomFamily n)) coefficient degree)
    (n : ℕ) :
    2 ^ n ≤ coefficient * (16 * (n + 1) ^ 2 + 1) ^ degree := by
  have hwidth := natBitLength_canonicalAtomFamily_le n
  have hcharge :=
    two_pow_le_canonicalNatValidationBits_canonicalAtomFamily inputLength n
  have hpolyBounded := hbudget n
  unfold PolyBounded at hpolyBounded
  have hmonotone :
      coefficient * (natBitLength (canonicalAtomFamily n) + 1) ^ degree ≤
        coefficient * (16 * (n + 1) ^ 2 + 1) ^ degree :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) degree)
  omega

/-! ## §6 The obstruction

§5 forces an exponential below a fixed polynomial.  This section spends that
into an outright contradiction: a doubling per public atom is not dominated by
any polynomial in the code's width, at any coefficient and any degree. -/

/-- Every fixed polynomial is eventually beaten by `2 ^ n`.  The witness is
explicit: `n = 2 ^ (4 · (natBitLength constant + exponent + 1))`. -/
private theorem poly_lt_two_pow (constant exponent : ℕ) :
    ∃ index : ℕ, constant * (index + 1) ^ exponent < 2 ^ index := by
  obtain ⟨width, hwidth⟩ :
      ∃ value : ℕ, natBitLength constant = value := ⟨_, rfl⟩
  obtain ⟨step, hstep⟩ :
      ∃ value : ℕ, width + exponent + 1 = value := ⟨_, rfl⟩
  obtain ⟨index, hindex⟩ :
      ∃ value : ℕ, (2 : ℕ) ^ (4 * step) = value := ⟨_, rfl⟩
  refine ⟨index, ?_⟩
  have hdefinition : natBitLength constant = Nat.log 2 constant + 1 := rfl
  have hconstant : constant < 2 ^ width := by
    have hlog := Nat.lt_pow_succ_log_self (b := 2) (by omega) constant
    have hexponent : Nat.log 2 constant + 1 = width := by omega
    simp only [Nat.succ_eq_add_one] at hlog
    rwa [hexponent] at hlog
  have hstepPositive : 1 ≤ step := by omega
  have hbase : step + 1 ≤ 2 ^ step := Nat.lt_two_pow_self
  have hfourth : (2 : ℕ) ^ (4 * step) = (2 ^ step) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  have hquartic : (step + 1) ^ 4 ≤ index := by
    rw [← hindex, hfourth]
    exact Nat.pow_le_pow_left hbase 4
  have hbudget : width + (4 * step + 1) * exponent ≤ (step + 1) ^ 4 := by
    have hleftBound : width ≤ step := by omega
    have hrightBound : exponent ≤ step := by omega
    have hmul : (4 * step + 1) * exponent ≤ (4 * step + 1) * step :=
      Nat.mul_le_mul_left _ hrightBound
    have hchain :
        width + (4 * step + 1) * exponent ≤ 4 * (step * step) + 2 * step := by
      nlinarith [hleftBound, hmul]
    have hgrow : 4 * (step * step) + 2 * step ≤ (step + 1) ^ 4 := by
      nlinarith [hstepPositive, Nat.zero_le (step * step * step * step),
        Nat.zero_le (step * step * step)]
    omega
  have hsuccessor : index + 1 ≤ 2 ^ (4 * step + 1) := by
    have hone : 1 ≤ (2 : ℕ) ^ (4 * step) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hpower : (index + 1) ^ exponent ≤ 2 ^ ((4 * step + 1) * exponent) := by
    refine (Nat.pow_le_pow_left hsuccessor exponent).trans ?_
    rw [← pow_mul]
  have hpositive : 0 < (index + 1) ^ exponent :=
    Nat.one_le_pow exponent (index + 1) (by omega)
  have hscaled : constant * (index + 1) ^ exponent <
      2 ^ width * 2 ^ ((4 * step + 1) * exponent) := by
    calc
      constant * (index + 1) ^ exponent <
          2 ^ width * (index + 1) ^ exponent :=
        Nat.mul_lt_mul_of_lt_of_le hconstant (le_refl _) hpositive
      _ ≤ 2 ^ width * 2 ^ ((4 * step + 1) * exponent) :=
        Nat.mul_le_mul_left _ hpower
  have hcombine :
      (2 : ℕ) ^ width * 2 ^ ((4 * step + 1) * exponent) =
        2 ^ (width + (4 * step + 1) * exponent) := by
    rw [← pow_add]
  have hdominate :
      (2 : ℕ) ^ (width + (4 * step + 1) * exponent) ≤ 2 ^ index :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The polynomial the family's budget would have to beat. -/
private theorem exists_two_pow_gt (coefficient degree : ℕ) :
    ∃ n : ℕ, coefficient * (16 * (n + 1) ^ 2 + 1) ^ degree < 2 ^ n := by
  obtain ⟨n, hn⟩ := poly_lt_two_pow (coefficient * 17 ^ degree) (2 * degree)
  refine ⟨n, lt_of_le_of_lt ?_ hn⟩
  have hsquare : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hstep : 16 * (n + 1) ^ 2 + 1 ≤ 17 * (n + 1) ^ 2 := by omega
  calc
    coefficient * (16 * (n + 1) ^ 2 + 1) ^ degree ≤
        coefficient * (17 * (n + 1) ^ 2) ^ degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep degree)
    _ = coefficient * 17 ^ degree * (n + 1) ^ (2 * degree) := by
      rw [mul_pow, ← pow_mul]
      ring

theorem not_polyBounded_canonicalNatValidationBits
    (inputLength coefficient degree : ℕ) :
    ¬ ∀ n : ℕ,
      PolyBounded
        (canonicalNatValidationBits inputLength (canonicalAtomFamily n))
        (natBitLength (canonicalAtomFamily n)) coefficient degree := by
  intro hbudget
  obtain ⟨n, hn⟩ := exists_two_pow_gt coefficient degree
  have hforced :=
    two_pow_le_budget_of_polyBounded_canonicalAtomFamily inputLength
      coefficient degree hbudget n
  omega

end NearCubicWires.ValidatorTraversalWidthLedger
