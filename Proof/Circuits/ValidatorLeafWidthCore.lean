import Proof.Supplier.ValidatorLegalSumWalk

namespace NearCubicWires.ValidatorLeafWidthCore

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ValidatorPolynomialDomination

/-! ## §1 One pairing step at least doubles the width -/

theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

theorem one_le_natBitLength (value : ℕ) : 1 ≤ natBitLength value := by
  unfold natBitLength
  omega

theorem natBitLength_zero : natBitLength 0 = 1 := by
  unfold natBitLength
  simp

theorem natBitLength_one : natBitLength 1 = 1 := by
  unfold natBitLength
  simp

/-- Two bits are needed for every value from `2` up. -/
theorem two_le_natBitLength {value : ℕ} (hle : 2 ≤ value) :
    2 ≤ natBitLength value := by
  have hlog : 1 ≤ Nat.log 2 value :=
    Nat.le_log_of_pow_le (by omega) (by simpa using hle)
  unfold natBitLength
  omega

/-- **Squaring doubles the width**, to within one bit.  This is the whole
reason a decoded cell count is logarithmic in the code. -/
theorem two_mul_natBitLength_le_natBitLength_mul_self (value : ℕ) :
    2 * natBitLength value ≤ natBitLength (value * value) + 1 := by
  rcases Nat.eq_zero_or_pos value with rfl | hpositive
  · simp [natBitLength_zero]
  · have hself : 2 ^ Nat.log 2 value ≤ value :=
      Nat.pow_log_le_self 2 (by omega)
    have hsquare : 2 ^ (Nat.log 2 value * 2) ≤ value * value := by
      rw [Nat.pow_mul]
      calc
        (2 ^ Nat.log 2 value) ^ 2 =
            2 ^ Nat.log 2 value * 2 ^ Nat.log 2 value := by ring
        _ ≤ value * value := Nat.mul_le_mul hself hself
    have hlog : Nat.log 2 value * 2 ≤ Nat.log 2 (value * value) :=
      Nat.le_log_of_pow_le (by omega) hsquare
    unfold natBitLength
    omega

/-- The pairing dominates the square of the larger component. -/
theorem mul_self_max_le_pair (left right : ℕ) :
    max left right * max left right ≤ Nat.pair left right := by
  simp only [Nat.pair]
  split
  · rename_i hlt
    have hmax : max left right = right := by omega
    rw [hmax]
    omega
  · rename_i hnotLt
    have hmax : max left right = left := by omega
    rw [hmax]
    omega

/-- **The width ledger of one pairing.**  The two component widths together
exceed the pair's width by at most one bit — so a pairing never loses more than
a bit of the room it needs. -/
theorem natBitLength_add_le_natBitLength_pair (left right : ℕ) :
    natBitLength left + natBitLength right ≤
      natBitLength (Nat.pair left right) + 1 := by
  have hleft : natBitLength left ≤ natBitLength (max left right) :=
    natBitLength_mono (le_max_left _ _)
  have hright : natBitLength right ≤ natBitLength (max left right) :=
    natBitLength_mono (le_max_right _ _)
  have hsquare :=
    two_mul_natBitLength_le_natBitLength_mul_self (max left right)
  have hpair :
      natBitLength (max left right * max left right) ≤
        natBitLength (Nat.pair left right) :=
    natBitLength_mono (mul_self_max_le_pair left right)
  omega

/-- Tagging with the constant `1` costs a whole bit: this is the step the
tagged-cell codec repeats. -/
theorem natBitLength_succ_le_natBitLength_pair_one (value : ℕ) :
    natBitLength value + 1 ≤ natBitLength (Nat.pair 1 value) := by
  rcases Nat.lt_or_ge value 2 with hsmall | hlarge
  · interval_cases value
    · have : Nat.pair 1 0 = 2 := by simp [Nat.pair]
      rw [this, natBitLength_zero]
      exact two_le_natBitLength (le_refl 2)
    · have : Nat.pair 1 1 = 3 := by simp [Nat.pair]
      rw [this, natBitLength_one]
      exact two_le_natBitLength (by omega)
  · have hwidth : 2 ≤ natBitLength value := two_le_natBitLength hlarge
    have hsquare :=
      two_mul_natBitLength_le_natBitLength_mul_self value
    have hle : value * value ≤ Nat.pair 1 value := by
      have hmax : max 1 value = value := by omega
      have := mul_self_max_le_pair 1 value
      rwa [hmax] at this
    have := natBitLength_mono hle
    omega

/-! ## §2 The structural parser's node count

`rawBalancedTraversalTree` is the total proof view of the fixed depth-first
controller: it accepts *every* natural and produces the tree the controller
would walk.  Its branch case recurses into the two halves of the payload, and
the payload is one pairing below the code while the branch tag costs two bits,
so §1 gives the two halves' widths *together* no more room than the code's.
That is exactly the induction that closes a linear node bound. -/

open RawBalancedTraversalTree in
/-- A branch tag is at least `2`: the controller selects a branch precisely
when the tag's own left projection is nonzero, and neither `0` nor `1` has
that. -/
theorem two_le_of_unpair_fst_ne_zero {tag : ℕ}
    (htag : (Nat.unpair tag).1 ≠ 0) : 2 ≤ tag := by
  have hzero : Nat.unpair 0 = (0, 0) := by
    have hcode : Nat.pair 0 0 = 0 := rfl
    calc
      Nat.unpair 0 = Nat.unpair (Nat.pair 0 0) := by rw [hcode]
      _ = (0, 0) := Nat.unpair_pair 0 0
  have hone : Nat.unpair 1 = (0, 1) := by
    have hcode : Nat.pair 0 1 = 1 := rfl
    calc
      Nat.unpair 1 = Nat.unpair (Nat.pair 0 1) := by rw [hcode]
      _ = (0, 1) := Nat.unpair_pair 0 1
  by_contra hsmall
  interval_cases tag
  · exact htag (by rw [hzero])
  · exact htag (by rw [hone])

theorem rawBalancedTraversalTree_nodeCount_succ_le (code : ℕ) :
    (rawBalancedTraversalTree code).nodeCount + 1 ≤ 2 * natBitLength code := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      rw [rawBalancedTraversalTree]
      split
      · rename_i hzero
        subst hzero
        simp [RawBalancedTraversalTree.nodeCount, natBitLength_zero]
      · rename_i hzero
        dsimp only
        split
        · have hwidth := one_le_natBitLength code
          simp only [RawBalancedTraversalTree.nodeCount]
          omega
        · rename_i hleaf
          have htag : 2 ≤ (Nat.unpair code).1 :=
            two_le_of_unpair_fst_ne_zero hleaf
          have hsplit : (Nat.unpair code).1 + (Nat.unpair code).2 ≤ code :=
            Nat.unpair_add_le code
          have hpayload : (Nat.unpair code).2 < code := by omega
          have hleftLt : (Nat.unpair (Nat.unpair code).2).1 < code :=
            lt_of_le_of_lt (Nat.unpair_left_le _) hpayload
          have hrightLt : (Nat.unpair (Nat.unpair code).2).2 < code :=
            lt_of_le_of_lt (Nat.unpair_right_le _) hpayload
          have hleftBound := inductionHypothesis _ hleftLt
          have hrightBound := inductionHypothesis _ hrightLt
          have hhalves :
              natBitLength (Nat.unpair (Nat.unpair code).2).1 +
                  natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
                natBitLength (Nat.unpair code).2 + 1 := by
            have hpair :=
              natBitLength_add_le_natBitLength_pair
                (Nat.unpair (Nat.unpair code).2).1
                (Nat.unpair (Nat.unpair code).2).2
            rwa [Nat.pair_unpair] at hpair
          have houter :
              natBitLength (Nat.unpair code).1 +
                  natBitLength (Nat.unpair code).2 ≤
                natBitLength code + 1 := by
            have hpair :=
              natBitLength_add_le_natBitLength_pair (Nat.unpair code).1
                (Nat.unpair code).2
            rwa [Nat.pair_unpair] at hpair
          have htagWidth : 2 ≤ natBitLength (Nat.unpair code).1 :=
            two_le_natBitLength htag
          simp only [RawBalancedTraversalTree.nodeCount]
          omega

/-- Normalization erases raw tags only, so it preserves the node count. -/
theorem nodeCount_normalized (tree : RawBalancedTraversalTree) :
    tree.normalized.nodeCount = tree.nodeCount := by
  induction tree with
  | empty => rfl
  | leaf tag atom => rfl
  | branch tag left right ihLeft ihRight =>
      simp [RawBalancedTraversalTree.normalized,
        RawBalancedTraversalTree.nodeCount, BalancedTraversalTree.nodeCount,
        ihLeft, ihRight]

/-- Every balanced tree has at most as many atoms as nodes. -/
theorem atoms_length_le_nodeCount (tree : BalancedTraversalTree) :
    tree.atoms.length ≤ tree.nodeCount := by
  induction tree with
  | empty => simp [BalancedTraversalTree.atoms, BalancedTraversalTree.nodeCount]
  | leaf atom => simp [BalancedTraversalTree.atoms,
      BalancedTraversalTree.nodeCount]
  | branch left right ihLeft ihRight =>
      simp only [BalancedTraversalTree.atoms, BalancedTraversalTree.nodeCount,
        List.length_append]
      omega

/-- **The atom ledger of the structural parser.**  The decoded atom list is
shorter than twice the code's width. -/
theorem rawBalancedTraversalTree_atoms_length_succ_le (code : ℕ) :
    (rawBalancedTraversalTree code).atoms.length + 1 ≤ 2 * natBitLength code := by
  have hatoms :
      (rawBalancedTraversalTree code).atoms.length ≤
        (rawBalancedTraversalTree code).nodeCount := by
    have := atoms_length_le_nodeCount (rawBalancedTraversalTree code).normalized
    rw [nodeCount_normalized] at this
    exact this
  have hnodes := rawBalancedTraversalTree_nodeCount_succ_le code
  omega

/-! ## §3 The tagged-cell codec

A tagged cell is `Nat.pair 1 (Nat.pair value rest)`, so §1's constant-tag rule
applies once per cell: a decoded stream is strictly shorter than the width of
the code it came from. -/

theorem encodeTaggedList_length_succ_le (values : List ℕ) :
    values.length + 1 ≤ natBitLength (encodeTaggedList values) := by
  induction values with
  | nil => simp [encodeTaggedList, natBitLength_zero]
  | cons value rest inductionHypothesis =>
      have htag :=
        natBitLength_succ_le_natBitLength_pair_one
          (Nat.pair value (encodeTaggedList rest))
      have hinner :
          natBitLength (encodeTaggedList rest) ≤
            natBitLength (Nat.pair value (encodeTaggedList rest)) :=
        natBitLength_mono (Nat.right_le_pair value (encodeTaggedList rest))
      simp only [List.length_cons, encodeTaggedList]
      omega

/-- **The stream ledger.**  Whatever a code decodes to under the tagged codec,
its length is below the code's width. -/
theorem streamOfCode_length_succ_le (code : ℕ) :
    (BalancedClauseStreamFlattenProgram.streamOfCode code).length + 1 ≤
      natBitLength code := by
  have hwidth := one_le_natBitLength code
  unfold BalancedClauseStreamFlattenProgram.streamOfCode
  cases hdecode : decodeTaggedList code with
  | none => simpa using hwidth
  | some values =>
      have hcode : encodeTaggedList values = code :=
        encodeTaggedList_of_decode hdecode
      have hlength := encodeTaggedList_length_succ_le values
      rw [hcode] at hlength
      simpa using hlength

/-! ## §4 The atom-width ledger

The counted charges do not merely repeat once per decoded atom: the per-atom
work is itself linear in the *atom's* width.  So what the polynomial bookkeeping
needs is not the atom count alone but the **sum of the atom widths**, and that
sum is again linear in the code's width — pairing adds widths back up to one
bit per node, and §2 already caps the node count.  This is why the counted
stages on the validator's path stay at degree one in the width, not two. -/

private theorem length_flatMap_le_sum_map
    (values : List ℕ) (f : ℕ → List ℕ) (g : ℕ → ℕ)
    (hle : ∀ value, (f value).length ≤ g value) :
    (values.flatMap f).length ≤ (values.map g).sum := by
  induction values with
  | nil => simp
  | cons value rest inductionHypothesis =>
      have hhead := hle value
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons]
      omega

/-- **The atom-width ledger of the structural parser.**  The decoded atoms'
widths, plus the node count, fit inside three times the code's width. -/
theorem rawBalancedTraversalTree_atomWidth_le (code : ℕ) :
    (((rawBalancedTraversalTree code).atoms.map natBitLength).sum +
        (rawBalancedTraversalTree code).nodeCount) + 1 ≤
      3 * natBitLength code := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      rw [rawBalancedTraversalTree]
      split
      · rename_i hzero
        subst hzero
        simp [RawBalancedTraversalTree.atoms, RawBalancedTraversalTree.normalized,
          RawBalancedTraversalTree.nodeCount, natBitLength_zero]
      · rename_i hzero
        dsimp only
        split
        · have hwidth := one_le_natBitLength code
          have hatom :
              natBitLength (Nat.unpair code).2 ≤ natBitLength code :=
            natBitLength_mono (Nat.unpair_right_le code)
          simp only [RawBalancedTraversalTree.atoms,
            RawBalancedTraversalTree.normalized,
            RawBalancedTraversalTree.nodeCount, BalancedTraversalTree.atoms,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          omega
        · rename_i hleaf
          have htag : 2 ≤ (Nat.unpair code).1 :=
            two_le_of_unpair_fst_ne_zero hleaf
          have hsplit : (Nat.unpair code).1 + (Nat.unpair code).2 ≤ code :=
            Nat.unpair_add_le code
          have hpayload : (Nat.unpair code).2 < code := by omega
          have hleftLt : (Nat.unpair (Nat.unpair code).2).1 < code :=
            lt_of_le_of_lt (Nat.unpair_left_le _) hpayload
          have hrightLt : (Nat.unpair (Nat.unpair code).2).2 < code :=
            lt_of_le_of_lt (Nat.unpair_right_le _) hpayload
          have hleftBound := inductionHypothesis _ hleftLt
          have hrightBound := inductionHypothesis _ hrightLt
          have hhalves :
              natBitLength (Nat.unpair (Nat.unpair code).2).1 +
                  natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
                natBitLength (Nat.unpair code).2 + 1 := by
            have hpair :=
              natBitLength_add_le_natBitLength_pair
                (Nat.unpair (Nat.unpair code).2).1
                (Nat.unpair (Nat.unpair code).2).2
            rwa [Nat.pair_unpair] at hpair
          have houter :
              natBitLength (Nat.unpair code).1 +
                  natBitLength (Nat.unpair code).2 ≤
                natBitLength code + 1 := by
            have hpair :=
              natBitLength_add_le_natBitLength_pair (Nat.unpair code).1
                (Nat.unpair code).2
            rwa [Nat.pair_unpair] at hpair
          have htagWidth : 2 ≤ natBitLength (Nat.unpair code).1 :=
            two_le_natBitLength htag
          simp only [RawBalancedTraversalTree.atoms,
            RawBalancedTraversalTree.normalized,
            RawBalancedTraversalTree.nodeCount, BalancedTraversalTree.atoms,
            List.map_append, List.sum_append]
          simp only [RawBalancedTraversalTree.atoms] at hleftBound hrightBound
          omega

/-- **The flattened stream ledger.**  Concatenating every decoded atom of a raw
code still costs only three times the code's width. -/
theorem treeStreamValues_length_le (code : ℕ) :
    (BalancedClauseStreamFlattenProgram.treeStreamValues
        (rawBalancedTraversalTree code).normalized).length ≤
      3 * natBitLength code := by
  have hsum :=
    length_flatMap_le_sum_map (rawBalancedTraversalTree code).atoms
      BalancedClauseStreamFlattenProgram.streamOfCode natBitLength
      (fun value => by
        have := streamOfCode_length_succ_le value
        omega)
  have hwidth := rawBalancedTraversalTree_atomWidth_le code
  have hgoal :
      (BalancedClauseStreamFlattenProgram.treeStreamValues
          (rawBalancedTraversalTree code).normalized).length =
        ((rawBalancedTraversalTree code).atoms.flatMap
          BalancedClauseStreamFlattenProgram.streamOfCode).length := rfl
  rw [hgoal]
  omega

theorem natBitLength_encodeBalancedList_le (bound : ℕ) (hbound : 1 ≤ bound) :
    ∀ values : List ℕ, (∀ value ∈ values, natBitLength value ≤ bound) →
      natBitLength (encodeBalancedList values) ≤
        4 ^ balancedListHeight values * bound := by
  intro values
  induction values using encodeBalancedList.induct with
  | case1 =>
      intro _
      rw [encodeBalancedList, balancedListHeight]
      simpa [natBitLength_zero] using hbound
  | case2 value =>
      intro hvalues
      have hvalue : natBitLength value ≤ bound := hvalues value (by simp)
      have hone : natBitLength 1 ≤ bound := by
        rw [natBitLength_one]
        exact hbound
      have hpair := pairCodeBits_le 1 value
      have hmax : max (natBitLength 1) (natBitLength value) ≤ bound := by
        exact Nat.max_le.2 ⟨hone, hvalue⟩
      rw [encodeBalancedList, balancedListHeight]
      have hfour : (4 : ℕ) ^ 1 * bound = 4 * bound := by ring
      omega
  | case3 first second rest values leftLength left right ihLeft ihRight =>
      intro hvalues
      have hleftMembers : ∀ value ∈ left, natBitLength value ≤ bound :=
        fun value hvalue => hvalues value (List.mem_of_mem_take hvalue)
      have hrightMembers : ∀ value ∈ right, natBitLength value ≤ bound :=
        fun value hvalue => hvalues value (List.mem_of_mem_drop hvalue)
      have hleft := ihLeft hleftMembers
      have hright := ihRight hrightMembers
      rw [encodeBalancedList, balancedListHeight]
      set heightLeft := balancedListHeight left with hheightLeft
      set heightRight := balancedListHeight right with hheightRight
      set codeLeft := encodeBalancedList left with hcodeLeft
      set codeRight := encodeBalancedList right with hcodeRight
      have hleftPow :
          (4 : ℕ) ^ heightLeft ≤ 4 ^ max heightLeft heightRight :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hrightPow :
          (4 : ℕ) ^ heightRight ≤ 4 ^ max heightLeft heightRight :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hinner :
          natBitLength (Nat.pair codeLeft codeRight) ≤
            2 * (4 ^ max heightLeft heightRight * bound) := by
        refine (pairCodeBits_le codeLeft codeRight).trans ?_
        have hmax :
            max (natBitLength codeLeft) (natBitLength codeRight) ≤
              4 ^ max heightLeft heightRight * bound := by
          refine Nat.max_le.2 ⟨hleft.trans ?_, hright.trans ?_⟩
          · exact Nat.mul_le_mul_right _ hleftPow
          · exact Nat.mul_le_mul_right _ hrightPow
        omega
      have hpositive : 1 ≤ (4 : ℕ) ^ max heightLeft heightRight :=
        Nat.one_le_pow _ _ (by omega)
      have htwo : natBitLength 2 ≤ 2 := by
        have hlog : Nat.log 2 2 < 2 :=
          Nat.log_lt_of_lt_pow (by omega) (by norm_num)
        unfold natBitLength
        omega
      have houter :=
        pairCodeBits_le 2 (Nat.pair codeLeft codeRight)
      have hstep :
          (4 : ℕ) ^ (1 + max heightLeft heightRight) * bound =
            4 * (4 ^ max heightLeft heightRight * bound) := by
        rw [Nat.pow_add, Nat.pow_one]
        ring
      have hproduct : 1 ≤ 4 ^ max heightLeft heightRight * bound :=
        Nat.one_le_iff_ne_zero.2 (by positivity)
      omega

/-- The midpoint tree's height, spent into a quadratic in the atom count. -/
private theorem pow_balancedListHeight_le (values : List ℕ) :
    (4 : ℕ) ^ balancedListHeight values ≤ 16 * (values.length + 1) ^ 2 := by
  have hheight := balancedListHeight_le_clog values
  have hclog : (2 : ℕ) ^ Nat.clog 2 values.length ≤ 2 * (values.length + 1) := by
    rcases Nat.lt_or_ge values.length 2 with hsmall | hlarge
    · interval_cases h : values.length
      · simp
      · simp
    · have hone : 1 ≤ Nat.clog 2 values.length :=
        Nat.clog_pos (by omega) hlarge
      obtain ⟨exponent, hexponent⟩ :
          ∃ exponent, Nat.clog 2 values.length = exponent + 1 :=
        ⟨Nat.clog 2 values.length - 1, by omega⟩
      have hpred :=
        Nat.pow_pred_clog_lt_self (b := 2) (by omega) (x := values.length)
          (by omega)
      rw [hexponent] at hpred ⊢
      simp only [Nat.pred_succ] at hpred
      rw [Nat.pow_succ]
      omega
  have hpow :
      (4 : ℕ) ^ balancedListHeight values ≤
        4 ^ (Nat.clog 2 values.length + 1) :=
    Nat.pow_le_pow_right (by omega) hheight
  have hexpand :
      (4 : ℕ) ^ (Nat.clog 2 values.length + 1) =
        4 * (2 ^ Nat.clog 2 values.length * 2 ^ Nat.clog 2 values.length) := by
    rw [Nat.pow_succ]
    have hfour : (4 : ℕ) ^ Nat.clog 2 values.length =
        2 ^ Nat.clog 2 values.length * 2 ^ Nat.clog 2 values.length := by
      rw [← Nat.pow_add, show (4 : ℕ) = 2 ^ 2 from rfl, ← Nat.pow_mul]
      congr 1
      omega
    rw [hfour]
    ring
  have hsquare :
      2 ^ Nat.clog 2 values.length * 2 ^ Nat.clog 2 values.length ≤
        (2 * (values.length + 1)) * (2 * (values.length + 1)) :=
    Nat.mul_le_mul hclog hclog
  have hfinal :
      16 * (values.length + 1) ^ 2 =
        4 * ((2 * (values.length + 1)) * (2 * (values.length + 1))) := by
    ring
  omega

/-- **The re-encoding width, in the atom count and the widest atom.**  The
factor is quadratic in the count; that is what the pairing codec costs on a
midpoint tree, and it is not improvable by rebracketing the same atoms. -/
theorem natBitLength_encodeBalancedList_le_quadratic
    (values : List ℕ) (bound : ℕ) (hbound : 1 ≤ bound)
    (hvalues : ∀ value ∈ values, natBitLength value ≤ bound) :
    natBitLength (encodeBalancedList values) ≤
      16 * (values.length + 1) ^ 2 * bound := by
  refine (natBitLength_encodeBalancedList_le bound hbound values hvalues).trans
    ?_
  exact Nat.mul_le_mul_right _ (pow_balancedListHeight_le values)

/-- Height of the structural parse. -/
def rawHeight : RawBalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf _ _ => 0
  | .branch _ left right => 1 + max (rawHeight left) (rawHeight right)

theorem nodeCount_succ_le_pow_rawHeight (tree : RawBalancedTraversalTree) :
    tree.nodeCount + 1 ≤ 2 ^ (rawHeight tree + 1) := by
  induction tree with
  | empty => simp [RawBalancedTraversalTree.nodeCount, rawHeight]
  | leaf tag atom => simp [RawBalancedTraversalTree.nodeCount, rawHeight]
  | branch tag left right ihLeft ihRight =>
      have hleft :
          (2 : ℕ) ^ (rawHeight left + 1) ≤
            2 ^ (max (rawHeight left) (rawHeight right) + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hright :
          (2 : ℕ) ^ (rawHeight right + 1) ≤
            2 ^ (max (rawHeight left) (rawHeight right) + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hstep :
          (2 : ℕ) ^ (1 + max (rawHeight left) (rawHeight right) + 1) =
            2 * 2 ^ (max (rawHeight left) (rawHeight right) + 1) := by
        rw [show 1 + max (rawHeight left) (rawHeight right) + 1 =
          (max (rawHeight left) (rawHeight right) + 1) + 1 by omega,
          Nat.pow_succ]
        ring
      simp only [RawBalancedTraversalTree.nodeCount, rawHeight]
      omega

/-- **A pairing doubles the width.**  This is the multiplicative reading of §1,
and the rule the height induction runs on. -/
theorem two_mul_natBitLength_max_le_natBitLength_pair (left right : ℕ) :
    2 * natBitLength (max left right) ≤ natBitLength (Nat.pair left right) + 1 := by
  have hsquare :=
    two_mul_natBitLength_le_natBitLength_mul_self (max left right)
  have hpair :
      natBitLength (max left right * max left right) ≤
        natBitLength (Nat.pair left right) :=
    natBitLength_mono (mul_self_max_le_pair left right)
  omega

/-- **The height ledger.**  Every branch of the structural parse costs a factor
of four in the code's width. -/
theorem pow_rawHeight_le (code : ℕ) :
    rawHeight (rawBalancedTraversalTree code) = 0 ∨
      4 ^ rawHeight (rawBalancedTraversalTree code) + 2 ≤
        2 * natBitLength code := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      rw [rawBalancedTraversalTree]
      split
      · exact Or.inl rfl
      · rename_i hzero
        dsimp only
        split
        · exact Or.inl rfl
        · rename_i hleaf
          refine Or.inr ?_
          have htag : 2 ≤ (Nat.unpair code).1 :=
            two_le_of_unpair_fst_ne_zero hleaf
          have htagWidth : 2 ≤ natBitLength (Nat.unpair code).1 :=
            two_le_natBitLength htag
          have hsplit : (Nat.unpair code).1 + (Nat.unpair code).2 ≤ code :=
            Nat.unpair_add_le code
          have hpayload : (Nat.unpair code).2 < code := by omega
          have hleftLt : (Nat.unpair (Nat.unpair code).2).1 < code :=
            lt_of_le_of_lt (Nat.unpair_left_le _) hpayload
          have hrightLt : (Nat.unpair (Nat.unpair code).2).2 < code :=
            lt_of_le_of_lt (Nat.unpair_right_le _) hpayload
          have houter :
              2 *
                  natBitLength
                    (max (Nat.unpair code).1 (Nat.unpair code).2) ≤
                natBitLength code + 1 := by
            have hpair :=
              two_mul_natBitLength_max_le_natBitLength_pair (Nat.unpair code).1
                (Nat.unpair code).2
            rwa [Nat.pair_unpair] at hpair
          have hinner :
              2 *
                  natBitLength
                    (max (Nat.unpair (Nat.unpair code).2).1
                      (Nat.unpair (Nat.unpair code).2).2) ≤
                natBitLength (Nat.unpair code).2 + 1 := by
            have hpair :=
              two_mul_natBitLength_max_le_natBitLength_pair
                (Nat.unpair (Nat.unpair code).2).1
                (Nat.unpair (Nat.unpair code).2).2
            rwa [Nat.pair_unpair] at hpair
          have htagMax :
              natBitLength (Nat.unpair code).1 ≤
                natBitLength (max (Nat.unpair code).1 (Nat.unpair code).2) :=
            natBitLength_mono (le_max_left _ _)
          have hpayloadMax :
              natBitLength (Nat.unpair code).2 ≤
                natBitLength (max (Nat.unpair code).1 (Nat.unpair code).2) :=
            natBitLength_mono (le_max_right _ _)
          have hleftMax :
              natBitLength (Nat.unpair (Nat.unpair code).2).1 ≤
                natBitLength
                  (max (Nat.unpair (Nat.unpair code).2).1
                    (Nat.unpair (Nat.unpair code).2).2) :=
            natBitLength_mono (le_max_left _ _)
          have hrightMax :
              natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
                natBitLength
                  (max (Nat.unpair (Nat.unpair code).2).1
                    (Nat.unpair (Nat.unpair code).2).2) :=
            natBitLength_mono (le_max_right _ _)
          have hleftWidth := one_le_natBitLength (Nat.unpair (Nat.unpair code).2).1
          have hrightWidth :=
            one_le_natBitLength (Nat.unpair (Nat.unpair code).2).2
          simp only [rawHeight]
          rcases Nat.le_total
              (rawHeight (rawBalancedTraversalTree
                (Nat.unpair (Nat.unpair code).2).1))
              (rawHeight (rawBalancedTraversalTree
                (Nat.unpair (Nat.unpair code).2).2)) with hle | hle
          · rw [Nat.max_eq_right hle]
            rcases inductionHypothesis _ hrightLt with hzeroHeight | hbound
            · have hcollapse :
                  (4 : ℕ) ^
                      (1 + rawHeight (rawBalancedTraversalTree
                        (Nat.unpair (Nat.unpair code).2).2)) = 4 := by
                rw [hzeroHeight]
                norm_num
              rw [hcollapse]
              omega
            · have hstep :
                  (4 : ℕ) ^
                      (1 + rawHeight (rawBalancedTraversalTree
                        (Nat.unpair (Nat.unpair code).2).2)) =
                    4 * 4 ^ (rawHeight (rawBalancedTraversalTree
                      (Nat.unpair (Nat.unpair code).2).2)) := by
                rw [Nat.pow_add, Nat.pow_one]
              obtain ⟨value, hvalue⟩ :
                  ∃ value : ℕ,
                    (4 : ℕ) ^ (rawHeight (rawBalancedTraversalTree
                      (Nat.unpair (Nat.unpair code).2).2)) = value :=
                ⟨_, rfl⟩
              rw [hvalue] at hstep hbound
              rw [hstep]
              omega
          · rw [Nat.max_eq_left hle]
            rcases inductionHypothesis _ hleftLt with hzeroHeight | hbound
            · have hcollapse :
                  (4 : ℕ) ^
                      (1 + rawHeight (rawBalancedTraversalTree
                        (Nat.unpair (Nat.unpair code).2).1)) = 4 := by
                rw [hzeroHeight]
                norm_num
              rw [hcollapse]
              omega
            · have hstep :
                  (4 : ℕ) ^
                      (1 + rawHeight (rawBalancedTraversalTree
                        (Nat.unpair (Nat.unpair code).2).1)) =
                    4 * 4 ^ (rawHeight (rawBalancedTraversalTree
                      (Nat.unpair (Nat.unpair code).2).1)) := by
                rw [Nat.pow_add, Nat.pow_one]
              obtain ⟨value, hvalue⟩ :
                  ∃ value : ℕ,
                    (4 : ℕ) ^ (rawHeight (rawBalancedTraversalTree
                      (Nat.unpair (Nat.unpair code).2).1)) = value :=
                ⟨_, rfl⟩
              rw [hvalue] at hstep hbound
              rw [hstep]
              omega

/-- **The square-root node ledger.**  The decoded node count squared fits
inside eight times the code's width. -/
theorem rawBalancedTraversalTree_nodeCount_sq_le (code : ℕ) :
    ((rawBalancedTraversalTree code).nodeCount + 1) ^ 2 ≤
      8 * natBitLength code := by
  have hpow := nodeCount_succ_le_pow_rawHeight (rawBalancedTraversalTree code)
  have hsquare :
      ((rawBalancedTraversalTree code).nodeCount + 1) ^ 2 ≤
        (2 ^ (rawHeight (rawBalancedTraversalTree code) + 1)) ^ 2 :=
    Nat.pow_le_pow_left hpow 2
  have hexpand :
      ((2 : ℕ) ^ (rawHeight (rawBalancedTraversalTree code) + 1)) ^ 2 =
        4 * 4 ^ rawHeight (rawBalancedTraversalTree code) := by
    have hfour : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [hfour, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    ring
  have hwidth := one_le_natBitLength code
  rcases pow_rawHeight_le code with hzeroHeight | hbound
  · rw [hzeroHeight] at hexpand hsquare
    simp only [Nat.pow_zero, Nat.mul_one] at hexpand
    omega
  · obtain ⟨value, hvalue⟩ :
        ∃ value : ℕ,
          (4 : ℕ) ^ rawHeight (rawBalancedTraversalTree code) = value := ⟨_, rfl⟩
    rw [hvalue] at hexpand hbound
    omega

/-- The decoded atom count, squared. -/
theorem rawBalancedTraversalTree_atoms_length_sq_le (code : ℕ) :
    ((rawBalancedTraversalTree code).atoms.length + 1) ^ 2 ≤
      8 * natBitLength code := by
  have hatoms :
      (rawBalancedTraversalTree code).atoms.length ≤
        (rawBalancedTraversalTree code).nodeCount := by
    have := atoms_length_le_nodeCount (rawBalancedTraversalTree code).normalized
    rw [nodeCount_normalized] at this
    exact this
  refine le_trans ?_ (rawBalancedTraversalTree_nodeCount_sq_le code)
  exact Nat.pow_le_pow_left (by omega) 2

/-! ## §7 The re-encoding width, as a domination certificate

Spending §4, §5 and §6 together: from a *degree `d`* certificate for the raw
code's width, the canonical re-encoding of that code's decoded atoms carries a
certificate at degree `2d` — the squared atom count contributes `d` by §6, and
the widest atom contributes the other.  At the anchor degree `d = 1` supplied by
`polyBounded_witnessWidth` this is **degree two**. -/

theorem polyBounded_natBitLength_encodeBalancedList_atoms
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded
      (natBitLength (encodeBalancedList (rawBalancedTraversalTree raw).atoms))
      measure (16 * (8 * coefficient * (3 * coefficient))) (degree + degree) := by
  have hwidths := rawBalancedTraversalTree_atomWidth_le raw
  have hcount :
      PolyBounded (((rawBalancedTraversalTree raw).atoms.length + 1) ^ 2) measure
        (8 * coefficient) degree :=
    (hraw.const_mul 8).mono (rawBalancedTraversalTree_atoms_length_sq_le raw)
  have hbound :
      PolyBounded (3 * natBitLength raw) measure (3 * coefficient) degree :=
    hraw.const_mul 3
  have hmembers :
      ∀ value ∈ (rawBalancedTraversalTree raw).atoms,
        natBitLength value ≤ 3 * natBitLength raw := by
    intro value hvalue
    have hmem :
        natBitLength value ∈
          (rawBalancedTraversalTree raw).atoms.map natBitLength :=
      List.mem_map_of_mem hvalue
    have hsingle :=
      List.single_le_sum
        (l := (rawBalancedTraversalTree raw).atoms.map natBitLength)
        (fun _ _ => Nat.zero_le _) _ hmem
    omega
  have hquadratic :=
    natBitLength_encodeBalancedList_le_quadratic
      (rawBalancedTraversalTree raw).atoms (3 * natBitLength raw)
      (by have := one_le_natBitLength raw; omega) hmembers
  refine ((hcount.mul hbound).const_mul 16).mono ?_
  refine hquadratic.trans ?_
  exact le_of_eq (by ring)

end NearCubicWires.ValidatorLeafWidthCore
