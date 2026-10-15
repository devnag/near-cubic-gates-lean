import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.MvPolynomial.Eval
import Proof.Foundations.SupplierPrime

/-!
# Exact signed-score printer algebra

This module proves the local, representation-sensitive part of Appendix B:
finite binary reconstruction, signed-by-Boolean multiplication using positive
and negative bit planes, equality as two consecutive weak cuts, and the
dominance reduction.  It also connects each bit-plane call to the executable
Williams contract.  Constructing one fixed interpreter program that performs
the preprocessing, all calls, and output encoding still requires a verified
program-composition interface; no uncharged semantic runner is introduced
here.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierPrinter

open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdCompiler

/-! ## Exact signed binary slicing -/

theorem ofBits_eq_sum {width : ℕ} (bits : Fin width → Bool) :
    Nat.ofBits bits =
      ∑ bit : Fin width, if bits bit then 2 ^ bit.val else 0 := by
  simpa only [encodeBitInput] using
    (NearCubicWires.encodeBitInput_eq_ofBits bits).symm

theorem testBit_sum_eq {value width : ℕ} (hvalue : value < 2 ^ width) :
    (∑ bit : Fin width, if value.testBit bit.val then 2 ^ bit.val else 0) =
      value := by
  simpa only [encodeBitInput] using
    NearCubicWires.encodeBitInput_testBit hvalue

theorem testBit_toNat_sum_eq {value width : ℕ}
    (hvalue : value < 2 ^ width) :
    (∑ bit : Fin width, (value.testBit bit.val).toNat * 2 ^ bit.val) =
      value := by
  calc
    (∑ bit : Fin width, (value.testBit bit.val).toNat * 2 ^ bit.val) =
        ∑ bit : Fin width,
          if value.testBit bit.val then 2 ^ bit.val else 0 := by
      apply Finset.sum_congr rfl
      intro bit _
      cases value.testBit bit.val <;> simp
    _ = value := testBit_sum_eq hvalue

def positiveMagnitudeBit (value : ℤ) (bit : ℕ) : Bool :=
  if 0 ≤ value then value.natAbs.testBit bit else false

def negativeMagnitudeBit (value : ℤ) (bit : ℕ) : Bool :=
  if value < 0 then value.natAbs.testBit bit else false

theorem signed_binary_reconstruction {value : ℤ} {width : ℕ}
    (hvalue : value.natAbs < 2 ^ width) :
    value =
      ((∑ bit : Fin width,
        (positiveMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) -
      ((∑ bit : Fin width,
        (negativeMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) := by
  by_cases hnonnegative : 0 ≤ value
  · have hsum := testBit_toNat_sum_eq hvalue
    simp [positiveMagnitudeBit, negativeMagnitudeBit, hnonnegative,
      not_lt.mpr hnonnegative, hsum, Int.natAbs_of_nonneg hnonnegative]
  · have hnegative : value < 0 := lt_of_not_ge hnonnegative
    have hsum := testBit_toNat_sum_eq hvalue
    simp [positiveMagnitudeBit, negativeMagnitudeBit, hnegative,
      hnonnegative, hsum]
    simp [abs_of_neg hnegative]

theorem signed_binary_reconstruction_sum {value : ℤ} {width : ℕ}
    (hvalue : value.natAbs < 2 ^ width) :
    value = ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
      (((positiveMagnitudeBit value bit.val).toNat : ℤ) -
        ((negativeMagnitudeBit value bit.val).toNat : ℤ)) := by
  calc
    value =
        ((∑ bit : Fin width,
          (positiveMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) -
        ((∑ bit : Fin width,
          (negativeMagnitudeBit value bit.val).toNat * 2 ^ bit.val : ℕ) : ℤ) :=
      signed_binary_reconstruction hvalue
    _ = ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
        (((positiveMagnitudeBit value bit.val).toNat : ℤ) -
          ((negativeMagnitudeBit value bit.val).toNat : ℤ)) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro bit _
      ring

/-! ## Signed-by-Boolean matrix multiplication -/

abbrev IntMatrix (rows columns : ℕ) :=
  Fin rows → Fin columns → ℤ

def signedBooleanProduct {rows inner columns : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns) :
    IntMatrix rows columns :=
  fun row column =>
    ∑ index, left row index * (right index column).toNat

def positiveBitPlane {rows columns : ℕ}
    (matrix : IntMatrix rows columns) (bit : ℕ) :
    BitMatrix rows columns :=
  fun row column => positiveMagnitudeBit (matrix row column) bit

def negativeBitPlane {rows columns : ℕ}
    (matrix : IntMatrix rows columns) (bit : ℕ) :
    BitMatrix rows columns :=
  fun row column => negativeMagnitudeBit (matrix row column) bit

def recombinedSignedProduct {rows inner columns width : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns) :
    IntMatrix rows columns :=
  fun row column =>
    ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
      (((integerMatrixProduct (positiveBitPlane left bit.val) right
          row column : ℕ) : ℤ) -
        ((integerMatrixProduct (negativeBitPlane left bit.val) right
          row column : ℕ) : ℤ))

theorem integerMatrixProduct_cast {rows inner columns : ℕ}
    (left : BitMatrix rows inner) (right : BitMatrix inner columns)
    (row : Fin rows) (column : Fin columns) :
    ((integerMatrixProduct left right row column : ℕ) : ℤ) =
      ∑ index,
        ((left row index).toNat : ℤ) *
          ((right index column).toNat : ℤ) := by
  rw [integerMatrixProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  cases left row index <;> cases right index column <;> rfl

theorem recombinedSignedProduct_eq {rows inner columns width : ℕ}
    (left : IntMatrix rows inner) (right : BitMatrix inner columns)
    (hmagnitude : ∀ row index, (left row index).natAbs < 2 ^ width) :
    recombinedSignedProduct (width := width) left right =
      signedBooleanProduct left right := by
  funext row column
  simp only [recombinedSignedProduct, signedBooleanProduct]
  simp_rw [integerMatrixProduct_cast]
  simp only [positiveBitPlane, negativeBitPlane]
  calc
    (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
        ((∑ index,
          ((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) *
            ((right index column).toNat : ℤ)) -
        ∑ index,
          ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ) *
            ((right index column).toNat : ℤ))) =
      ∑ bit : Fin width, ∑ index : Fin inner,
        (2 ^ bit.val : ℤ) *
          ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
            ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
            ((right index column).toNat : ℤ)) := by
      apply Finset.sum_congr rfl
      intro bit _
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = ∑ index : Fin inner, ∑ bit : Fin width,
        (2 ^ bit.val : ℤ) *
          ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
            ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
            ((right index column).toNat : ℤ)) := Finset.sum_comm
    _ = ∑ index, left row index * (right index column).toNat := by
      apply Finset.sum_congr rfl
      intro index _
      have hreconstruction :=
        signed_binary_reconstruction_sum (hmagnitude row index)
      calc
        (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
            ((((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
              ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ)) *
              ((right index column).toNat : ℤ))) =
            (∑ bit : Fin width, (2 ^ bit.val : ℤ) *
              (((positiveMagnitudeBit (left row index) bit.val).toNat : ℤ) -
                ((negativeMagnitudeBit (left row index) bit.val).toNat : ℤ))) *
              ((right index column).toNat : ℤ) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bit _
          ring
        _ = left row index * (right index column).toNat :=
          congrArg
            (fun value : ℤ =>
              value * ((right index column).toNat : ℤ))
            hreconstruction.symm

/-! ## Connection to the executable rectangular-product contract -/

def algorithmRecombinedSignedProduct
    (algorithm : ExecutableRectangularProductAlgorithm)
    (U width : ℕ)
    (left : IntMatrix U (rectangularInnerDimension U))
    (right : BitMatrix (rectangularInnerDimension U) U) :
    IntMatrix U U :=
  fun row column =>
    ∑ bit : Fin width, (2 ^ bit.val : ℤ) *
      (((algorithm.compute U (positiveBitPlane left bit.val) right
          row column : ℕ) : ℤ) -
        ((algorithm.compute U (negativeBitPlane left bit.val) right
          row column : ℕ) : ℤ))

theorem algorithmRecombinedSignedProduct_eq
    (algorithm : ExecutableRectangularProductAlgorithm)
    (onset U width : ℕ) (hU : onset ≤ U)
    (hcorrect : ∀ request : RectangularProductRequest,
      onset ≤ request.dimension →
        algorithm.compute request.dimension request.left request.right =
          integerMatrixProduct request.left request.right)
    (left : IntMatrix U (rectangularInnerDimension U))
    (right : BitMatrix (rectangularInnerDimension U) U)
    (hmagnitude : ∀ row index, (left row index).natAbs < 2 ^ width) :
    algorithmRecombinedSignedProduct algorithm U width left right =
      signedBooleanProduct left right := by
  have hpositive (bit : Fin width) :
      algorithm.compute U (positiveBitPlane left bit.val) right =
        integerMatrixProduct (positiveBitPlane left bit.val) right := by
    exact hcorrect
      (⟨U, positiveBitPlane left bit.val, right⟩ :
        RectangularProductRequest) hU
  have hnegative (bit : Fin width) :
      algorithm.compute U (negativeBitPlane left bit.val) right =
        integerMatrixProduct (negativeBitPlane left bit.val) right := by
    exact hcorrect
      (⟨U, negativeBitPlane left bit.val, right⟩ :
        RectangularProductRequest) hU
  funext row column
  simp only [algorithmRecombinedSignedProduct]
  simp_rw [hpositive, hnegative]
  exact congrFun (congrFun
    (recombinedSignedProduct_eq left right hmagnitude) row) column

def signedPlaneSteps
    (algorithm : ExecutableRectangularProductAlgorithm)
    (U width : ℕ)
    (left : IntMatrix U (rectangularInnerDimension U))
    (right : BitMatrix (rectangularInnerDimension U) U) : ℕ :=
  ∑ bit : Fin width,
    (algorithm.runner.budget
        (⟨U, positiveBitPlane left bit.val, right⟩ :
          RectangularProductRequest) +
      algorithm.runner.budget
        (⟨U, negativeBitPlane left bit.val, right⟩ :
          RectangularProductRequest))

theorem signedPlaneSteps_le
    (algorithm : ExecutableRectangularProductAlgorithm)
    (onset coefficient logExponent U width : ℕ) (hU : onset ≤ U)
    (hbudget : ∀ request : RectangularProductRequest,
      onset ≤ request.dimension →
        algorithm.runner.budget request ≤
          coefficient * request.dimension ^ 2 *
            logScale request.dimension ^ logExponent)
    (left : IntMatrix U (rectangularInnerDimension U))
    (right : BitMatrix (rectangularInnerDimension U) U) :
    signedPlaneSteps algorithm U width left right ≤
      width * (2 * (coefficient * U ^ 2 *
        logScale U ^ logExponent)) := by
  unfold signedPlaneSteps
  calc
    (∑ bit : Fin width,
      (algorithm.runner.budget
          (⟨U, positiveBitPlane left bit.val, right⟩ :
            RectangularProductRequest) +
        algorithm.runner.budget
          (⟨U, negativeBitPlane left bit.val, right⟩ :
            RectangularProductRequest))) ≤
        ∑ _bit : Fin width,
          ((coefficient * U ^ 2 * logScale U ^ logExponent) +
            (coefficient * U ^ 2 * logScale U ^ logExponent)) := by
      apply Finset.sum_le_sum
      intro bit _
      exact Nat.add_le_add
        (hbudget
          (⟨U, positiveBitPlane left bit.val, right⟩ :
            RectangularProductRequest) hU)
        (hbudget
          (⟨U, negativeBitPlane left bit.val, right⟩ :
            RectangularProductRequest) hU)
    _ = width * (2 * (coefficient * U ^ 2 *
        logScale U ^ logExponent)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

theorem executableRectangularProduct_supplies_signedSlices
    (contract : ExecutableBooleanRectangularProductContract) :
    ∃ algorithm : ExecutableRectangularProductAlgorithm,
      OracleFree algorithm.runner.program ∧
      ∃ onset coefficient logExponent : ℕ, 0 < coefficient ∧
        ∀ (U width : ℕ), onset ≤ U →
          ∀ (left : IntMatrix U (rectangularInnerDimension U))
            (right : BitMatrix (rectangularInnerDimension U) U),
            (∀ row index, (left row index).natAbs < 2 ^ width) →
            algorithmRecombinedSignedProduct algorithm U width left right =
              signedBooleanProduct left right ∧
            signedPlaneSteps algorithm U width left right ≤
              width * (2 * (coefficient * U ^ 2 *
                logScale U ^ logExponent)) := by
  rcases contract with
    ⟨algorithm, onset, coefficient, logExponent, hcoefficient, hcontract⟩
  refine ⟨algorithm, algorithm.oracleFree, onset, coefficient, logExponent,
    hcoefficient, ?_⟩
  intro U width hU left right hmagnitude
  refine ⟨algorithmRecombinedSignedProduct_eq algorithm onset U width hU
    (fun request hrequest => (hcontract request hrequest).1)
    left right hmagnitude, ?_⟩
  exact signedPlaneSteps_le algorithm onset coefficient logExponent
    U width hU (fun request hrequest => (hcontract request hrequest).2)
    left right

/-! ## Equality cuts and weighted dominance -/

def weakCut (threshold score : ℤ) : Bool :=
  decide (threshold ≤ score)

def exactCut (threshold score : ℤ) : Bool :=
  decide (threshold = score)

theorem exactCut_eq_successiveCuts (threshold score : ℤ) :
    ((exactCut threshold score).toNat : ℤ) =
      (weakCut threshold score).toNat -
        (weakCut (threshold + 1) score).toNat := by
  unfold exactCut weakCut
  by_cases hequal : threshold = score
  · subst score
    simp
  · by_cases hbelow : score < threshold
    · have hnotThreshold : ¬threshold ≤ score := by omega
      have hnotSuccessor : ¬threshold + 1 ≤ score := by omega
      simp [hequal, hnotThreshold, hnotSuccessor]
    · have habove : threshold + 1 ≤ score := by omega
      have hthreshold : threshold ≤ score := by omega
      simp [hequal, hthreshold, habove]

theorem threshold_split_as_dominance
    (threshold leftScore rightScore : ℤ) :
    weakCut threshold (leftScore + rightScore) =
      decide (threshold - leftScore ≤ rightScore) := by
  unfold weakCut
  by_cases hleft : threshold ≤ leftScore + rightScore
  · have hright : threshold - leftScore ≤ rightScore := by omega
    simp [hleft, hright]
  · have hright : ¬threshold - leftScore ≤ rightScore := by omega
    simp [hleft, hright]

def weightedDominance {Rows Gates Columns : ℕ}
    (left : IntMatrix Rows Gates) (right : IntMatrix Gates Columns)
    (weight : Fin Gates → ℤ) : IntMatrix Rows Columns :=
  fun row column =>
    ∑ gate, weight gate *
      ((decide (left row gate ≤ right gate column) : Bool).toNat : ℤ)

def weightedThresholdScore {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (threshold weight : Fin Gates → ℤ) : IntMatrix Rows Columns :=
  fun row column =>
    ∑ gate, weight gate *
      ((weakCut (threshold gate)
        (leftScore row gate + rightScore gate column)).toNat : ℤ)

def weightedExactScore {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (target weight : Fin Gates → ℤ) : IntMatrix Rows Columns :=
  fun row column =>
    ∑ gate, weight gate *
      ((exactCut (target gate)
        (leftScore row gate + rightScore gate column)).toNat : ℤ)

theorem weightedExactScore_eq_successiveThresholdScores
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (target weight : Fin Gates → ℤ) :
    weightedExactScore leftScore rightScore target weight =
      fun row column =>
        weightedThresholdScore leftScore rightScore target weight row column -
          weightedThresholdScore leftScore rightScore
            (fun gate => target gate + 1) weight row column := by
  funext row column
  unfold weightedExactScore weightedThresholdScore
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro gate _
  rw [exactCut_eq_successiveCuts]
  ring

theorem weightedThresholdScore_eq_dominance
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (threshold weight : Fin Gates → ℤ) :
    weightedThresholdScore leftScore rightScore threshold weight =
      weightedDominance
        (fun row gate => threshold gate - leftScore row gate)
        rightScore weight := by
  funext row column
  apply Finset.sum_congr rfl
  intro gate _
  rw [threshold_split_as_dominance]

/-- Every signed exact-equation table is the difference of two weighted
dominance tables, so the same Boolean rectangular-product backend prints both
cuts. -/
theorem weightedExactScore_eq_successiveDominance
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (target weight : Fin Gates → ℤ) :
    weightedExactScore leftScore rightScore target weight =
      fun row column =>
        weightedDominance
            (fun row gate => target gate - leftScore row gate)
            rightScore weight row column -
          weightedDominance
            (fun row gate => target gate + 1 - leftScore row gate)
            rightScore weight row column := by
  rw [weightedExactScore_eq_successiveThresholdScores,
    weightedThresholdScore_eq_dominance,
    weightedThresholdScore_eq_dominance]

/-! ## Exact same-bucket/cross-bucket dominance split -/

/-- Semantic certificate produced by a stable joint sort.  Left copies precede
right copies on ties, so cross-bucket comparisons are strict in bucket index
and only same-bucket pairs require a local scan. -/
structure BucketedDominanceLayout
    (Rows Gates Columns : Type) [Fintype Gates] (Buckets : ℕ) where
  leftScore : Rows → Gates → ℤ
  rightScore : Gates → Columns → ℤ
  leftBucket : Rows → Gates → Fin Buckets
  rightBucket : Gates → Columns → Fin Buckets
  comparison : ∀ row gate column,
    leftScore row gate ≤ rightScore gate column ↔
      leftBucket row gate < rightBucket gate column ∨
        (leftBucket row gate = rightBucket gate column ∧
          leftScore row gate ≤ rightScore gate column)

/-! ### Canonical stable joint-sort layout -/

/-- A stable-sort occurrence is either one left row or one right column.  The
sum-to-fin equivalence supplies the final deterministic tie breaker, after the
mandatory left-before-right tag used by the dominance reduction. -/
abbrev StableDominanceCopy (Rows Columns : ℕ) :=
  Fin Rows ⊕ Fin Columns

def stableDominanceCopyId {Rows Columns : ℕ} :
    StableDominanceCopy Rows Columns → Fin (Rows + Columns) :=
  finSumFinEquiv

def stableDominanceCopyScore {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    StableDominanceCopy Rows Columns → ℤ
  | .inl row => leftScore row gate
  | .inr column => rightScore gate column

/-- Lexicographic sort key.  The occurrence id makes all keys distinct, while
`Fin.castAdd` places every left copy before every right copy on an exact tie. -/
def stableDominanceKey {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    ℤ ×ₗ Fin (Rows + Columns) :=
  toLex (stableDominanceCopyScore leftScore rightScore gate copy,
    stableDominanceCopyId copy)

theorem stableDominanceKey_injective {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    Function.Injective (stableDominanceKey leftScore rightScore gate) := by
  intro left right hequal
  have hid :
      stableDominanceCopyId left = stableDominanceCopyId right :=
    congrArg (fun key : ℤ ×ₗ Fin (Rows + Columns) => (ofLex key).2)
      hequal
  exact finSumFinEquiv.injective hid

def stableDominanceKeys {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) : Finset (ℤ ×ₗ Fin (Rows + Columns)) :=
  Finset.univ.image (stableDominanceKey leftScore rightScore gate)

theorem stableDominanceKeys_card {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    (stableDominanceKeys leftScore rightScore gate).card =
      Rows + Columns := by
  rw [stableDominanceKeys,
    Finset.card_image_of_injective _
      (stableDominanceKey_injective leftScore rightScore gate)]
  simp

def stableDominanceKeyMember {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    stableDominanceKeys leftScore rightScore gate :=
  ⟨stableDominanceKey leftScore rightScore gate copy, by
    simp [stableDominanceKeys]⟩

/-- Zero-based position of an occurrence in the stable joint sort.  Defining
the rank through Mathlib's finite order isomorphism makes uniqueness and total
ordering part of the construction instead of an extra layout hypothesis. -/
def stableDominanceRank {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (copy : StableDominanceCopy Rows Columns) :
    Fin (Rows + Columns) :=
  ((stableDominanceKeys leftScore rightScore gate).orderIsoOfFin
    (stableDominanceKeys_card leftScore rightScore gate)).symm
      (stableDominanceKeyMember leftScore rightScore gate copy)

theorem stableDominanceRank_lt_iff_key_lt {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (left right : StableDominanceCopy Rows Columns) :
    stableDominanceRank leftScore rightScore gate left <
        stableDominanceRank leftScore rightScore gate right ↔
      stableDominanceKey leftScore rightScore gate left <
        stableDominanceKey leftScore rightScore gate right := by
  let keys := stableDominanceKeys leftScore rightScore gate
  let cardProof : keys.card = Rows + Columns :=
    stableDominanceKeys_card leftScore rightScore gate
  let order := keys.orderIsoOfFin cardProof
  change order.symm
        (stableDominanceKeyMember leftScore rightScore gate left) <
      order.symm
        (stableDominanceKeyMember leftScore rightScore gate right) ↔ _
  rw [order.symm.lt_iff_lt]
  rfl

theorem stableDominanceKey_left_lt_right_iff {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (row : Fin Rows) (gate : Fin Gates) (column : Fin Columns) :
    stableDominanceKey leftScore rightScore gate (.inl row) <
        stableDominanceKey leftScore rightScore gate (.inr column) ↔
      leftScore row gate ≤ rightScore gate column := by
  unfold stableDominanceKey stableDominanceCopyScore
    stableDominanceCopyId
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hscore | ⟨hscore, _⟩)
    · exact le_of_lt hscore
    · exact le_of_eq hscore
  · intro hscore
    by_cases hstrict : leftScore row gate < rightScore gate column
    · exact Or.inl hstrict
    · refine Or.inr ⟨le_antisymm hscore (le_of_not_gt hstrict), ?_⟩
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      change row.val < Rows + column.val
      omega

theorem stableDominanceRank_left_lt_right_iff
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (row : Fin Rows) (gate : Fin Gates) (column : Fin Columns) :
    stableDominanceRank leftScore rightScore gate (.inl row) <
        stableDominanceRank leftScore rightScore gate (.inr column) ↔
      leftScore row gate ≤ rightScore gate column := by
  rw [stableDominanceRank_lt_iff_key_lt,
    stableDominanceKey_left_lt_right_iff]

theorem stableDominanceRank_injective {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    Function.Injective
      (stableDominanceRank leftScore rightScore gate) := by
  intro left right hrank
  apply stableDominanceKey_injective leftScore rightScore gate
  let keys := stableDominanceKeys leftScore rightScore gate
  let cardProof : keys.card = Rows + Columns :=
    stableDominanceKeys_card leftScore rightScore gate
  let order := keys.orderIsoOfFin cardProof
  have hmember :
      stableDominanceKeyMember leftScore rightScore gate left =
        stableDominanceKeyMember leftScore rightScore gate right := by
    exact order.symm.injective hrank
  exact congrArg Subtype.val hmember

/-- Number of blocks in the stable sort.  `bucketSize + 1` keeps the
construction total; callers pass the desired positive block width minus one. -/
def stableDominanceBucketCount
    (Rows Columns bucketSize : ℕ) : ℕ :=
  (Rows + Columns) / (bucketSize + 1) + 1

/-- Number of stable buckets that the rectangular backend can carry once one
gate coordinate is included.  The zero-gate case is kept total. -/
def stableCapacityBucketBudget (capacity gates : ℕ) : ℕ :=
  if gates = 0 then 1 else capacity / gates

/-- Canonical block size selected from the backend capacity.  When there is
only room for one bucket it uses the whole joint list; otherwise division by
`budget - 1` leaves one full bucket of rounding slack. -/
def stableCapacityBucketSize
    (Rows Columns capacity gates : ℕ) : ℕ :=
  let budget := stableCapacityBucketBudget capacity gates
  if budget ≤ 1 then Rows + Columns
  else (Rows + Columns) / (budget - 1)

theorem stableCapacityBucketCount_le_budget
    (Rows Columns capacity gates : ℕ)
    (_hgates : 0 < gates)
    (hbudget : 1 < stableCapacityBucketBudget capacity gates) :
    stableDominanceBucketCount Rows Columns
        (stableCapacityBucketSize Rows Columns capacity gates) ≤
      stableCapacityBucketBudget capacity gates := by
  let entries := Rows + Columns
  let budget := stableCapacityBucketBudget capacity gates
  have hdivisor : 0 < budget - 1 := Nat.sub_pos_of_lt hbudget
  have hwidth : 0 < entries / (budget - 1) + 1 := Nat.succ_pos _
  have hentries :
      entries < (budget - 1) * (entries / (budget - 1) + 1) :=
    Nat.lt_mul_div_succ entries hdivisor
  have hquotient :
      entries / (entries / (budget - 1) + 1) < budget - 1 := by
    exact (Nat.div_lt_iff_lt_mul hwidth).2 hentries
  unfold stableDominanceBucketCount stableCapacityBucketSize
  change
    entries /
          ((if budget ≤ 1 then entries else entries / (budget - 1)) + 1) +
        1 ≤
      budget
  rw [if_neg (not_le_of_gt hbudget)]
  omega

/-- The canonical stable layout always fits when the number of gate
coordinates squared fits the rectangular inner dimension.  This is the exact
finite form of the printer's strict exponent inequality. -/
theorem stableCapacityBucketDimension_le
    (Rows Columns capacity gates : ℕ)
    (hgateSquare : gates * gates ≤ capacity) :
    gates *
        stableDominanceBucketCount Rows Columns
          (stableCapacityBucketSize Rows Columns capacity gates) ≤
      capacity := by
  by_cases hgatesZero : gates = 0
  · simp [hgatesZero]
  have hgates : 0 < gates := Nat.pos_of_ne_zero hgatesZero
  let budget := stableCapacityBucketBudget capacity gates
  have hbudgetEq : budget = capacity / gates := by
    simp [budget, stableCapacityBucketBudget, hgatesZero]
  have hgatesLeBudget : gates ≤ budget := by
    rw [hbudgetEq]
    exact (Nat.le_div_iff_mul_le hgates).2 hgateSquare
  have hgateBudget : gates * budget ≤ capacity := by
    rw [hbudgetEq, Nat.mul_comm]
    exact Nat.div_mul_le_self capacity gates
  by_cases hbudgetLarge : 1 < budget
  · calc
      gates *
          stableDominanceBucketCount Rows Columns
            (stableCapacityBucketSize Rows Columns capacity gates) ≤
          gates * budget := by
            exact Nat.mul_le_mul_left gates
              (stableCapacityBucketCount_le_budget Rows Columns capacity gates
                hgates (by simpa [budget] using hbudgetLarge))
      _ ≤ capacity := hgateBudget
  · have hbudgetSmall : budget ≤ 1 := Nat.le_of_not_gt hbudgetLarge
    have hgatesEq : gates = 1 := by omega
    have hbudgetOne : budget = 1 := by omega
    subst gates
    have hcapacityEq : capacity = 1 := by
      change stableCapacityBucketBudget capacity 1 = 1 at hbudgetOne
      simpa [stableCapacityBucketBudget] using hbudgetOne
    subst capacity
    unfold stableDominanceBucketCount stableCapacityBucketSize
    simp only [stableCapacityBucketBudget, one_ne_zero, if_false,
      Nat.div_one, one_mul]
    rw [if_pos le_rfl]
    have hentries :
        Rows + Columns < Rows + Columns + 1 := Nat.lt_succ_self _
    rw [Nat.div_eq_of_lt hentries]

def stableDominanceBucket {Rows Columns bucketSize : ℕ}
    (rank : Fin (Rows + Columns)) :
    Fin (stableDominanceBucketCount Rows Columns bucketSize) :=
  ⟨rank.val / (bucketSize + 1), by
    unfold stableDominanceBucketCount
    have hrank : rank.val ≤ Rows + Columns := Nat.le_of_lt rank.isLt
    have hdiv :
        rank.val / (bucketSize + 1) ≤
          (Rows + Columns) / (bucketSize + 1) :=
      Nat.div_le_div_right hrank
    omega⟩

theorem stableDominanceBucket_lt_implies_rank_lt
    {Rows Columns bucketSize : ℕ}
    {left right : Fin (Rows + Columns)}
    (hbucket :
      stableDominanceBucket (bucketSize := bucketSize) left <
        stableDominanceBucket (bucketSize := bucketSize) right) :
    left < right := by
  by_contra hnot
  have hrank : right.val ≤ left.val := by
    exact le_of_not_gt hnot
  have hdiv :
      right.val / (bucketSize + 1) ≤
        left.val / (bucketSize + 1) :=
    Nat.div_le_div_right hrank
  exact (not_lt_of_ge hdiv) hbucket

theorem stableDominanceRank_lt_implies_bucket_le
    {Rows Columns bucketSize : ℕ}
    {left right : Fin (Rows + Columns)}
    (hrank : left < right) :
    stableDominanceBucket (bucketSize := bucketSize) left ≤
      stableDominanceBucket (bucketSize := bucketSize) right := by
  exact Nat.div_le_div_right (Nat.le_of_lt hrank)

/-- The production stable joint-sort constructor.  Bucketing is performed on
unique sorted occurrences, so equal scores retain the required left/right
ordering without assuming distinct weights or distinct rows. -/
def stableBucketedDominanceLayout {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (bucketSize : ℕ) :
    BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns)
      (stableDominanceBucketCount Rows Columns bucketSize) where
  leftScore := leftScore
  rightScore := rightScore
  leftBucket := fun row gate =>
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate (.inl row))
  rightBucket := fun gate column =>
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate (.inr column))
  comparison := by
    intro row gate column
    have hrank :
        stableDominanceRank leftScore rightScore gate (.inl row) <
            stableDominanceRank leftScore rightScore gate (.inr column) ↔
          leftScore row gate ≤ rightScore gate column :=
      stableDominanceRank_left_lt_right_iff
        leftScore rightScore row gate column
    constructor
    · intro hscore
      have hrankLt := hrank.mpr hscore
      have hbucketLe :=
        stableDominanceRank_lt_implies_bucket_le
          (bucketSize := bucketSize) hrankLt
      rcases hbucketLe.lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, hscore⟩
    · rintro (hbucket | ⟨_, hscore⟩)
      · exact hrank.mp
          (stableDominanceBucket_lt_implies_rank_lt hbucket)
      · exact hscore

/-- Occurrences assigned to one stable-sort block for one gate. -/
def stableDominanceBucketCopies {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates)
    (bucket : Fin
      (stableDominanceBucketCount Rows Columns bucketSize)) :
    Finset (StableDominanceCopy Rows Columns) :=
  Finset.univ.filter fun copy =>
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate copy) = bucket

/-- Every block contains at most its declared width.  This is the quantitative
fact that rules out a one-bucket semantic fallback: the local scan is bounded
because stable ranks are unique, even when many scores are equal. -/
theorem stableDominanceBucketCopies_card_le
    {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates)
    (bucket : Fin
      (stableDominanceBucketCount Rows Columns bucketSize)) :
    (stableDominanceBucketCopies leftScore rightScore gate bucket).card ≤
      bucketSize + 1 := by
  let width := bucketSize + 1
  let rankValue : StableDominanceCopy Rows Columns → ℕ :=
    fun copy =>
      (stableDominanceRank leftScore rightScore gate copy).val
  have hrankInjective : Function.Injective rankValue := by
    intro left right hequal
    apply stableDominanceRank_injective leftScore rightScore gate
    exact Fin.ext hequal
  have hsubset :
      (stableDominanceBucketCopies leftScore rightScore gate bucket).image
          rankValue ⊆
        Finset.Ico (bucket.val * width) ((bucket.val + 1) * width) := by
    intro rank hrank
    rcases Finset.mem_image.mp hrank with ⟨copy, hcopy, rfl⟩
    have hbucket := (Finset.mem_filter.mp hcopy).2
    have hquotient :
        rankValue copy / width = bucket.val := by
      exact congrArg Fin.val hbucket
    have hwidth : 0 < width := by
      simp [width]
    have hlower : bucket.val * width ≤ rankValue copy := by
      apply (Nat.le_div_iff_mul_le hwidth).mp
      exact le_of_eq hquotient.symm
    have hupper : rankValue copy < (bucket.val + 1) * width := by
      apply (Nat.div_lt_iff_lt_mul hwidth).mp
      omega
    exact Finset.mem_Ico.mpr ⟨hlower, hupper⟩
  calc
    (stableDominanceBucketCopies
        leftScore rightScore gate bucket).card =
        ((stableDominanceBucketCopies
          leftScore rightScore gate bucket).image rankValue).card :=
      (Finset.card_image_of_injective _ hrankInjective).symm
    _ ≤ (Finset.Ico (bucket.val * width)
        ((bucket.val + 1) * width)).card :=
      Finset.card_le_card hsubset
    _ = bucketSize + 1 := by
      rw [Nat.card_Ico]
      dsimp [width]
      rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- Right occurrences sharing the canonical block of one left occurrence. -/
def stableSameBucketColumns {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (row : Fin Rows) :
    Finset (Fin Columns) :=
  Finset.univ.filter fun column =>
    stableDominanceBucket (bucketSize := bucketSize)
        (stableDominanceRank leftScore rightScore gate (.inl row)) =
      stableDominanceBucket (bucketSize := bucketSize)
        (stableDominanceRank leftScore rightScore gate (.inr column))

theorem stableSameBucketColumns_card_le
    {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) (row : Fin Rows) :
    (stableSameBucketColumns
      (bucketSize := bucketSize) leftScore rightScore gate row).card ≤
        bucketSize + 1 := by
  let bucket :=
    stableDominanceBucket (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate (.inl row))
  have hinject :
      (stableSameBucketColumns
          (bucketSize := bucketSize)
          leftScore rightScore gate row).card ≤
        (stableDominanceBucketCopies
          leftScore rightScore gate bucket).card := by
    apply Finset.card_le_card_of_injOn Sum.inr
    · intro column hcolumn
      have hsame := (Finset.mem_filter.mp hcolumn).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact hsame.symm
    · exact Sum.inr_injective.injOn
  exact hinject.trans
    (stableDominanceBucketCopies_card_le
      leftScore rightScore gate bucket)

/-- Exact number of same-block row/column comparisons for one gate. -/
def stableSameBucketPairCount {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) : ℕ :=
  ∑ row, (stableSameBucketColumns
    (bucketSize := bucketSize) leftScore rightScore gate row).card

/-- The stable local scan is linear in the number of left copies times the
declared block width, independently of score multiplicities. -/
theorem stableSameBucketPairCount_le
    {Rows Gates Columns bucketSize : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (gate : Fin Gates) :
    stableSameBucketPairCount
        (bucketSize := bucketSize) leftScore rightScore gate ≤
      Rows * (bucketSize + 1) := by
  unfold stableSameBucketPairCount
  calc
    (∑ row : Fin Rows,
        (stableSameBucketColumns
          (bucketSize := bucketSize)
          leftScore rightScore gate row).card) ≤
        ∑ _row : Fin Rows, (bucketSize + 1) := by
      apply Finset.sum_le_sum
      intro row _
      exact stableSameBucketColumns_card_le
        leftScore rightScore gate row
    _ = Rows * (bucketSize + 1) := by simp

def bucketedWeightedDominance
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, weight gate *
    ((decide
      (layout.leftScore row gate ≤ layout.rightScore gate column) :
        Bool).toNat : ℤ)

def sameBucketContribution
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, if
      layout.leftBucket row gate = layout.rightBucket gate column ∧
        layout.leftScore row gate ≤ layout.rightScore gate column
    then weight gate else 0

def laterBucketContribution
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) : ℤ :=
  ∑ gate, if
      layout.leftBucket row gate < layout.rightBucket gate column
    then weight gate else 0

/-- Equation (B.3) is exactly the sum of the local scan and the rectangular
cross-bucket product; ties are wholly contained in the local term. -/
theorem bucketedWeightedDominance_eq_same_add_later
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) :
    bucketedWeightedDominance layout weight row column =
      sameBucketContribution layout weight row column +
        laterBucketContribution layout weight row column := by
  unfold bucketedWeightedDominance sameBucketContribution
    laterBucketContribution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro gate _
  by_cases hlater :
      layout.leftBucket row gate < layout.rightBucket gate column
  · have hcomparison :
        layout.leftScore row gate ≤ layout.rightScore gate column :=
      (layout.comparison row gate column).2 (Or.inl hlater)
    have hne :
        layout.leftBucket row gate ≠ layout.rightBucket gate column :=
      ne_of_lt hlater
    simp [hlater, hcomparison, hne]
  · by_cases hsame :
      layout.leftBucket row gate = layout.rightBucket gate column ∧
        layout.leftScore row gate ≤ layout.rightScore gate column
    · have hcomparison :
          layout.leftScore row gate ≤ layout.rightScore gate column :=
        (layout.comparison row gate column).2 (Or.inr hsame)
      simp [hsame]
    · have hcomparison :
          ¬layout.leftScore row gate ≤ layout.rightScore gate column := by
        intro hcomparison
        rcases (layout.comparison row gate column).1 hcomparison with
          hcross | hlocal
        · exact hlater hcross
        · exact hsame hlocal
      simp [hlater, hcomparison]

@[simp] theorem stableBucketedWeightedDominance_eq
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (bucketSize : ℕ) (weight : Fin Gates → ℤ) :
    (fun row column =>
      bucketedWeightedDominance
        (stableBucketedDominanceLayout
          leftScore rightScore bucketSize)
        weight row column) =
      weightedDominance leftScore rightScore weight := by
  rfl

/-- Canonical B.3 decomposition with no caller-supplied layout certificate. -/
theorem weightedDominance_eq_stable_same_add_later
    {Rows Gates Columns : ℕ}
    (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns)
    (bucketSize : ℕ) (weight : Fin Gates → ℤ)
    (row : Fin Rows) (column : Fin Columns) :
    weightedDominance leftScore rightScore weight row column =
      sameBucketContribution
          (stableBucketedDominanceLayout
            leftScore rightScore bucketSize)
          weight row column +
        laterBucketContribution
          (stableBucketedDominanceLayout
            leftScore rightScore bucketSize)
          weight row column := by
  exact bucketedWeightedDominance_eq_same_add_later
    (stableBucketedDominanceLayout leftScore rightScore bucketSize)
    weight row column

/-- Signed left matrix of the cross-bucket product, indexed by the genuine
occurrence pair `(gate,bucket)`. -/
def laterBucketLeft
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) :
    Rows → Gates × Fin Buckets → ℤ :=
  fun row index =>
    if index.2 = layout.leftBucket row index.1
    then weight index.1 else 0

/-- Boolean right matrix selecting buckets strictly earlier than the right
copy's bucket. -/
def laterBucketRight
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets) :
    Gates × Fin Buckets → Columns → Bool :=
  fun index column =>
    decide (index.2 < layout.rightBucket index.1 column)

def finiteSignedBooleanProduct
    {Rows Inner Columns : Type} [Fintype Inner]
    (left : Rows → Inner → ℤ) (right : Inner → Columns → Bool)
    (row : Rows) (column : Columns) : ℤ :=
  ∑ index, left row index * (right index column).toNat

/-- The cross-bucket term is one signed-by-Boolean product.  Each gate has
exactly one nonzero left bucket coordinate, so no coefficient is duplicated. -/
theorem laterBucketProduct_eq
    {Rows Gates Columns : Type} [Fintype Gates] {Buckets : ℕ}
    (layout : BucketedDominanceLayout Rows Gates Columns Buckets)
    (weight : Gates → ℤ) (row : Rows) (column : Columns) :
    finiteSignedBooleanProduct
        (laterBucketLeft layout weight) (laterBucketRight layout)
        row column =
      laterBucketContribution layout weight row column := by
  unfold finiteSignedBooleanProduct laterBucketLeft laterBucketRight
    laterBucketContribution
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro gate _
  rw [Finset.sum_eq_single (layout.leftBucket row gate)]
  · by_cases hlater :
      layout.leftBucket row gate < layout.rightBucket gate column
    · simp [hlater]
    · simp [hlater]
  · intro bucket _ hbucket
    simp [hbucket]
  · simp

/-- Reindex the genuine pair coordinates into the rectangular backend's
contiguous inner dimension. -/
def reindexedLaterBucketLeft
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets)
    (weight : Fin Gates → ℤ) : IntMatrix Rows (Gates * Buckets) :=
  fun row index =>
    laterBucketLeft layout weight row (finProdFinEquiv.symm index)

def reindexedLaterBucketRight
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets) :
    BitMatrix (Gates * Buckets) Columns :=
  fun index column =>
    laterBucketRight layout (finProdFinEquiv.symm index) column

theorem reindexedLaterBucketProduct_eq
    {Rows Gates Columns Buckets : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets)
    (weight : Fin Gates → ℤ) :
    signedBooleanProduct
        (reindexedLaterBucketLeft layout weight)
        (reindexedLaterBucketRight layout) =
      fun row column =>
        laterBucketContribution layout weight row column := by
  funext row column
  unfold signedBooleanProduct reindexedLaterBucketLeft
    reindexedLaterBucketRight
  calc
    (∑ index,
      laterBucketLeft layout weight row (finProdFinEquiv.symm index) *
        (laterBucketRight layout
          (finProdFinEquiv.symm index) column).toNat) =
        ∑ index : Fin Gates × Fin Buckets,
          laterBucketLeft layout weight row index *
            (laterBucketRight layout index column).toNat := by
      exact Equiv.sum_comp finProdFinEquiv.symm
        (fun index : Fin Gates × Fin Buckets =>
          laterBucketLeft layout weight row index *
            (laterBucketRight layout index column).toNat)
    _ = laterBucketContribution layout weight row column :=
      laterBucketProduct_eq layout weight row column

/-- Zero padding into the imported rectangular-product inner dimension. -/
def padSignedInner {Rows Used Capacity : ℕ}
    (left : IntMatrix Rows Used) : IntMatrix Rows Capacity :=
  fun row index =>
    if hindex : index.val < Used
    then left row ⟨index.val, hindex⟩ else 0

def padBooleanInner {Used Capacity Columns : ℕ}
    (right : BitMatrix Used Columns) : BitMatrix Capacity Columns :=
  fun index column =>
    if hindex : index.val < Used
    then right ⟨index.val, hindex⟩ column else false

theorem signedBooleanProduct_padInner_eq
    {Rows Used Capacity Columns : ℕ}
    (hcapacity : Used ≤ Capacity)
    (left : IntMatrix Rows Used) (right : BitMatrix Used Columns) :
    signedBooleanProduct
        (padSignedInner (Capacity := Capacity) left)
        (padBooleanInner (Capacity := Capacity) right) =
      signedBooleanProduct left right := by
  funext row column
  unfold signedBooleanProduct
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hcapacity
  induction extra with
  | zero =>
      apply Finset.sum_congr rfl
      intro index _
      simp [padSignedInner, padBooleanInner]
  | succ extra inductionHypothesis =>
      rw [show Used + (extra + 1) = (Used + extra) + 1 by omega]
      rw [Fin.sum_univ_castSucc]
      have hhead :
          (∑ index : Fin (Used + extra),
            padSignedInner (Capacity := (Used + extra) + 1) left row
                index.castSucc *
              (padBooleanInner (Capacity := (Used + extra) + 1) right
                index.castSucc column).toNat) =
            ∑ index : Fin (Used + extra),
              padSignedInner (Capacity := Used + extra) left row index *
                (padBooleanInner (Capacity := Used + extra) right
                  index column).toNat := by
        apply Finset.sum_congr rfl
        intro index _
        simp only [padSignedInner, padBooleanInner, Fin.val_castSucc]
      rw [hhead, inductionHypothesis (by omega)]
      simp [padSignedInner, padBooleanInner, Fin.val_last]

theorem paddedLaterBucketLeft_natAbs_lt
    {Rows Gates Columns Buckets Capacity width : ℕ}
    (layout :
      BucketedDominanceLayout (Fin Rows) (Fin Gates) (Fin Columns) Buckets)
    (weight : Fin Gates → ℤ)
    (hweight : ∀ gate, (weight gate).natAbs < 2 ^ width) :
    ∀ row index,
      (padSignedInner (Capacity := Capacity)
        (reindexedLaterBucketLeft layout weight) row index).natAbs <
          2 ^ width := by
  intro row index
  unfold padSignedInner
  split
  · unfold reindexedLaterBucketLeft laterBucketLeft
    split
    · exact hweight _
    · simp
  · simp

/-- Complete semantic handoff from the stable bucket layout to the imported
rectangular-product runner.  The remaining hypotheses are precisely its onset,
inner-capacity, and signed bit-width ledgers. -/
theorem algorithmRecombinedLaterBucketProduct_eq
    (algorithm : ExecutableRectangularProductAlgorithm)
    (onset U Gates Buckets width : ℕ)
    (hU : onset ≤ U)
    (hcapacity :
      Gates * Buckets ≤ rectangularInnerDimension U)
    (hcorrect : ∀ request : RectangularProductRequest,
      onset ≤ request.dimension →
        algorithm.compute request.dimension request.left request.right =
          integerMatrixProduct request.left request.right)
    (layout :
      BucketedDominanceLayout (Fin U) (Fin Gates) (Fin U) Buckets)
    (weight : Fin Gates → ℤ)
    (hweight : ∀ gate, (weight gate).natAbs < 2 ^ width) :
    algorithmRecombinedSignedProduct algorithm U width
        (padSignedInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketLeft layout weight))
        (padBooleanInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketRight layout)) =
      fun row column =>
        laterBucketContribution layout weight row column := by
  calc
    algorithmRecombinedSignedProduct algorithm U width
        (padSignedInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketLeft layout weight))
        (padBooleanInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketRight layout)) =
      signedBooleanProduct
        (padSignedInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketLeft layout weight))
        (padBooleanInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketRight layout)) :=
      algorithmRecombinedSignedProduct_eq algorithm onset U width hU
        hcorrect _ _
        (paddedLaterBucketLeft_natAbs_lt layout weight hweight)
    _ = signedBooleanProduct
        (reindexedLaterBucketLeft layout weight)
        (reindexedLaterBucketRight layout) :=
      signedBooleanProduct_padInner_eq hcapacity _ _
    _ = (fun row column =>
        laterBucketContribution layout weight row column) :=
      reindexedLaterBucketProduct_eq layout weight

/-- Executable cross-bucket half of B.3 for the canonical stable joint sort.
The only remaining premises are the imported backend's public onset/correctness
ledger and the two explicit representation-capacity inequalities. -/
theorem algorithmRecombinedStableLaterBucketProduct_eq
    (algorithm : ExecutableRectangularProductAlgorithm)
    (onset U Gates width bucketSize : ℕ)
    (hU : onset ≤ U)
    (hcapacity :
      Gates *
          stableDominanceBucketCount U U bucketSize ≤
        rectangularInnerDimension U)
    (hcorrect : ∀ request : RectangularProductRequest,
      onset ≤ request.dimension →
        algorithm.compute request.dimension request.left request.right =
          integerMatrixProduct request.left request.right)
    (leftScore : IntMatrix U Gates)
    (rightScore : IntMatrix Gates U)
    (weight : Fin Gates → ℤ)
    (hweight : ∀ gate, (weight gate).natAbs < 2 ^ width) :
    algorithmRecombinedSignedProduct algorithm U width
        (padSignedInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketLeft
            (stableBucketedDominanceLayout
              leftScore rightScore bucketSize)
            weight))
        (padBooleanInner
          (Capacity := rectangularInnerDimension U)
          (reindexedLaterBucketRight
            (stableBucketedDominanceLayout
              leftScore rightScore bucketSize))) =
      fun row column =>
        laterBucketContribution
          (stableBucketedDominanceLayout
            leftScore rightScore bucketSize)
          weight row column := by
  exact algorithmRecombinedLaterBucketProduct_eq
    algorithm onset U Gates
      (stableDominanceBucketCount U U bucketSize)
      width hU hcapacity hcorrect
      (stableBucketedDominanceLayout
        leftScore rightScore bucketSize)
      weight hweight

/-! ## Occurrence-sensitive exact batch evaluation -/

/-- A monomial is a list, rather than a set, because the canonical expansion
in A.12.1 is occurrence-sensitive.  Repeated equations therefore remain
distinct coordinates while evaluation is their ordinary conjunction. -/
def exactMonomialValue {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomial : List Equation) (row : Row) (column : Column) : Bool :=
  monomial.all fun equation => holds equation row column

/-- Number of true monomial occurrences at one point. -/
def polynomialOccurrenceCount {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) : ℕ :=
  (monomials.map fun monomial =>
    (exactMonomialValue holds monomial row column).toNat).sum

/-- Evaluation of an explicitly represented `𝔽₂` polynomial.  This is total
on every row and column, including malformed upstream representations. -/
def exactPolynomialValue {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) : Bool :=
  decide (Odd (polynomialOccurrenceCount holds monomials row column))

/-- The true coordinates are indexed by positions in the monomial list.  Two
definitionally equal monomials at different positions remain different
members of this finset. -/
def trueMonomialOccurrences {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    Finset (Fin monomials.length) :=
  Finset.univ.filter fun index =>
    exactMonomialValue holds (monomials.get index) row column = true

theorem trueMonomialOccurrences_card {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    (trueMonomialOccurrences holds monomials row column).card =
      polynomialOccurrenceCount holds monomials row column := by
  have hlist :
      monomials.map (fun monomial =>
          (exactMonomialValue holds monomial row column).toNat) =
        List.ofFn (fun index : Fin monomials.length =>
          (exactMonomialValue holds (monomials.get index) row column).toNat) := by
    simpa using
      (List.ofFn_getElem_eq_map monomials
        (fun monomial =>
          (exactMonomialValue holds monomial row column).toNat)).symm
  have hsum :
      polynomialOccurrenceCount holds monomials row column =
        ∑ index : Fin monomials.length,
          (exactMonomialValue holds (monomials.get index) row column).toNat := by
    unfold polynomialOccurrenceCount
    rw [hlist, List.sum_ofFn]
  unfold trueMonomialOccurrences
  rw [Finset.card_filter]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro index _
  cases exactMonomialValue holds (monomials.get index) row column <;> rfl

/-- Number of size-`j` subsets whose every monomial occurrence is true. -/
def trueOccurrenceSubsetCount {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (j : ℕ)
    (row : Row) (column : Column) : ℕ :=
  ((Finset.univ : Finset (Fin monomials.length)).powersetCard j).filter
    (fun subset =>
      subset ⊆ trueMonomialOccurrences holds monomials row column) |>.card

/-- The occurrence-indexed elementary-symmetric identity used by A.12.1.
This explicitly rules out accidental deduplication of identical monomials. -/
theorem trueOccurrenceSubsetCount_eq_choose
    {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (j : ℕ)
    (row : Row) (column : Column) :
    trueOccurrenceSubsetCount holds monomials j row column =
      (polynomialOccurrenceCount holds monomials row column).choose j := by
  have hfilter :
      ((Finset.univ : Finset (Fin monomials.length)).powersetCard j).filter
          (fun subset =>
            subset ⊆ trueMonomialOccurrences holds monomials row column) =
        (trueMonomialOccurrences holds monomials row column).powersetCard j := by
    ext subset
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact and_comm
  unfold trueOccurrenceSubsetCount
  rw [hfilter, Finset.card_powersetCard,
    trueMonomialOccurrences_card]

/-- The truncated lift is literally the signed sum over occurrence subsets;
the exponent `j` represents subsets of size `j + 1`. -/
theorem binLift_eq_occurrenceSubsetExpansion
    {Row Column Equation : Type}
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    binLift Q (polynomialOccurrenceCount holds monomials row column) =
      ∑ j ∈ range
          (min Q (polynomialOccurrenceCount holds monomials row column)),
        (-2 : ℤ) ^ j *
          (trueOccurrenceSubsetCount holds monomials (j + 1)
            row column : ℤ) := by
  unfold binLift
  apply Finset.sum_congr rfl
  intro j _
  rw [trueOccurrenceSubsetCount_eq_choose]

/-- Extending the occurrence-subset expansion to every syntactic monomial
position adds only zero terms.  This fixed, input-independent index set is the
one used by the matrix printer. -/
theorem binLift_eq_fullOccurrenceSubsetExpansion
    {Row Column Equation : Type}
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    binLift Q (polynomialOccurrenceCount holds monomials row column) =
      ∑ j ∈ range (min Q monomials.length),
        (-2 : ℤ) ^ j *
          (trueOccurrenceSubsetCount holds monomials (j + 1)
            row column : ℤ) := by
  rw [binLift_eq_occurrenceSubsetExpansion]
  apply Finset.sum_subset
  · apply Finset.range_mono
    apply min_le_min_left
    rw [← trueMonomialOccurrences_card]
    simpa using
      (Finset.card_le_card
        (Finset.subset_univ
          (trueMonomialOccurrences holds monomials row column)))
  · intro j hjLarge hjSmall
    have hjLarge' : j < min Q monomials.length :=
      Finset.mem_range.mp hjLarge
    have hjSmall' :
        ¬j < min Q
          (polynomialOccurrenceCount holds monomials row column) := by
      simpa only [Finset.mem_range] using hjSmall
    have hcount :
        polynomialOccurrenceCount holds monomials row column < j + 1 := by
      omega
    rw [trueOccurrenceSubsetCount_eq_choose,
      Nat.choose_eq_zero_of_lt hcount]
    simp

theorem exactPolynomialValue_toNat {Row Column Equation : Type}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    (exactPolynomialValue holds monomials row column).toNat =
      polynomialOccurrenceCount holds monomials row column % 2 := by
  unfold exactPolynomialValue
  rcases Nat.even_or_odd
      (polynomialOccurrenceCount holds monomials row column) with heven | hodd
  · simp [Nat.not_odd_iff_even.mpr heven, Nat.even_iff.mp heven]
  · simp [hodd, Nat.odd_iff.mp hodd]

/-! ### Canonical `𝔽₂` polynomial rows -/

/-- Expand one formal monomial into its literal occurrences.  Exponents are
retained as repeated entries: Boolean evaluation is unchanged, while degree
and printer syntax cannot be understated by silently squarefree-reducing. -/
noncomputable def monomialVariableOccurrences {Variable : Type}
    [DecidableEq Variable] (monomial : Variable →₀ ℕ) : List Variable :=
  monomial.support.toList.flatMap fun coordinate =>
    List.replicate (monomial coordinate) coordinate

theorem exactMonomialValue_variableOccurrences
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (monomial : Variable →₀ ℕ) (row : Row) (column : Column) :
    exactMonomialValue holds (monomialVariableOccurrences monomial) row column =
      monomial.support.toList.all fun coordinate =>
        holds coordinate row column := by
  unfold monomialVariableOccurrences exactMonomialValue
  simp only [List.all_flatMap, List.all_replicate]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hall coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hcoordinate)
    simpa [hpositive] using hall coordinate hcoordinate
  · intro hall coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hcoordinate)
    simpa [hpositive] using hall coordinate hcoordinate

theorem monomial_eval_eq_exactMonomialValue
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (monomial : Variable →₀ ℕ) (row : Row) (column : Column) :
    (∏ coordinate ∈ monomial.support,
        ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate) =
      ((exactMonomialValue holds
        (monomialVariableOccurrences monomial) row column).toNat :
          ZMod 2) := by
  have hfactor : ∀ coordinate ∈ monomial.support,
      ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate =
        if holds coordinate row column = true then 1 else 0 := by
    intro coordinate hcoordinate
    have hpositive : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp hcoordinate
    cases holds coordinate row column <;> simp [hpositive]
  calc
    (∏ coordinate ∈ monomial.support,
        ((holds coordinate row column).toNat : ZMod 2) ^
          monomial coordinate) =
        ∏ coordinate ∈ monomial.support,
          if holds coordinate row column = true then 1 else 0 := by
            apply Finset.prod_congr rfl
            intro coordinate hcoordinate
            exact hfactor coordinate hcoordinate
    _ = if ∀ coordinate ∈ monomial.support,
          holds coordinate row column = true then 1 else 0 :=
      Finset.prod_boole
    _ = ((exactMonomialValue holds
        (monomialVariableOccurrences monomial) row column).toNat :
          ZMod 2) := by
      rw [exactMonomialValue_variableOccurrences]
      by_cases hall : ∀ coordinate ∈ monomial.support,
          holds coordinate row column = true
      · have hallList :
            (monomial.support.toList.all fun coordinate =>
              holds coordinate row column) = true := by
          rw [List.all_eq_true]
          intro coordinate hcoordinate
          exact hall coordinate (Finset.mem_toList.mp hcoordinate)
        rw [if_pos hall, hallList]
        rfl
      · have hallList :
            (monomial.support.toList.all fun coordinate =>
              holds coordinate row column) = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          apply hall
          rw [List.all_eq_true] at htrue
          intro coordinate hcoordinate
          exact htrue coordinate (Finset.mem_toList.mpr hcoordinate)
        rw [if_neg hall, hallList]
        rfl

/-- Canonical occurrence-sensitive expansion of a finite `𝔽₂` polynomial.
Support membership removes zero coefficients; every surviving coefficient is
one because the coefficient ring is `ZMod 2`. -/
noncomputable def polynomialMonomialOccurrences
    {Variable : Type} [DecidableEq Variable]
    (polynomial : MvPolynomial Variable (ZMod 2)) :
    List (List Variable) :=
  polynomial.support.toList.map monomialVariableOccurrences

theorem zmodTwo_coeff_eq_one_of_mem_support
    {Variable : Type}
    (polynomial : MvPolynomial Variable (ZMod 2))
    (monomial : Variable →₀ ℕ) (hmonomial : monomial ∈ polynomial.support) :
    polynomial.coeff monomial = 1 := by
  classical
  have hnonzero : polynomial.coeff monomial ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmonomial
  have hvalNonzero : (polynomial.coeff monomial).val ≠ 0 := by
    intro hzero
    exact hnonzero ((ZMod.val_eq_zero _).mp hzero)
  apply (ZMod.val_eq_one (by norm_num) _).mp
  have hlt := ZMod.val_lt (polynomial.coeff monomial)
  omega

theorem polynomialOccurrenceCount_variableOccurrences
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    polynomialOccurrenceCount holds
        (polynomialMonomialOccurrences polynomial) row column =
      ∑ monomial ∈ polynomial.support,
        (exactMonomialValue holds
          (monomialVariableOccurrences monomial) row column).toNat := by
  unfold polynomialOccurrenceCount polynomialMonomialOccurrences
  simp [Function.comp_def, Finset.sum_map_toList]

theorem aeval_polynomial_eq_occurrenceCount
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    MvPolynomial.aeval
        (fun coordinate =>
          ((holds coordinate row column).toNat : ZMod 2))
        polynomial =
      (polynomialOccurrenceCount holds
        (polynomialMonomialOccurrences polynomial) row column :
          ZMod 2) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    polynomialOccurrenceCount_variableOccurrences]
  push_cast
  apply Finset.sum_congr rfl
  intro monomial hmonomial
  rw [zmodTwo_coeff_eq_one_of_mem_support polynomial monomial hmonomial,
    map_one, one_mul, monomial_eval_eq_exactMonomialValue]

/-- The generic row consumed by the exact-score printer is definitionally the
Boolean value of the source `𝔽₂` polynomial after canonical expansion. -/
theorem exactPolynomialValue_compiled
    {Variable Row Column : Type} [DecidableEq Variable]
    (holds : Variable → Row → Column → Bool)
    (polynomial : MvPolynomial Variable (ZMod 2))
    (row : Row) (column : Column) :
    exactPolynomialValue holds
        (polynomialMonomialOccurrences polynomial) row column =
      decide
        (MvPolynomial.aeval
          (fun coordinate =>
            ((holds coordinate row column).toNat : ZMod 2))
          polynomial = 1) := by
  unfold exactPolynomialValue
  rw [aeval_polynomial_eq_occurrenceCount]
  exact decide_eq_decide.mpr ZMod.natCast_eq_one_iff_odd.symm

/-- The signed score printed before reduction modulo `2^Q`. -/
def liftedColumnScore {Row Column Equation : Type} [Fintype Row]
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) : ℤ :=
  ∑ row, binLift Q
    (polynomialOccurrenceCount holds monomials row column)

/-- The desired exact Boolean column count. -/
def exactColumnCount {Row Column Equation : Type} [Fintype Row]
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) : ℕ :=
  ∑ row, (exactPolynomialValue holds monomials row column).toNat

/-- Equation (A.12.1), summed over all live assignments.  The statement does
not assume monomials are unique and hence preserves canonical occurrences. -/
theorem liftedColumnScore_modEq_exactColumnCount
    {Row Column Equation : Type} [Fintype Row]
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) :
    liftedColumnScore Q holds monomials column ≡
      (exactColumnCount holds monomials column : ℤ)
        [ZMOD (2 : ℤ) ^ Q] := by
  unfold liftedColumnScore exactColumnCount
  rw [Nat.cast_sum]
  apply Int.ModEq.sum
  intro row _
  rw [exactPolynomialValue_toNat]
  exact binLiftModEqParity Q
    (polynomialOccurrenceCount holds monomials row column)

theorem exactColumnCount_le_card
    {Row Column Equation : Type} [Fintype Row]
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) :
    exactColumnCount holds monomials column ≤ Fintype.card Row := by
  unfold exactColumnCount
  calc
    (∑ row, (exactPolynomialValue holds monomials row column).toNat) ≤
        ∑ _row : Row, 1 := by
      apply Finset.sum_le_sum
      intro row _
      cases exactPolynomialValue holds monomials row column <;> simp
    _ = Fintype.card Row := by simp

/-- The least nonnegative residue of the signed printed score. -/
def recoveredColumnCount {Row Column Equation : Type} [Fintype Row]
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) : ℕ :=
  Int.toNat (liftedColumnScore Q holds monomials column % (2 : ℤ) ^ Q)

/-- Once the Boolean column contains fewer than `2^Q` rows, modular reduction
recovers the exact count, not merely its parity or a congruence class. -/
theorem recoveredColumnCount_eq
    {Row Column Equation : Type} [Fintype Row]
    (Q : ℕ) (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column)
    (hcard : Fintype.card Row < 2 ^ Q) :
    recoveredColumnCount Q holds monomials column =
      exactColumnCount holds monomials column := by
  have hcountNat :
      exactColumnCount holds monomials column < 2 ^ Q :=
    lt_of_le_of_lt (exactColumnCount_le_card holds monomials column) hcard
  have hcountNonnegative :
      (0 : ℤ) ≤ (exactColumnCount holds monomials column : ℕ) := by
    exact_mod_cast Nat.zero_le (exactColumnCount holds monomials column)
  have hcountLt :
      (exactColumnCount holds monomials column : ℤ) < (2 : ℤ) ^ Q := by
    exact_mod_cast hcountNat
  have hmod :=
    Int.ModEq.eq
      (liftedColumnScore_modEq_exactColumnCount
        Q holds monomials column)
  rw [Int.emod_eq_of_lt hcountNonnegative hcountLt] at hmod
  unfold recoveredColumnCount
  rw [hmod]
  simp

/-- A.12.1's standard live cube has `2^K` rows, so `K < Q` is the complete
range condition needed for exact recovery. -/
theorem recoveredBitInputColumnCount_eq
    {K Q : ℕ} {Column Equation : Type}
    (holds : Equation → BitInput K → Column → Bool)
    (monomials : List (List Equation)) (column : Column)
    (hKQ : K < Q) :
    recoveredColumnCount Q holds monomials column =
      exactColumnCount holds monomials column := by
  apply recoveredColumnCount_eq
  simpa [BitInput] using Nat.pow_lt_pow_right Nat.one_lt_two hKQ

end NearCubicWires.SupplierPrinter
