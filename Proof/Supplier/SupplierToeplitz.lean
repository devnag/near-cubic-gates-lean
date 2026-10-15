import Proof.Supplier.SupplierList
import Proof.Supplier.SupplierToeplitzCore

/-!
# Production Toeplitz supplier list

The supplier uses the explicit binary Toeplitz family, rather than a
noncomputable presentation of a finite field.  This file builds the nested
zero-prefix partition directly on hash output bits and derives the exact
cardinality, density, and count recurrence needed by the pointwise list.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierToeplitz

open NearCubicWires.SupplierList
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitzCore

abbrev BinaryVector (rank : ℕ) :=
  NearCubicWires.SupplierToeplitzCore.BitVec rank

/-- Hash outputs whose first `level` coordinates vanish. -/
def zeroPrefixCell (rank level : ℕ) : Finset (BinaryVector rank) :=
  Finset.univ.filter fun value =>
    ∀ coordinate : Fin rank,
      coordinate.val < level → value coordinate = 0

@[simp] theorem mem_zeroPrefixCell
    {rank level : ℕ} (value : BinaryVector rank) :
    value ∈ zeroPrefixCell rank level ↔
      ∀ coordinate : Fin rank,
        coordinate.val < level → value coordinate = 0 := by
  simp [zeroPrefixCell]

/-- Reindex the unconstrained suffix after a zero prefix. -/
def suffixIndex {rank level : ℕ} (hlevel : level ≤ rank)
    (coordinate : Fin (rank - level)) : Fin rank :=
  ⟨level + coordinate.val, by omega⟩

/-- Extend an arbitrary suffix by `level` leading zero coordinates. -/
def extendZeroPrefix {rank level : ℕ} (hlevel : level ≤ rank)
    (suffix : BinaryVector (rank - level)) : BinaryVector rank :=
  fun coordinate =>
    if hprefix : coordinate.val < level then
      0
    else
      suffix ⟨coordinate.val - level, by omega⟩

@[simp] theorem extendZeroPrefix_prefix
    {rank level : ℕ} (hlevel : level ≤ rank)
    (suffix : BinaryVector (rank - level)) (coordinate : Fin rank)
    (hcoordinate : coordinate.val < level) :
    extendZeroPrefix hlevel suffix coordinate = 0 := by
  simp [extendZeroPrefix, hcoordinate]

@[simp] theorem extendZeroPrefix_suffix
    {rank level : ℕ} (hlevel : level ≤ rank)
    (suffix : BinaryVector (rank - level))
    (coordinate : Fin (rank - level)) :
    extendZeroPrefix hlevel suffix (suffixIndex hlevel coordinate) =
      suffix coordinate := by
  simp only [extendZeroPrefix, suffixIndex]
  split
  · rename_i hprefix
    omega
  · congr 1
    apply Fin.ext
    simp

/-- A zero-prefix vector is completely and uniquely determined by its
unconstrained suffix. -/
def zeroPrefixEquiv {rank level : ℕ} (hlevel : level ≤ rank) :
    {value : BinaryVector rank // value ∈ zeroPrefixCell rank level} ≃
      BinaryVector (rank - level) where
  toFun value := fun coordinate =>
    value.1 (suffixIndex hlevel coordinate)
  invFun suffix :=
    ⟨extendZeroPrefix hlevel suffix, by
      rw [mem_zeroPrefixCell]
      intro coordinate hcoordinate
      exact extendZeroPrefix_prefix hlevel suffix coordinate hcoordinate⟩
  left_inv value := by
    apply Subtype.ext
    funext coordinate
    change
      extendZeroPrefix hlevel
          (fun suffixCoordinate =>
            value.1 (suffixIndex hlevel suffixCoordinate))
          coordinate =
        value.1 coordinate
    by_cases hcoordinate : coordinate.val < level
    · rw [extendZeroPrefix_prefix hlevel _ coordinate hcoordinate]
      exact ((mem_zeroPrefixCell value.1).mp value.2
        coordinate hcoordinate).symm
    · simp only [extendZeroPrefix, hcoordinate, ↓reduceDIte]
      apply congrArg value.1
      apply Fin.ext
      simp only [suffixIndex]
      omega
  right_inv suffix := by
    funext coordinate
    exact extendZeroPrefix_suffix hlevel suffix coordinate

theorem bitVec_card (rank : ℕ) :
    Fintype.card (BinaryVector rank) = 2 ^ rank := by
  exact NearCubicWires.SupplierToeplitzCore.card_bitVec rank

theorem zeroPrefixCell_card
    {rank level : ℕ} (hlevel : level ≤ rank) :
    (zeroPrefixCell rank level).card = 2 ^ (rank - level) := by
  classical
  rw [← Fintype.card_coe]
  calc
    Fintype.card {value : BinaryVector rank //
        value ∈ zeroPrefixCell rank level} =
        Fintype.card (BinaryVector (rank - level)) :=
      Fintype.card_congr (zeroPrefixEquiv hlevel)
    _ = 2 ^ (rank - level) := bitVec_card _

/-- The sibling is the part of a prefix cell discarded by the next bit. -/
def siblingPrefixCell (rank level : ℕ) :
    Finset (BinaryVector rank) :=
  zeroPrefixCell rank level \ zeroPrefixCell rank (level + 1)

theorem zeroPrefixCell_succ_subset
    {rank level : ℕ} :
    zeroPrefixCell rank (level + 1) ⊆ zeroPrefixCell rank level := by
  intro value hvalue
  rw [mem_zeroPrefixCell] at hvalue ⊢
  intro coordinate hcoordinate
  exact hvalue coordinate (by omega)

theorem siblingPrefixCell_disjoint
    {rank level : ℕ} :
    Disjoint
      (siblingPrefixCell rank level)
      (zeroPrefixCell rank (level + 1)) := by
  classical
  exact Finset.sdiff_disjoint

theorem siblingPrefixCell_union_child
    {rank level : ℕ} :
    siblingPrefixCell rank level ∪ zeroPrefixCell rank (level + 1) =
      zeroPrefixCell rank level := by
  classical
  unfold siblingPrefixCell
  exact Finset.sdiff_union_of_subset zeroPrefixCell_succ_subset

theorem siblingPrefixCell_card
    {rank level : ℕ} (hlevel : level < rank) :
    (siblingPrefixCell rank level).card =
      2 ^ (rank - (level + 1)) := by
  classical
  unfold siblingPrefixCell
  rw [Finset.card_sdiff_of_subset zeroPrefixCell_succ_subset]
  rw [zeroPrefixCell_card hlevel.le,
    zeroPrefixCell_card (by omega)]
  have hexponent :
      rank - level = (rank - (level + 1)) + 1 := by
    omega
  rw [hexponent, pow_succ]
  omega

theorem siblingPrefixCell_balanced
    {rank level : ℕ} (hlevel : level < rank) :
    (siblingPrefixCell rank level).card =
      (zeroPrefixCell rank (level + 1)).card := by
  rw [siblingPrefixCell_card hlevel,
    zeroPrefixCell_card (by omega)]

theorem prefixCell_card_add
    {rank level : ℕ} :
    (siblingPrefixCell rank level).card +
        (zeroPrefixCell rank (level + 1)).card =
      (zeroPrefixCell rank level).card := by
  classical
  rw [← Finset.card_union_of_disjoint siblingPrefixCell_disjoint]
  rw [siblingPrefixCell_union_child]

theorem prefixSlice_density
    {rank level : ℕ} (hlevel : level < rank) :
    (((siblingPrefixCell rank level).card +
        (zeroPrefixCell rank (level + 1)).card : ℕ) : ℝ) /
        Fintype.card (BinaryVector rank) =
      1 / (2 : ℝ) ^ level := by
  rw [prefixCell_card_add, zeroPrefixCell_card hlevel.le,
    bitVec_card]
  norm_cast
  have hexponent : rank = (rank - level) + level := by omega
  have hpow : 2 ^ rank =
      2 ^ (rank - level) * 2 ^ level := by
    rw [← pow_add, ← hexponent]
  rw [hpow]
  push_cast
  field_simp

theorem terminalPrefix_density
    {rank level : ℕ} (hlevel : level ≤ rank) :
    ((zeroPrefixCell rank level).card : ℝ) /
        Fintype.card (BinaryVector rank) =
      1 / (2 : ℝ) ^ level := by
  rw [zeroPrefixCell_card hlevel, bitVec_card]
  norm_cast
  have hexponent : rank = (rank - level) + level := by omega
  have hpow : 2 ^ rank =
      2 ^ (rank - level) * 2 ^ level := by
    rw [← pow_add, ← hexponent]
  rw [hpow]
  push_cast
  field_simp

def toeplitzAggregate
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (contribution : Index → BinaryVector rank → ℝ)
    (seed : ToeplitzSeed rank) : ℝ :=
  ∑ index ∈ active,
    contribution index (toeplitzHash (label index) seed)

theorem sum_toeplitzHash_product_eq_zero
    {rank : ℕ} (leftLabel rightLabel : BinaryVector rank)
    (hdistinct : leftLabel ≠ rightLabel)
    (leftValue rightValue : BinaryVector rank → ℝ)
    (hleftCentered : ∑ output, leftValue output = 0)
    (hrightCentered : ∑ output, rightValue output = 0) :
    ∑ seed : ToeplitzSeed rank,
        leftValue (toeplitzHash leftLabel seed) *
          rightValue (toeplitzHash rightLabel seed) = 0 := by
  rw [sum_toeplitzHash_pair_exact leftLabel rightLabel hdistinct
    (fun leftOutput rightOutput =>
      leftValue leftOutput * rightValue rightOutput)]
  have hproduct :
      (∑ leftOutput : BinaryVector rank,
        ∑ rightOutput : BinaryVector rank,
          leftValue leftOutput * rightValue rightOutput) =
        (∑ leftOutput : BinaryVector rank, leftValue leftOutput) *
          ∑ rightOutput : BinaryVector rank, rightValue rightOutput := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hproduct, hleftCentered, hrightCentered]
  ring

/-- Pairwise independence removes every off-diagonal term.  The surviving
one-output multiplicity is kept exact so it cancels against the seed count. -/
theorem sum_toeplitzAggregate_sq
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (contribution : Index → BinaryVector rank → ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0) :
    ∑ seed : ToeplitzSeed rank,
        toeplitzAggregate active label contribution seed ^ 2 =
      Fintype.card (ToeplitzDiagonal rank) *
        ∑ index ∈ active,
          ∑ output : BinaryVector rank,
            contribution index output ^ 2 := by
  unfold toeplitzAggregate
  calc
    (∑ seed : ToeplitzSeed rank,
        (∑ index ∈ active,
          contribution index
            (toeplitzHash (label index) seed)) ^ 2) =
        ∑ left ∈ active, ∑ right ∈ active,
          ∑ seed : ToeplitzSeed rank,
            contribution left
                (toeplitzHash (label left) seed) *
              contribution right
                (toeplitzHash (label right) seed) := by
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.sum_comm]
    _ = ∑ index ∈ active,
          ∑ seed : ToeplitzSeed rank,
            contribution index
                (toeplitzHash (label index) seed) *
              contribution index
                (toeplitzHash (label index) seed) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_eq_single left
      · intro right hright hrightNe
        exact sum_toeplitzHash_product_eq_zero
          (label left) (label right)
          (hlabels left hleft right hright hrightNe.symm)
          (contribution left) (contribution right)
          (hcentered left hleft) (hcentered right hright)
      · intro hleftMissing
        exact (hleftMissing hleft).elim
    _ = ∑ index ∈ active,
          Fintype.card (ToeplitzDiagonal rank) *
            ∑ output : BinaryVector rank,
              contribution index output *
                contribution index output := by
      apply Finset.sum_congr rfl
      intro index _
      exact sum_toeplitzHash (label index)
        (fun output =>
          contribution index output * contribution index output)
    _ = Fintype.card (ToeplitzDiagonal rank) *
        ∑ index ∈ active,
          ∑ output : BinaryVector rank,
            contribution index output ^ 2 := by
      rw [Finset.mul_sum]
      simp [pow_two]

theorem realMean_toeplitzAggregate_sq
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (contribution : Index → BinaryVector rank → ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0) :
    realMean (fun seed : ToeplitzSeed rank =>
      toeplitzAggregate active label contribution seed ^ 2) =
      ∑ index ∈ active,
        realMean (fun output : BinaryVector rank =>
          contribution index output ^ 2) := by
  have hdiagonalCard :
      (Fintype.card (ToeplitzDiagonal rank) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold realMean
  rw [sum_toeplitzAggregate_sq active label contribution
    hlabels hcentered]
  rw [card_toeplitzSeed_eq_oneMultiplicity_mul_output]
  simp only [Nat.cast_mul]
  calc
    (Fintype.card (ToeplitzDiagonal rank) : ℝ) *
          (∑ index ∈ active,
            ∑ output : BinaryVector rank,
              contribution index output ^ 2) /
        ((Fintype.card (ToeplitzDiagonal rank) : ℝ) *
          Fintype.card (BinaryVector rank)) =
        (∑ index ∈ active,
          ∑ output : BinaryVector rank,
            contribution index output ^ 2) /
          Fintype.card (BinaryVector rank) :=
      mul_div_mul_left _ _ hdiagonalCard
    _ = ∑ index ∈ active,
        (∑ output : BinaryVector rank,
          contribution index output ^ 2) /
            Fintype.card (BinaryVector rank) :=
      Finset.sum_div _ _ _

theorem realMean_toeplitzAggregate_sq_le
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (contribution : Index → BinaryVector rank → ℝ)
    (variance : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0)
    (hvariance : ∀ index ∈ active,
      realMean (fun output : BinaryVector rank =>
        contribution index output ^ 2) ≤ variance) :
    realMean (fun seed : ToeplitzSeed rank =>
      toeplitzAggregate active label contribution seed ^ 2) ≤
      active.card * variance := by
  rw [realMean_toeplitzAggregate_sq active label contribution
    hlabels hcentered]
  calc
    (∑ index ∈ active,
      realMean (fun output : BinaryVector rank =>
        contribution index output ^ 2)) ≤
        ∑ _index ∈ active, variance :=
      Finset.sum_le_sum fun index hindex =>
        hvariance index hindex
    _ = active.card * variance := by simp

theorem toeplitzAggregate_chebyshev
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (contribution : Index → BinaryVector rank → ℝ)
    (coordinateVariance threshold : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0)
    (hvariance : ∀ index ∈ active,
      realMean (fun output : BinaryVector rank =>
        contribution index output ^ 2) ≤ coordinateVariance)
    (hthreshold : 0 < threshold) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (threshold <
        |toeplitzAggregate active label contribution seed|)) ≤
      (active.card * coordinateVariance) / threshold ^ 2 := by
  letI : Nonempty (ToeplitzSeed rank) :=
    ⟨(0, 0)⟩
  exact booleanMean_abs_gt_le
    (fun seed => toeplitzAggregate active label contribution seed)
    threshold (active.card * coordinateVariance) hthreshold
    (realMean_toeplitzAggregate_sq_le active label contribution
      coordinateVariance hlabels hcentered hvariance)

theorem toeplitzSignedSlice_chebyshev
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (positive negative : Finset (BinaryVector rank))
    (level activeBound : ℕ) (threshold : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hdisjoint : Disjoint positive negative)
    (hbalanced : positive.card = negative.card)
    (hactive : active.card ≤ activeBound)
    (hdensity :
      ((positive.card + negative.card : ℕ) : ℝ) /
          Fintype.card (BinaryVector rank) ≤
        1 / (2 : ℝ) ^ level)
    (hthreshold : 0 < threshold) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (threshold <
        |toeplitzAggregate active label
          (fun _index => signedSlice positive negative) seed|)) ≤
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
        threshold ^ 2 := by
  have hcentered : ∀ index ∈ active,
      ∑ output : BinaryVector rank,
        signedSlice positive negative output = 0 := by
    intro _index _
    rw [sum_signedSlice positive negative hdisjoint, hbalanced]
    simp
  have hvariance : ∀ index ∈ active,
      realMean (fun output : BinaryVector rank =>
        signedSlice positive negative output ^ 2) ≤
          1 / (2 : ℝ) ^ level := by
    intro _index _
    rw [realMean_signedSlice_sq positive negative hdisjoint]
    simpa only [Nat.cast_add] using hdensity
  have hbase := toeplitzAggregate_chebyshev active label
    (fun _index => signedSlice positive negative)
    (1 / (2 : ℝ) ^ level) threshold hlabels hcentered hvariance
    hthreshold
  calc
    booleanMean (fun seed : ToeplitzSeed rank =>
        decide (threshold <
          |toeplitzAggregate active label
            (fun _index => signedSlice positive negative) seed|)) ≤
        ((active.card : ℝ) * (1 / (2 : ℝ) ^ level)) /
          threshold ^ 2 := hbase
    _ ≤ ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
          threshold ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg threshold)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hactive

def toeplitzCellCount
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (cell : Finset (BinaryVector rank))
    (seed : ToeplitzSeed rank) : ℕ :=
  ∑ index ∈ active,
    (decide (toeplitzHash (label index) seed ∈ cell) : Bool).toNat

theorem realMean_toeplitzCellCount
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (cell : Finset (BinaryVector rank)) :
    realMean (fun seed : ToeplitzSeed rank =>
      (toeplitzCellCount active label cell seed : ℝ)) =
      active.card *
        (cell.card / Fintype.card (BinaryVector rank) : ℝ) := by
  have hdiagonalCard :
      (Fintype.card (ToeplitzDiagonal rank) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold realMean toeplitzCellCount
  push_cast
  simp_rw [← bitAsReal_eq_toNat]
  rw [Finset.sum_comm]
  have hperIndex : ∀ index ∈ active,
      ∑ seed : ToeplitzSeed rank,
          bitAsReal
            (decide (toeplitzHash (label index) seed ∈ cell)) =
        Fintype.card (ToeplitzDiagonal rank) * cell.card := by
    intro index _
    calc
      (∑ seed : ToeplitzSeed rank,
          bitAsReal
            (decide (toeplitzHash (label index) seed ∈ cell))) =
          Fintype.card (ToeplitzDiagonal rank) *
            ∑ output : BinaryVector rank,
              bitAsReal (decide (output ∈ cell)) :=
        sum_toeplitzHash (label index)
          (fun output => bitAsReal (decide (output ∈ cell)))
      _ = Fintype.card (ToeplitzDiagonal rank) * cell.card := by
        congr 1
        simp [bitAsReal]
  have hsum :
      (∑ index ∈ active,
        ∑ seed : ToeplitzSeed rank,
          bitAsReal
            (decide (toeplitzHash (label index) seed ∈ cell))) =
        ∑ _index ∈ active,
          (Fintype.card (ToeplitzDiagonal rank) : ℝ) *
            cell.card := by
    exact Finset.sum_congr rfl fun index hindex =>
      hperIndex index hindex
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_toeplitzSeed_eq_oneMultiplicity_mul_output]
  simp only [Nat.cast_mul]
  field_simp

theorem toeplitzCell_nonempty_le
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (cell : Finset (BinaryVector rank)) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (0 < toeplitzCellCount active label cell seed)) ≤
      active.card *
        (cell.card / Fintype.card (BinaryVector rank) : ℝ) := by
  letI : Nonempty (ToeplitzSeed rank) :=
    ⟨(0, 0)⟩
  calc
    booleanMean (fun seed : ToeplitzSeed rank =>
        decide (0 < toeplitzCellCount active label cell seed)) ≤
        realMean (fun seed : ToeplitzSeed rank =>
          (toeplitzCellCount active label cell seed : ℝ)) :=
      booleanMean_positiveNat_le_realMean
        (toeplitzCellCount active label cell)
    _ = active.card *
        (cell.card / Fintype.card (BinaryVector rank) : ℝ) :=
      realMean_toeplitzCellCount active label cell

theorem toeplitzCell_terminalBound
    {Index : Type} [DecidableEq Index]
    {rank : ℕ} (active : Finset Index)
    (label : Index → BinaryVector rank)
    (cell : Finset (BinaryVector rank))
    (level activeBound : ℕ)
    (hactive : active.card ≤ activeBound)
    (hdensity :
      (cell.card : ℝ) / Fintype.card (BinaryVector rank) ≤
        1 / (2 : ℝ) ^ level) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (0 < toeplitzCellCount active label cell seed)) ≤
      (activeBound : ℝ) / (2 : ℝ) ^ level := by
  calc
    booleanMean (fun seed : ToeplitzSeed rank =>
        decide (0 < toeplitzCellCount active label cell seed)) ≤
        (active.card : ℝ) *
          ((cell.card : ℝ) /
            Fintype.card (BinaryVector rank)) :=
      toeplitzCell_nonempty_le active label cell
    _ ≤ (activeBound : ℝ) * (1 / (2 : ℝ) ^ level) := by
      apply mul_le_mul
      · exact_mod_cast hactive
      · exact hdensity
      · positivity
      · positivity
    _ = (activeBound : ℝ) / (2 : ℝ) ^ level := by ring

theorem toeplitzPrefixSlice_chebyshev
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ} (hlevel : level < rank)
    (active : Finset Index) (label : Index → BinaryVector rank)
    (activeBound : ℕ) (threshold : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hactive : active.card ≤ activeBound)
    (hthreshold : 0 < threshold) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (threshold <
        |toeplitzAggregate active label
          (fun _index =>
            signedSlice (siblingPrefixCell rank level)
              (zeroPrefixCell rank (level + 1))) seed|)) ≤
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
        threshold ^ 2 := by
  apply toeplitzSignedSlice_chebyshev active label
    (siblingPrefixCell rank level)
    (zeroPrefixCell rank (level + 1))
    level activeBound threshold hlabels
  · exact siblingPrefixCell_disjoint
  · exact siblingPrefixCell_balanced hlevel
  · exact hactive
  · exact (prefixSlice_density hlevel).le
  · exact hthreshold

theorem toeplitzTerminalPrefix_bound
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ} (hlevel : level ≤ rank)
    (active : Finset Index) (label : Index → BinaryVector rank)
    (activeBound : ℕ) (hactive : active.card ≤ activeBound) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      decide (0 <
        toeplitzCellCount active label
          (zeroPrefixCell rank level) seed)) ≤
      (activeBound : ℝ) / (2 : ℝ) ^ level := by
  apply toeplitzCell_terminalBound active label
    (zeroPrefixCell rank level) level activeBound hactive
  exact (terminalPrefix_density hlevel).le

theorem toeplitzPrefixCount_add
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ}
    (active : Finset Index) (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) :
    toeplitzCellCount active label (zeroPrefixCell rank level) seed =
      toeplitzCellCount active label (siblingPrefixCell rank level) seed +
        toeplitzCellCount active label
          (zeroPrefixCell rank (level + 1)) seed := by
  classical
  unfold toeplitzCellCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  let value := toeplitzHash (label index) seed
  have hunion :
      siblingPrefixCell rank level ∪
          zeroPrefixCell rank (level + 1) =
        zeroPrefixCell rank level :=
    siblingPrefixCell_union_child
  have hdisjoint :
      Disjoint (siblingPrefixCell rank level)
        (zeroPrefixCell rank (level + 1)) :=
    siblingPrefixCell_disjoint
  change
    (decide (value ∈ zeroPrefixCell rank level) : Bool).toNat =
      (decide (value ∈ siblingPrefixCell rank level) : Bool).toNat +
        (decide
          (value ∈ zeroPrefixCell rank (level + 1)) : Bool).toNat
  have hmembership :
      value ∈ zeroPrefixCell rank level ↔
        value ∈ siblingPrefixCell rank level ∨
          value ∈ zeroPrefixCell rank (level + 1) := by
    rw [← hunion]
    simp
  by_cases hsibling : value ∈ siblingPrefixCell rank level
  · have hchild : value ∉ zeroPrefixCell rank (level + 1) :=
      Finset.disjoint_left.mp hdisjoint hsibling
    simp [hmembership, hsibling, hchild]
  · by_cases hchild : value ∈ zeroPrefixCell rank (level + 1)
    · simp [hmembership, hsibling, hchild]
    · simp [hmembership, hsibling, hchild]

/-- Exact `parent = 2 * child + (sibling - child)` recurrence. -/
theorem toeplitzPrefixCount_recurrence
    {Index : Type} [DecidableEq Index]
    {rank level : ℕ}
    (active : Finset Index) (label : Index → BinaryVector rank)
    (seed : ToeplitzSeed rank) :
    (toeplitzCellCount active label
        (zeroPrefixCell rank level) seed : ℤ) =
      2 * (toeplitzCellCount active label
        (zeroPrefixCell rank (level + 1)) seed : ℤ) +
      ((toeplitzCellCount active label
          (siblingPrefixCell rank level) seed : ℤ) -
        (toeplitzCellCount active label
          (zeroPrefixCell rank (level + 1)) seed : ℤ)) := by
  have hadd :=
    toeplitzPrefixCount_add (level := level) active label seed
  omega

end NearCubicWires.SupplierToeplitz
