import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Coset.Basic

/-!
# Explicit binary Toeplitz hashing

This module supplies the finite, executable pairwise-independent hash family
used by the supplier construction.  The diagonal seed has `2 * rank - 1`
bits, the translation has `rank` bits, and no finite-field representation or
choice of an irreducible polynomial is hidden in the implementation.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierToeplitzCore

abbrev 𝔽₂ := ZMod 2
abbrev BitVec (rank : ℕ) := Fin rank → 𝔽₂
abbrev ToeplitzDiagonal (rank : ℕ) :=
  (Fin rank → 𝔽₂) × (Fin (rank - 1) → 𝔽₂)
abbrev ToeplitzSeed (rank : ℕ) :=
  ToeplitzDiagonal rank × BitVec rank

/-- The first coordinate stores the main and lower diagonals; the second
stores strict upper diagonals in increasing distance from the main one. -/
def toeplitzEntry {rank : ℕ} (diagonal : ToeplitzDiagonal rank)
    (row column : Fin rank) : 𝔽₂ :=
  if h : column.val ≤ row.val then
    diagonal.1 ⟨row.val - column.val, by omega⟩
  else
    diagonal.2 ⟨column.val - row.val - 1, by omega⟩

def toeplitzApply {rank : ℕ} (diagonal : ToeplitzDiagonal rank)
    (input : BitVec rank) : BitVec rank :=
  fun row => ∑ column : Fin rank,
    toeplitzEntry diagonal row column * input column

def toeplitzHash {rank : ℕ} (input : BitVec rank)
    (seed : ToeplitzSeed rank) : BitVec rank :=
  toeplitzApply seed.1 input + seed.2

@[simp] theorem toeplitzHash_apply {rank : ℕ} (input : BitVec rank)
    (seed : ToeplitzSeed rank) (row : Fin rank) :
    toeplitzHash input seed row =
      toeplitzApply seed.1 input row + seed.2 row :=
  rfl

/-- Restrict the diagonal seed to the `rank` diagonals meeting one fixed input
column.  `values row` is placed on the diagonal through `(row, pivot)`;
diagonals not meeting that column are set to zero. -/
def pivotDiagonal {rank : ℕ} (pivot : Fin rank)
    (values : BitVec rank) : ToeplitzDiagonal rank :=
  (fun lower =>
      if h : pivot.val + lower.val < rank then
        values ⟨pivot.val + lower.val, h⟩
      else
        0,
    fun upper =>
      if h : upper.val < pivot.val then
        values ⟨pivot.val - upper.val - 1, by omega⟩
      else
        0)

@[simp] theorem pivotDiagonal_lower {rank : ℕ} (pivot : Fin rank)
    (values : BitVec rank) (lower : Fin rank) :
    (pivotDiagonal pivot values).1 lower =
      if h : pivot.val + lower.val < rank then
        values ⟨pivot.val + lower.val, h⟩
      else
        0 :=
  rfl

@[simp] theorem pivotDiagonal_upper {rank : ℕ} (pivot : Fin rank)
    (values : BitVec rank) (upper : Fin (rank - 1)) :
    (pivotDiagonal pivot values).2 upper =
      if h : upper.val < pivot.val then
        values ⟨pivot.val - upper.val - 1, by omega⟩
      else
        0 :=
  rfl

def pivotDiagonalLinear {rank : ℕ} (pivot : Fin rank) :
    BitVec rank →ₗ[𝔽₂] ToeplitzDiagonal rank where
  toFun := pivotDiagonal pivot
  map_add' left right := by
    ext coordinate <;>
      simp only [pivotDiagonal, Prod.fst_add, Prod.snd_add,
        Pi.add_apply]
    · split <;> rfl
    · split <;> rfl
  map_smul' scalar values := by
    ext coordinate <;>
      simp only [pivotDiagonal, Pi.smul_apply, smul_eq_mul]
    · by_cases h : pivot.val + coordinate.val < rank <;> simp [h]
    · by_cases h : coordinate.val < pivot.val <;> simp [h]

def toeplitzApplyLinear {rank : ℕ} (input : BitVec rank) :
    ToeplitzDiagonal rank →ₗ[𝔽₂] BitVec rank where
  toFun := fun diagonal => toeplitzApply diagonal input
  map_add' left right := by
    funext row
    simp only [toeplitzApply, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro column _
    unfold toeplitzEntry
    split <;> simp [add_mul]
  map_smul' scalar diagonal := by
    funext row
    simp only [toeplitzApply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro column _
    unfold toeplitzEntry
    split <;> simp [mul_assoc]

def toeplitzInputLinear {rank : ℕ}
    (diagonal : ToeplitzDiagonal rank) :
    BitVec rank →ₗ[𝔽₂] BitVec rank where
  toFun := toeplitzApply diagonal
  map_add' left right := by
    funext row
    simp only [toeplitzApply, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext row
    simp only [toeplitzApply, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro column _
    simp only [RingHom.id_apply]
    ac_rfl

/-- The square restricted map whose determinant witnesses that every output
can be obtained from the Toeplitz diagonal whenever `input pivot = 1`. -/
def pivotTransform {rank : ℕ} (input : BitVec rank)
    (pivot : Fin rank) : BitVec rank →ₗ[𝔽₂] BitVec rank :=
  (toeplitzApplyLinear input).comp (pivotDiagonalLinear pivot)

private theorem pivotDiagonal_single_entry_eq_zero_of_le
    {rank : ℕ} (pivot row column source : Fin rank)
    (hpivotSource : pivot.val ≤ source.val)
    (hrowColumn : row.val < column.val) :
    toeplitzEntry
        (pivotDiagonal pivot (Pi.single column (1 : 𝔽₂)))
        row source = 0 := by
  classical
  unfold toeplitzEntry
  by_cases hsourceRow : source.val ≤ row.val
  · simp only [dif_pos hsourceRow, pivotDiagonal_lower]
    by_cases hbound : pivot.val + (row.val - source.val) < rank
    · simp only [dif_pos hbound, Pi.single_apply]
      split
      · rename_i hequal
        have hvalues : pivot.val + (row.val - source.val) =
            column.val := by
          exact congrArg Fin.val hequal
        omega
      · rfl
    · simp [hbound]
  · simp only [dif_neg hsourceRow, pivotDiagonal_upper]
    by_cases hbound : source.val - row.val - 1 < pivot.val
    · simp only [dif_pos hbound, Pi.single_apply]
      split
      · rename_i hequal
        have hvalues : pivot.val -
              (source.val - row.val - 1) - 1 =
            column.val := by
          exact congrArg Fin.val hequal
        omega
      · rfl
    · simp [hbound]

private theorem pivotDiagonal_single_entry_pivot
    {rank : ℕ} (pivot row : Fin rank) :
    toeplitzEntry
        (pivotDiagonal pivot (Pi.single row (1 : 𝔽₂)))
        row pivot = 1 := by
  classical
  unfold toeplitzEntry
  by_cases hpivotRow : pivot.val ≤ row.val
  · simp only [dif_pos hpivotRow, pivotDiagonal_lower]
    have hbound : pivot.val + (row.val - pivot.val) < rank := by
      omega
    have hindex :
        (⟨pivot.val + (row.val - pivot.val), hbound⟩ : Fin rank) =
          row := by
      apply Fin.ext
      simp
      omega
    simp [hbound, hindex]
  · simp only [dif_neg hpivotRow, pivotDiagonal_upper]
    have hbound : pivot.val - row.val - 1 < pivot.val := by
      omega
    have hindex :
        (⟨pivot.val - (pivot.val - row.val - 1) - 1, by omega⟩ :
            Fin rank) = row := by
      apply Fin.ext
      simp
      omega
    simp [hbound, hindex]

private theorem pivotDiagonal_single_entry_eq_zero_of_lt
    {rank : ℕ} (pivot row source : Fin rank)
    (hpivotSource : pivot.val < source.val) :
    toeplitzEntry
        (pivotDiagonal pivot (Pi.single row (1 : 𝔽₂)))
        row source = 0 := by
  classical
  unfold toeplitzEntry
  by_cases hsourceRow : source.val ≤ row.val
  · simp only [dif_pos hsourceRow, pivotDiagonal_lower]
    have hbound : pivot.val + (row.val - source.val) < rank := by
      omega
    simp only [dif_pos hbound, Pi.single_apply]
    split
    · rename_i hequal
      have hvalues : pivot.val + (row.val - source.val) =
          row.val := by
        exact congrArg Fin.val hequal
      omega
    · rfl
  · simp only [dif_neg hsourceRow, pivotDiagonal_upper]
    by_cases hbound : source.val - row.val - 1 < pivot.val
    · simp only [dif_pos hbound, Pi.single_apply]
      split
      · rename_i hequal
        have hvalues : pivot.val -
              (source.val - row.val - 1) - 1 =
            row.val := by
          exact congrArg Fin.val hequal
        omega
      · rfl
    · simp [hbound]

theorem pivotTransform_matrix_above_eq_zero
    {rank : ℕ} (input : BitVec rank) (pivot row column : Fin rank)
    (hminimal : ∀ source : Fin rank,
      source.val < pivot.val → input source = 0)
    (hrowColumn : row.val < column.val) :
    LinearMap.toMatrix' (pivotTransform input pivot) row column = 0 := by
  classical
  rw [LinearMap.toMatrix'_apply]
  simp only [pivotTransform, LinearMap.comp_apply,
    toeplitzApplyLinear]
  change toeplitzApply
    (pivotDiagonal pivot (Pi.single column (1 : 𝔽₂))) input row = 0
  unfold toeplitzApply
  apply Finset.sum_eq_zero
  intro source _
  by_cases hsource : source.val < pivot.val
  · rw [hminimal source hsource, mul_zero]
  · rw [pivotDiagonal_single_entry_eq_zero_of_le
      pivot row column source (by omega) hrowColumn, zero_mul]

theorem pivotTransform_matrix_diagonal
    {rank : ℕ} (input : BitVec rank) (pivot row : Fin rank)
    (hpivot : input pivot = 1)
    (hminimal : ∀ source : Fin rank,
      source.val < pivot.val → input source = 0) :
    LinearMap.toMatrix' (pivotTransform input pivot) row row = 1 := by
  classical
  rw [LinearMap.toMatrix'_apply]
  simp only [pivotTransform, LinearMap.comp_apply,
    toeplitzApplyLinear]
  change toeplitzApply
    (pivotDiagonal pivot (Pi.single row (1 : 𝔽₂))) input row = 1
  unfold toeplitzApply
  rw [Finset.sum_eq_single pivot]
  · rw [pivotDiagonal_single_entry_pivot, one_mul, hpivot]
  · intro source _ hsource
    by_cases hsourcePivot : source.val < pivot.val
    · rw [hminimal source hsourcePivot, mul_zero]
    · have hpivotSource : pivot.val < source.val := by
        have hne : source.val ≠ pivot.val := by
          intro hequal
          apply hsource
          exact Fin.ext hequal
        omega
      rw [pivotDiagonal_single_entry_eq_zero_of_lt
        pivot row source hpivotSource, zero_mul]
  · simp

theorem pivotTransform_matrix_det
    {rank : ℕ} (input : BitVec rank) (pivot : Fin rank)
    (hpivot : input pivot = 1)
    (hminimal : ∀ source : Fin rank,
      source.val < pivot.val → input source = 0) :
    (LinearMap.toMatrix' (pivotTransform input pivot)).det = 1 := by
  classical
  let matrix := LinearMap.toMatrix' (pivotTransform input pivot)
  have hlower : matrix.BlockTriangular OrderDual.toDual := by
    intro row column habove
    exact pivotTransform_matrix_above_eq_zero
      input pivot row column hminimal habove
  rw [Matrix.det_of_lowerTriangular matrix hlower]
  apply Finset.prod_eq_one
  intro row _
  exact pivotTransform_matrix_diagonal
    input pivot row hpivot hminimal

theorem pivotTransform_surjective
    {rank : ℕ} (input : BitVec rank) (pivot : Fin rank)
    (hpivot : input pivot = 1)
    (hminimal : ∀ source : Fin rank,
      source.val < pivot.val → input source = 0) :
    Function.Surjective (pivotTransform input pivot) := by
  classical
  have hdet : IsUnit (pivotTransform input pivot).det := by
    rw [← LinearMap.det_toMatrix']
    rw [pivotTransform_matrix_det input pivot hpivot hminimal]
    exact isUnit_one
  let equivalence :=
    LinearMap.equivOfIsUnitDet
      (f := pivotTransform input pivot) hdet
  intro output
  refine ⟨equivalence.symm output, ?_⟩
  have happly := equivalence.apply_symm_apply output
  simpa only [equivalence, LinearMap.equivOfIsUnitDet_apply] using happly

theorem toeplitzApply_surjective_of_pivot
    {rank : ℕ} (input : BitVec rank) (pivot : Fin rank)
    (hpivot : input pivot = 1)
    (hminimal : ∀ source : Fin rank,
      source.val < pivot.val → input source = 0) :
    Function.Surjective (fun diagonal : ToeplitzDiagonal rank =>
      toeplitzApply diagonal input) := by
  intro output
  obtain ⟨values, hvalues⟩ :=
    pivotTransform_surjective input pivot hpivot hminimal output
  refine ⟨pivotDiagonal pivot values, ?_⟩
  exact hvalues

private theorem f2_eq_one_of_ne_zero (value : 𝔽₂)
    (hvalue : value ≠ 0) : value = 1 := by
  have hvalNonzero : value.val ≠ 0 :=
    (ZMod.val_eq_zero value).not.mpr hvalue
  have hval : value.val = 1 := by
    have hlt := value.val_lt
    omega
  exact (ZMod.val_eq_one (by omega) value).mp hval

theorem exists_first_one {rank : ℕ} (input : BitVec rank)
    (hinput : input ≠ 0) :
    ∃ pivot : Fin rank,
      input pivot = 1 ∧
      ∀ source : Fin rank,
        source.val < pivot.val → input source = 0 := by
  classical
  let support : Finset (Fin rank) :=
    Finset.univ.filter fun coordinate => input coordinate ≠ 0
  have hsupport : support.Nonempty := by
    by_contra hempty
    apply hinput
    funext coordinate
    change input coordinate = (0 : 𝔽₂)
    by_contra hcoordinate
    apply hempty
    refine ⟨coordinate, ?_⟩
    simp only [support, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hcoordinate
  let pivot := support.min' hsupport
  have hpivotMem : pivot ∈ support :=
    support.min'_mem hsupport
  refine ⟨pivot, ?_, ?_⟩
  · apply f2_eq_one_of_ne_zero
    simpa [support] using hpivotMem
  · intro source hsource
    by_contra hsourceNonzero
    have hsourceMem : source ∈ support := by
      simp [support, hsourceNonzero]
    have hpivotLe : pivot ≤ source :=
      support.min'_le source hsourceMem
    omega

theorem toeplitzApply_surjective {rank : ℕ} (input : BitVec rank)
    (hinput : input ≠ 0) :
    Function.Surjective (fun diagonal : ToeplitzDiagonal rank =>
      toeplitzApply diagonal input) := by
  obtain ⟨pivot, hpivot, hminimal⟩ :=
    exists_first_one input hinput
  exact toeplitzApply_surjective_of_pivot
    input pivot hpivot hminimal

theorem toeplitzHashPair_surjective
    {rank : ℕ} (left right : BitVec rank)
    (hdistinct : left ≠ right) :
    Function.Surjective (fun seed : ToeplitzSeed rank =>
      (toeplitzHash left seed, toeplitzHash right seed)) := by
  intro output
  have hdifference : left - right ≠ 0 :=
    sub_ne_zero.mpr hdistinct
  obtain ⟨diagonal, hdiagonal⟩ :=
    toeplitzApply_surjective (left - right) hdifference
      (output.1 - output.2)
  let translation : BitVec rank :=
    output.1 - toeplitzApply diagonal left
  refine ⟨(diagonal, translation), ?_⟩
  apply Prod.ext
  · funext row
    simp [toeplitzHash, translation]
  · have hlinear :
        toeplitzApply diagonal left -
            toeplitzApply diagonal right =
          output.1 - output.2 := by
      calc
        toeplitzApply diagonal left -
              toeplitzApply diagonal right =
            toeplitzApply diagonal (left - right) :=
          ((toeplitzInputLinear diagonal).map_sub left right).symm
        _ = output.1 - output.2 := hdiagonal
    funext row
    have hrow := congrFun hlinear row
    simp only [toeplitzHash_apply, translation, Pi.sub_apply]
    simp only [Pi.sub_apply] at hrow
    calc
      toeplitzApply diagonal right row +
            (output.1 row - toeplitzApply diagonal left row) =
          output.1 row -
            (toeplitzApply diagonal left row -
              toeplitzApply diagonal right row) := by
        abel
      _ = output.1 row - (output.1 row - output.2 row) := by
        rw [hrow]
      _ = output.2 row := by
        abel

def toeplitzHashLinear {rank : ℕ} (input : BitVec rank) :
    ToeplitzSeed rank →ₗ[𝔽₂] BitVec rank where
  toFun := toeplitzHash input
  map_add' left right := by
    funext row
    have hmap :=
      (toeplitzApplyLinear input).map_add left.1 right.1
    have hrow := congrFun hmap row
    change
      toeplitzApply (left.1 + right.1) input row =
        (toeplitzApply left.1 input +
          toeplitzApply right.1 input) row at hrow
    change
      toeplitzApply (left.1 + right.1) input row +
          (left.2 + right.2) row =
        (toeplitzApply left.1 input + left.2) row +
          (toeplitzApply right.1 input + right.2) row
    rw [hrow]
    simp only [Pi.add_apply]
    abel
  map_smul' scalar seed := by
    funext row
    have hmap :=
      (toeplitzApplyLinear input).map_smul scalar seed.1
    have hrow := congrFun hmap row
    change
      toeplitzApply (scalar • seed.1) input row =
        (scalar • toeplitzApply seed.1 input) row at hrow
    change
      toeplitzApply (scalar • seed.1) input row +
          (scalar • seed.2) row =
        scalar •
          (toeplitzApply seed.1 input + seed.2) row
    rw [hrow]
    simp only [Pi.smul_apply, Pi.add_apply, smul_add]

def toeplitzHashPairLinear {rank : ℕ}
    (left right : BitVec rank) :
    ToeplitzSeed rank →ₗ[𝔽₂] BitVec rank × BitVec rank :=
  (toeplitzHashLinear left).prod (toeplitzHashLinear right)

private def equalityFiberEquivSetFiber
    {Domain Codomain : Type*} (function : Domain → Codomain)
    (output : Codomain) :
    {input // function input = output} ≃
      function ⁻¹' ({output} : Set Codomain) :=
  Equiv.setCongr (by
    ext input
    change (function input = output ↔ function input = output)
    rfl)

/-- A surjective additive map splits, as a finite set, into its output and one
kernel fiber.  The equivalence is used only in proofs; all hashing operations
above remain directly executable. -/
noncomputable def surjectiveAddHomTotalEquiv
    {Domain Codomain : Type*}
    [AddGroup Domain] [AddGroup Codomain]
    (homomorphism : Domain →+ Codomain)
    (hsurjective : Function.Surjective homomorphism) :
    Domain ≃ Codomain × homomorphism.ker :=
  (Equiv.sigmaFiberEquiv homomorphism).symm |>.trans
    (Equiv.sigmaEquivProdOfEquiv fun output =>
      (equalityFiberEquivSetFiber homomorphism output).trans
        (AddMonoidHom.fiberEquivKerOfSurjective
          hsurjective output))

theorem surjectiveAddHomTotalEquiv_fst
    {Domain Codomain : Type*}
    [AddGroup Domain] [AddGroup Codomain]
    (homomorphism : Domain →+ Codomain)
    (hsurjective : Function.Surjective homomorphism)
    (input : Domain) :
    (surjectiveAddHomTotalEquiv homomorphism hsurjective input).1 =
      homomorphism input :=
  rfl

theorem sum_surjectiveAddHom
    {Domain Codomain : Type*}
    [AddGroup Domain] [AddGroup Codomain]
    [Fintype Domain] [Fintype Codomain] [DecidableEq Codomain]
    (homomorphism : Domain →+ Codomain)
    (hsurjective : Function.Surjective homomorphism)
    (value : Codomain → ℝ) :
    ∑ input : Domain, value (homomorphism input) =
      Fintype.card homomorphism.ker *
        ∑ output : Codomain, value output := by
  classical
  calc
    (∑ input : Domain, value (homomorphism input)) =
        ∑ output :
            Codomain × homomorphism.ker,
          value output.1 := by
      simpa only [surjectiveAddHomTotalEquiv_fst] using
        (surjectiveAddHomTotalEquiv
          homomorphism hsurjective).sum_comp
            (fun output => value output.1)
    _ = Fintype.card homomorphism.ker *
        ∑ output : Codomain, value output := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Finset.mul_sum]

theorem card_surjectiveAddHom
    {Domain Codomain : Type*}
    [AddGroup Domain] [AddGroup Codomain]
    [Fintype Domain] [Fintype Codomain] [DecidableEq Codomain]
    (homomorphism : Domain →+ Codomain)
    (hsurjective : Function.Surjective homomorphism) :
    Fintype.card Domain =
      Fintype.card Codomain * Fintype.card homomorphism.ker := by
  classical
  calc
    Fintype.card Domain =
        Fintype.card (Codomain × homomorphism.ker) :=
      Fintype.card_congr
        (surjectiveAddHomTotalEquiv homomorphism hsurjective)
    _ = Fintype.card Codomain *
        Fintype.card homomorphism.ker :=
      Fintype.card_prod Codomain homomorphism.ker

theorem sum_toeplitzHash_pair
    {rank : ℕ} (left right : BitVec rank)
    (hdistinct : left ≠ right)
    (value : BitVec rank → BitVec rank → ℝ) :
    ∑ seed : ToeplitzSeed rank,
        value (toeplitzHash left seed) (toeplitzHash right seed) =
      Fintype.card
          (toeplitzHashPairLinear left right).toAddMonoidHom.ker *
        ∑ leftOutput : BitVec rank,
          ∑ rightOutput : BitVec rank,
            value leftOutput rightOutput := by
  let pairHomomorphism :=
    (toeplitzHashPairLinear left right).toAddMonoidHom
  have hsurjective : Function.Surjective pairHomomorphism := by
    exact toeplitzHashPair_surjective left right hdistinct
  change
    (∑ seed : ToeplitzSeed rank,
      value (pairHomomorphism seed).1
        (pairHomomorphism seed).2) =
      Fintype.card pairHomomorphism.ker *
        ∑ leftOutput : BitVec rank,
          ∑ rightOutput : BitVec rank,
            value leftOutput rightOutput
  rw [sum_surjectiveAddHom pairHomomorphism hsurjective
    (fun output => value output.1 output.2)]
  rw [Fintype.sum_prod_type]

theorem card_toeplitzSeed_eq_pairOutput_mul_kernel
    {rank : ℕ} (left right : BitVec rank)
    (hdistinct : left ≠ right) :
    Fintype.card (ToeplitzSeed rank) =
      Fintype.card (BitVec rank × BitVec rank) *
        Fintype.card
          (toeplitzHashPairLinear left right).toAddMonoidHom.ker := by
  let pairHomomorphism :=
    (toeplitzHashPairLinear left right).toAddMonoidHom
  have hsurjective : Function.Surjective pairHomomorphism := by
    exact toeplitzHashPair_surjective left right hdistinct
  exact card_surjectiveAddHom pairHomomorphism hsurjective

/-- One output is uniform for every fixed input because the translation is a
fresh `rank`-bit vector.  The diagonal is retained as the independent fiber. -/
def toeplitzHashEquiv {rank : ℕ} (input : BitVec rank) :
    ToeplitzSeed rank ≃ ToeplitzDiagonal rank × BitVec rank where
  toFun seed := (seed.1, toeplitzHash input seed)
  invFun output :=
    (output.1, output.2 - toeplitzApply output.1 input)
  left_inv seed := by
    ext <;> simp [toeplitzHash]
  right_inv output := by
    ext <;> simp [toeplitzHash]

theorem sum_toeplitzHash
    {rank : ℕ} (input : BitVec rank) (value : BitVec rank → ℝ) :
    ∑ seed : ToeplitzSeed rank, value (toeplitzHash input seed) =
      Fintype.card (ToeplitzDiagonal rank) *
        ∑ output : BitVec rank, value output := by
  calc
    (∑ seed : ToeplitzSeed rank, value (toeplitzHash input seed)) =
        ∑ output : ToeplitzDiagonal rank × BitVec rank,
          value output.2 :=
      (toeplitzHashEquiv input).sum_comp
        (fun output => value output.2)
    _ = Fintype.card (ToeplitzDiagonal rank) *
        ∑ output : BitVec rank, value output := by
      rw [Fintype.sum_prod_type]
      simp

theorem card_toeplitzSeed_eq_oneMultiplicity_mul_output
    (rank : ℕ) :
    Fintype.card (ToeplitzSeed rank) =
      Fintype.card (ToeplitzDiagonal rank) *
        Fintype.card (BitVec rank) := by
  exact Fintype.card_prod
    (ToeplitzDiagonal rank) (BitVec rank)

theorem card_bitVec (rank : ℕ) :
    Fintype.card (BitVec rank) = 2 ^ rank := by
  simp [BitVec, ZMod.card]

theorem card_toeplitzDiagonal (rank : ℕ) :
    Fintype.card (ToeplitzDiagonal rank) =
      2 ^ (rank + (rank - 1)) := by
  simp [ToeplitzDiagonal, Fintype.card_prod,
    ZMod.card, pow_add]

theorem card_toeplitzSeed (rank : ℕ) :
    Fintype.card (ToeplitzSeed rank) =
      2 ^ (2 * rank + (rank - 1)) := by
  rw [card_toeplitzSeed_eq_oneMultiplicity_mul_output,
    card_toeplitzDiagonal, card_bitVec]
  rw [← pow_add]
  congr 1
  omega

theorem card_toeplitzHashPair_kernel
    {rank : ℕ} (left right : BitVec rank)
    (hdistinct : left ≠ right) :
    Fintype.card
        (toeplitzHashPairLinear left right).toAddMonoidHom.ker =
      2 ^ (rank - 1) := by
  have hcard :=
    card_toeplitzSeed_eq_pairOutput_mul_kernel
      left right hdistinct
  rw [card_toeplitzSeed, Fintype.card_prod,
    card_bitVec] at hcard
  have hseed :
      2 ^ (2 * rank + (rank - 1)) =
        2 ^ (2 * rank) * 2 ^ (rank - 1) := by
    exact pow_add 2 (2 * rank) (rank - 1)
  have houtputs :
      2 ^ rank * 2 ^ rank = 2 ^ (2 * rank) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hseed, houtputs] at hcard
  exact Nat.eq_of_mul_eq_mul_left
    (pow_pos (by omega) (2 * rank)) hcard.symm

theorem sum_toeplitzHash_exact
    {rank : ℕ} (input : BitVec rank)
    (value : BitVec rank → ℝ) :
    ∑ seed : ToeplitzSeed rank, value (toeplitzHash input seed) =
      ((2 ^ (rank + (rank - 1)) : ℕ) : ℝ) *
        ∑ output : BitVec rank, value output := by
  rw [sum_toeplitzHash, card_toeplitzDiagonal]

theorem sum_toeplitzHash_pair_exact
    {rank : ℕ} (left right : BitVec rank)
    (hdistinct : left ≠ right)
    (value : BitVec rank → BitVec rank → ℝ) :
    ∑ seed : ToeplitzSeed rank,
        value (toeplitzHash left seed) (toeplitzHash right seed) =
      ((2 ^ (rank - 1) : ℕ) : ℝ) *
        ∑ leftOutput : BitVec rank,
          ∑ rightOutput : BitVec rank,
            value leftOutput rightOutput := by
  rw [sum_toeplitzHash_pair left right hdistinct,
    card_toeplitzHashPair_kernel left right hdistinct]

end NearCubicWires.SupplierToeplitzCore
