import Proof.Wire_3_5.CompilerStackLift
import Proof.Foundations.SupplierPrinter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPrinter

variable {ZL ZR : Type} {R C : ℕ}

/-- The left half-scores evaluated at the enumerated rows: `A[a,i] = a_i(z_L(a))`. -/
def halfLeft (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) : IntMatrix R S.length :=
  fun r i => S[i.1].2.left (rowOf r)

/-- The right half-scores evaluated at the enumerated columns: `B[i,b] = b_i(z_R(b))`. -/
def halfRight (S : SignedOccurrenceList ZL ZR) (colOf : Fin C → ZR) : IntMatrix S.length C :=
  fun i c => S[i.1].2.right (colOf c)

/-- The signed occurrence weights `v_i`. -/
def occWeight (S : SignedOccurrenceList ZL ZR) : Fin S.length → ℤ := fun i => S[i.1].1

theorem exactCut_zero_toNat (a b : ℤ) : (((exactCut 0 (a + b)).toNat : ℕ) : ℤ) = bitZ (decide (a + b = 0)) := by
  unfold exactCut bitZ
  by_cases h : a + b = 0
  · simp [h]
  · have h' : ¬(0 : ℤ) = a + b := fun e => h e.symm
    simp [h, h']

/-- **The table is an exact-score table** of the evaluated half-scores (target `0`): the base printer's input. -/
theorem value_eq_exactScore (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) (colOf : Fin C → ZR)
    (r : Fin R) (c : Fin C) :
    S.value (rowOf r) (colOf c) =
      weightedExactScore (halfLeft S rowOf) (halfRight S colOf) (fun _ => 0) (occWeight S) r c := by
  unfold weightedExactScore halfLeft halfRight occWeight SignedOccurrenceList.value
  simp only [exactCut_zero_toNat]
  rw [← Fin.sum_univ_fun_getElem S (fun p => p.1 * bitZ (p.2.holds (rowOf r) (colOf c)))]
  rfl

theorem value_eq_successiveDominance (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) (colOf : Fin C → ZR)
    (r : Fin R) (c : Fin C) :
    S.value (rowOf r) (colOf c) =
      weightedDominance (fun r i => 0 - halfLeft S rowOf r i) (halfRight S colOf) (occWeight S) r c -
        weightedDominance (fun r i => 0 + 1 - halfLeft S rowOf r i) (halfRight S colOf) (occWeight S) r c := by
  rw [value_eq_exactScore, weightedExactScore_eq_successiveDominance]

/-! ## The `m = 2s` cuts as one weighted-dominance table -/

/-- The row side of cut `j = (i, θ)`: `A[a,j] = θ − a_i(z_L(a))`, so `A[a,j] ≤ B[j,b]` iff `E_i ≥ θ`. -/
def cutLeft (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) : IntMatrix R (S.length * 2) :=
  fun r g => ((finProdFinEquiv.symm g).2.val : ℤ) - halfLeft S rowOf r (finProdFinEquiv.symm g).1

/-- The column side of cut `j = (i, θ)`: `B[j,b] = b_i(z_R(b))`. -/
def cutRight (S : SignedOccurrenceList ZL ZR) (colOf : Fin C → ZR) : IntMatrix (S.length * 2) C :=
  fun g c => halfRight S colOf (finProdFinEquiv.symm g).1 c

/-- The cut weight: `ω_{(i,0)} = v_i`, `ω_{(i,1)} = −v_i`. -/
def cutWeight (S : SignedOccurrenceList ZL ZR) : Fin (S.length * 2) → ℤ :=
  fun g => if (finProdFinEquiv.symm g).2.val = 0 then occWeight S (finProdFinEquiv.symm g).1
    else -occWeight S (finProdFinEquiv.symm g).1

theorem dec_toNat (p : Prop) [Decidable p] : (((decide p).toNat : ℕ) : ℤ) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem cut_pair (v a b : ℤ) :
    v * ((decide ((0 : ℤ) - a ≤ b)).toNat : ℤ) + -v * ((decide ((1 : ℤ) - a ≤ b)).toNat : ℤ) =
      v * bitZ (decide (a + b = 0)) := by
  rw [dec_toNat, dec_toNat]
  unfold bitZ
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem value_eq_weightedDominance (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) (colOf : Fin C → ZR)
    (r : Fin R) (c : Fin C) :
    S.value (rowOf r) (colOf c) = weightedDominance (cutLeft S rowOf) (cutRight S colOf) (cutWeight S) r c := by
  rw [value_eq_exactScore]
  unfold weightedDominance weightedExactScore
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_two]
  simp only [cutLeft, cutRight, cutWeight, Equiv.symm_apply_apply, Fin.val_zero, Fin.val_one,
    Nat.cast_zero, Nat.cast_one, if_true, one_ne_zero, if_false, exactCut_zero_toNat]
  exact (cut_pair _ _ _).symm

theorem value_eq_B3_split (S : SignedOccurrenceList ZL ZR) (rowOf : Fin R → ZL) (colOf : Fin C → ZR)
    (bucketSize : ℕ) (r : Fin R) (c : Fin C) :
    S.value (rowOf r) (colOf c) =
      sameBucketContribution (stableBucketedDominanceLayout (cutLeft S rowOf) (cutRight S colOf) bucketSize)
          (cutWeight S) r c +
        signedBooleanProduct
          (reindexedLaterBucketLeft (stableBucketedDominanceLayout (cutLeft S rowOf) (cutRight S colOf) bucketSize)
            (cutWeight S))
          (reindexedLaterBucketRight (stableBucketedDominanceLayout (cutLeft S rowOf) (cutRight S colOf) bucketSize))
          r c := by
  rw [value_eq_weightedDominance, weightedDominance_eq_stable_same_add_later, reindexedLaterBucketProduct_eq]

/-! ## The score envelope of a stacked equation -/

theorem abs_add_mul_le (x y H V W : ℤ) (hH : 0 ≤ H) (hx : |x| ≤ V) (hy : |y| ≤ W) :
    |x + H * y| ≤ V + H * W := by
  calc |x + H * y| ≤ |x| + |H * y| := abs_add_le _ _
    _ = |x| + H * |y| := by rw [abs_mul, abs_of_nonneg hH]
    _ ≤ V + H * W := by gcongr

theorem stack_left_abs_le (H V : ℤ) (hH : 0 ≤ H) (Es : List (SeparatedEquation ZL ZR)) (zl : ZL)
    (hV : ∀ E ∈ Es, |E.left zl| ≤ V) :
    |(stackEquations H Es).left zl| ≤ V * ∑ j ∈ Finset.range Es.length, H ^ j := by
  induction Es with
  | nil => simp [stackEquations]
  | cons E Es ih =>
    have ih' := ih (fun E' hE' => hV E' (List.mem_cons_of_mem _ hE'))
    rw [List.length_cons, Finset.sum_range_succ', mul_add, pow_zero, mul_one]
    have hsum : V * ∑ j ∈ Finset.range Es.length, H ^ (j + 1) = H * (V * ∑ j ∈ Finset.range Es.length, H ^ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum, add_comm (H * _)]
    exact abs_add_mul_le _ _ H V _ hH (hV E List.mem_cons_self) ih'

/-- The stacked right half-score envelope. -/
theorem stack_right_abs_le (H V : ℤ) (hH : 0 ≤ H) (Es : List (SeparatedEquation ZL ZR)) (zr : ZR)
    (hV : ∀ E ∈ Es, |E.right zr| ≤ V) :
    |(stackEquations H Es).right zr| ≤ V * ∑ j ∈ Finset.range Es.length, H ^ j := by
  induction Es with
  | nil => simp [stackEquations]
  | cons E Es ih =>
    have ih' := ih (fun E' hE' => hV E' (List.mem_cons_of_mem _ hE'))
    rw [List.length_cons, Finset.sum_range_succ', mul_add, pow_zero, mul_one]
    have hsum : V * ∑ j ∈ Finset.range Es.length, H ^ (j + 1) = H * (V * ∑ j ∈ Finset.range Es.length, H ^ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum, add_comm (H * _)]
    exact abs_add_mul_le _ _ H V _ hH (hV E List.mem_cons_self) ih'

end NearCubicWires.WireExponent3_5.Compiler
