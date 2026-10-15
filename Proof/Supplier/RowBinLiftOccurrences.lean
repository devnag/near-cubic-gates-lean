import Proof.Supplier.SupplierEstimator

/-! A.12's occurrence-preserving expansion in a concrete list order. Repeated
monomials remain repeated list entries. This is the semantic output of the
remaining physical subset enumerator, not a machine realization assumption. -/
namespace NearCubicWires.RepairOrdinary.RowBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem filter_sublistsLen {α : Type} (p : α → Bool) (xs : List α) (n : ℕ) :
    (xs.sublistsLen n).filter (fun ys => ys.all p)=(xs.filter p).sublistsLen n := by
  induction xs generalizing n with
  | nil => cases n <;> simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases hx : p x <;>
        simp [List.sublistsLen_succ_cons,List.filter_map,Function.comp_def,hx,ih]

theorem sum_toNat_eq_filter_length {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map (fun x => (p x).toNat)).sum=(xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx,ih,Nat.add_comm]

/-- Ascending subset size, then the standard `sublistsLen` order. The signed
coefficient is a scalar; its magnitude never creates additional occurrences. -/
def terms {α : Type} (Q : ℕ) (monomials : List (List α)) : List (ℤ × List α) :=
  (List.range (min Q monomials.length)).flatMap fun j =>
    (monomials.sublistsLen (j+1)).map fun selected => ((-2 : ℤ)^j,selected.flatten)

theorem sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum=∑ j ∈ Finset.range n,f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

theorem sum_flatMap {α M : Type} [AddMonoid M] (xs : List α) (f : α → List M) :
    (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem terms_length {α : Type} (Q : ℕ) (monomials : List (List α)) :
    (terms Q monomials).length=
      ∑ j ∈ Finset.range (min Q monomials.length),monomials.length.choose (j+1) := by
  simp [terms,List.length_flatMap,sum_range]

theorem subset_true_count {α : Type} (monomials : List (List α))
    (p : α → Bool) (j : ℕ) :
    ((monomials.sublistsLen j).map
      (fun selected => (selected.flatten.all p).toNat)).sum=
      ((monomials.map (fun m : List α => (m.all p).toNat)).sum).choose j := by
  have hall (selected : List (List α)) :
      selected.flatten.all p=selected.all (fun m : List α => m.all p) := by simp
  simp_rw [hall]
  rw [sum_toNat_eq_filter_length,filter_sublistsLen,List.length_sublistsLen,
    sum_toNat_eq_filter_length]

theorem terms_value {α : Type} (Q : ℕ) (monomials : List (List α))
    (p : α → Bool) :
    ((terms Q monomials).map (fun t => t.1*((t.2.all p).toNat : ℤ))).sum=
      binLift Q ((monomials.map (fun m : List α => (m.all p).toNat)).sum) := by
  have hs (j : ℕ) :
      ((monomials.sublistsLen (j+1)).map
        (fun selected => (-2 : ℤ)^j*((selected.flatten.all p).toNat : ℤ))).sum=
      (-2 : ℤ)^j*(((monomials.map (fun m : List α => (m.all p).toNat)).sum).choose (j+1) : ℤ) := by
    rw [List.sum_map_mul_left]
    congr 1
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
      congrArg (fun n : ℕ => (n : ℤ)) (subset_true_count monomials p (j+1))
  have hb := binLift_eq_fullOccurrenceSubsetExpansion Q
    (fun a (_ : Unit) (_ : Unit) => p a) monomials () ()
  simp only [trueOccurrenceSubsetCount_eq_choose,polynomialOccurrenceCount,
    exactMonomialValue] at hb
  rw [hb]
  simp only [terms,List.map_flatMap,List.map_map,Function.comp_def,
    sum_flatMap]
  simp_rw [hs]
  exact sum_range _ _

end NearCubicWires.RepairOrdinary.RowBinLift
