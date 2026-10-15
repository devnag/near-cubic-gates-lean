import Proof.Supplier.RowTupleCandidate

/-! The actual binary enumeration order is a permutation of A.12's list
expansion. Equal monomial values and equal resulting terms stay repeated. -/
namespace NearCubicWires.RepairOrdinary.RowTupleTerms
open RowTupleSubsets RowTupleDigits SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem map_sublistsLen {α β : Type} (f : α→β) (xs : List α) (k : ℕ) :
    (xs.sublistsLen k).map (List.map f)=(xs.map f).sublistsLen k := by
  induction xs generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.sublistsLen_succ_cons,List.map_map,Function.comp_def,←ih]

def fetch {α : Type} (ms : List (List α)) (i : ℕ) : List α := (ms[i]?).getD []
def selectedMonomials {α : Type} (ms : List (List α)) (ds : List ℕ) := ds.map (fetch ms)

theorem fetch_range {α : Type} (ms : List (List α)) : (List.range ms.length).map (fetch ms)=ms := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [fetch,hj]

theorem monomials_perm {α : Type} (ms : List (List α)) (k : ℕ) :
    ((selected (digitWidth ms.length) ms.length k).map (selectedMonomials ms)).Perm (ms.sublistsLen k) := by
  have h := (chosen_perm ms.length k).map (selectedMonomials ms)
  change ((selected (digitWidth ms.length) ms.length k).map (List.map (fetch ms))).Perm
    (((List.range ms.length).sublistsLen k).map (List.map (fetch ms))) at h
  rw [map_sublistsLen,fetch_range] at h
  exact h

def terms {α : Type} (Q : ℕ) (ms : List (List α)) : List (ℤ×List α) :=
  (List.range (min Q ms.length)).flatMap fun j=>
    (selected (digitWidth ms.length) ms.length (j+1)).map fun ds=>
      ((-2 : ℤ)^j,(selectedMonomials ms ds).flatten)

theorem terms_perm {α : Type} (Q : ℕ) (ms : List (List α)) :
    (terms Q ms).Perm (RowBinLift.terms Q ms) := by
  apply List.Perm.flatMap_left
  intro j _
  have h := (monomials_perm ms (j+1)).map (fun selected=>((-2 : ℤ)^j,selected.flatten))
  simpa only [List.map_map,Function.comp_def] using h

theorem terms_value {α : Type} (Q : ℕ) (ms : List (List α)) (p : α→Bool) :
    ((terms Q ms).map (fun t=>t.1*((t.2.all p).toNat : ℤ))).sum=
      binLift Q ((ms.map (fun m : List α=>(m.all p).toNat)).sum) := by
  rw [((terms_perm Q ms).map _).sum_eq]
  exact RowBinLift.terms_value Q ms p

def candidateCount (Q M : ℕ) : ℕ :=
  ((List.range (min Q M)).map (fun j=>(candidates (digitWidth M) (j+1)).length)).sum

theorem candidateCount_bound (Q M : ℕ) : candidateCount Q M≤Q*(2*max 1 M)^Q := by
  have hb : ∀ j∈List.range (min Q M),
      (candidates (digitWidth M) (j+1)).length≤(2*max 1 M)^Q := by
    intro j hj
    have hjQ : j+1≤Q := (Nat.succ_le_of_lt (List.mem_range.mp hj)).trans (Nat.min_le_left _ _)
    exact (candidate_count M (j+1)).trans (Nat.pow_le_pow_right (by omega) hjQ)
  have hsum : ∀ js : List ℕ,(∀ j∈js,(candidates (digitWidth M) (j+1)).length≤(2*max 1 M)^Q) →
      (js.map (fun j=>(candidates (digitWidth M) (j+1)).length)).sum≤js.length*(2*max 1 M)^Q := by
    intro js hjs
    induction js with
    | nil => simp
    | cons j js ih =>
      have ht := ih (fun a ha=>hjs a (List.mem_cons_of_mem _ ha))
      have hh := hjs j (by simp)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  exact (hsum _ hb).trans (by simp only [List.length_range]; exact Nat.mul_le_mul_right _ (Nat.min_le_left _ _))

end NearCubicWires.RepairOrdinary.RowTupleTerms
