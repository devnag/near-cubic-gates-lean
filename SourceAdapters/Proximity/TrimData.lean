import SourceAdapters.Joins.TrimVerifier
import SourceAdapters.Proximity.TrimOrder

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the exact flat table loaded by the trimming
machine, its record counts, and proof-address membership.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Joins

/-- Complete coin-major/query-major table, with repetitions retained. -/
def queries {n : ℕ} (V : ThreeQueryVerifier n) : List (SignedQuery n) :=
  (List.ofFn fun coins : Fin (2 ^ V.randomBits) =>
    List.ofFn fun j : Fin 3 => V.clause coins j).flatten

/-- Three numeric fields for every original query. -/
def fields {n : ℕ} (V : ThreeQueryVerifier n) : List ℕ :=
  (queries V).flatMap trimQueryFields

theorem queryFields_length {n : ℕ} (q : SignedQuery n) :
    (trimQueryFields q).length = 3 := by
  cases h : q.address <;> simp [trimQueryFields, h]

theorem flatFields_length {n : ℕ} (qs : List (SignedQuery n)) :
    (qs.flatMap trimQueryFields).length = 3 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.flatMap_cons, List.length_append, queryFields_length,
      ih, List.length_cons]
    omega

theorem queries_length {n : ℕ} (V : ThreeQueryVerifier n) :
    (queries V).length = 3 * 2 ^ V.randomBits := by
  simp [queries, List.length_flatten, List.map_ofFn, Function.comp_def, Nat.mul_comm]

theorem fields_length {n : ℕ} (V : ThreeQueryVerifier n) :
    (fields V).length = 9 * 2 ^ V.randomBits := by
  rw [fields, flatFields_length, queries_length]
  omega

theorem requestFields_eq {n : ℕ} (V : ThreeQueryVerifier n) :
    trimRequestFields ⟨n, V⟩ = [n, V.randomBits] ++ fields V := by
  simp only [trimRequestFields, fields, queries, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

theorem requestWord_eq {n : ℕ} (V : ThreeQueryVerifier n) :
    trimRequestWord ⟨n, V⟩ = natWord n ++ natWord V.randomBits ++
      (fields V).flatMap natWord := by
  rw [trimRequestWord, requestFields_eq]
  simp [List.append_assoc]


/-- Input-coordinate queries contribute no source-proof address. -/
def queryProofValues {n : ℕ} (q : SignedQuery n) : List ℕ :=
  match q.address with
  | .inl _ => []
  | .inr address => [address]

def proofValues {n : ℕ} (V : ThreeQueryVerifier n) : List ℕ :=
  (queries V).flatMap queryProofValues

theorem queryProofValues_mem {n : ℕ} (q : SignedQuery n) (a : ℕ) :
    a ∈ queryProofValues q ↔ a ∈ proofAddressSet q := by
  cases h : q.address <;> simp [queryProofValues, proofAddressSet, h]

theorem mem_queries {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) :
    q ∈ queries V ↔ ∃ coins j, V.clause coins j = q := by
  constructor
  · intro h
    obtain ⟨qs, hqs, hq⟩ := List.mem_flatten.mp h
    obtain ⟨coins, rfl⟩ := List.mem_ofFn.mp hqs
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hq
    exact ⟨coins, j, hj⟩
  · rintro ⟨coins, j, h⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨coins, rfl⟩,
      List.mem_ofFn.mpr ⟨j, h⟩⟩

theorem proofValues_mem {n : ℕ} (V : ThreeQueryVerifier n) (a : ℕ) :
    a ∈ proofValues V ↔ a ∈ usedProofAddresses V := by
  simp only [proofValues, List.mem_flatMap, mem_queries, queryProofValues_mem,
    usedProofAddresses, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, ⟨coins, j, rfl⟩, h⟩
    exact ⟨coins, j, h⟩
  · rintro ⟨coins, j, h⟩
    exact ⟨_, ⟨coins, j, rfl⟩, h⟩

theorem proofValues_toFinset {n : ℕ} (V : ThreeQueryVerifier n) :
    (proofValues V).toFinset = usedProofAddresses V := by
  ext a
  simpa using proofValues_mem V a

theorem proofValues_sorted {n : ℕ} (V : ThreeQueryVerifier n) :
    (proofValues V).toFinset.sort (· ≤ ·) = trimSortedAddresses ⟨n, V⟩ := by
  rw [proofValues_toFinset]
  rfl

end NearCubicGates.Adapters.Proximity.Trim
