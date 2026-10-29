import SourceAdapters.Proximity.TrimSizes

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": every collected address is an explicitly supplied field;
record counts and all address bit lengths are bounded by the input word. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

theorem flatProofValues_length {n : ℕ} (qs : List (SignedQuery n)) :
    (qs.flatMap queryProofValues).length ≤ qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hq : (queryProofValues q).length ≤ 1 := by
      cases h : q.address <;> simp [queryProofValues, h]
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem proofValues_length_le {n : ℕ} (V : ThreeQueryVerifier n) :
    (proofValues V).length ≤ inputSize V := by
  have h1 := flatProofValues_length (queries V)
  have h2 := fields_count_le V
  rw [fields, flatFields_length] at h2
  exact h1.trans (by omega)

theorem proofValue_mem_fields {n : ℕ} (V : ThreeQueryVerifier n) {v : ℕ}
    (hv : v ∈ proofValues V) : v ∈ fields V := by
  obtain ⟨q, hq, hv⟩ := List.mem_flatMap.mp hv
  refine List.mem_flatMap.mpr ⟨q, hq, ?_⟩
  cases h : q.address <;> simp [queryProofValues, h] at hv
  subst v
  simp [trimQueryFields, h]

theorem proofValues_fit {C : Ctx} {n : ℕ} (V : ThreeQueryVerifier n)
    (hW : inputSize V + 2 ≤ C.Wd) {v : ℕ} (hv : v ∈ proofValues V) : v < 2 ^ C.Wd := by
  have hb := field_bits_le V (proofValue_mem_fields V hv)
  exact (lt_natBitLength v).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem proofValues_count_fit {C : Ctx} {n : ℕ} (V : ThreeQueryVerifier n)
    (hW : inputSize V + 2 ≤ C.Wd) : (proofValues V).length < 2 ^ C.Wd := by
  have hl := proofValues_length_le V
  exact lt_of_lt_of_le (by omega : (proofValues V).length < C.Wd) (Nat.lt_two_pow_self).le

end NearCubicGates.Adapters.Proximity.Trim
