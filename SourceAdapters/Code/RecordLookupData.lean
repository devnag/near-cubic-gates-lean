import Proof.Gates.Cells.Loop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": first-occurrence semantics for a counted numeric lookup. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.RecordLookup

def saved (length index scanned : ℕ) : ℕ := if index < scanned then index else length

theorem before_index_ne (records : List ℕ) (value k : ℕ) (hk : k < records.idxOf value) :
    records[k]'(hk.trans_le List.idxOf_le_length) ≠ value := by
  intro he
  have hklen : k < records.length := hk.trans_le (List.idxOf_le_length (l := records) (a := value))
  have h := List.not_of_lt_findIdx (p := fun x : ℕ => x == value) (xs := records) (i := k) hk
  have ht : (records[k] == value) = true := by simp [he]
  exact Bool.noConfusion (ht.symm.trans h)

theorem saved_step (records : List ℕ) (value k : ℕ) (hk : k < records.length) :
    (if records[k] = value ∧ saved records.length (records.idxOf value) k = records.length
      then k else saved records.length (records.idxOf value) k) =
      saved records.length (records.idxOf value) (k + 1) := by
  by_cases hbefore : records.idxOf value < k
  · have hn : records.idxOf value ≠ records.length := by
      have h := hbefore.trans hk
      omega
    have hs : records.idxOf value < k + 1 := by omega
    simp [saved, hbefore, hn, hs]
  · by_cases heq : records.idxOf value = k
    · have hv : records[k] = value := by
        have h := List.getElem_idxOf (show records.idxOf value < records.length by omega)
        simpa only [heq] using h
      simp [saved, heq, hv]
    · have hlt : k < records.idxOf value := by omega
      have hv := before_index_ne records value k hlt
      have hs : ¬ records.idxOf value < k + 1 := by omega
      simp [saved, hbefore, hv, hs]

theorem saved_final (records : List ℕ) (value : ℕ) :
    saved records.length (records.idxOf value) records.length = records.idxOf value := by
  have h : records.idxOf value ≤ records.length := List.idxOf_le_length
  unfold saved
  split_ifs <;> omega

end NearCubicGates.Adapters.Code.RecordLookup
