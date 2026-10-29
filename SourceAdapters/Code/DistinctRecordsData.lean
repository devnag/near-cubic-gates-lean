import SourceAdapters.Code.DistinctRecordsSpec

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": mathematical semantics of adjacent record suppression. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DistinctRecords

/-- A separate optional previous record makes zero an ordinary value. -/
def emitted (previous : Option ℕ) (value : ℕ) : List ℕ :=
  if previous = some value then [] else [value]

def scan (previous : Option ℕ) : List ℕ → List ℕ
  | [] => []
  | value :: records => emitted previous value ++ scan (some value) records

theorem emitted_length (previous : Option ℕ) (value : ℕ) : (emitted previous value).length ≤ 1 := by
  unfold emitted
  split <;> simp

theorem scan_length (previous : Option ℕ) (records : List ℕ) :
    (scan previous records).length ≤ records.length := by
  induction records generalizing previous with
  | nil => rfl
  | cons value records ih =>
    have h := emitted_length previous value
    have hi := ih (some value)
    simp only [scan, List.length_append, List.length_cons]
    omega

theorem scan_some (previous : ℕ) (records : List ℕ) :
    previous :: scan (some previous) records = records.destutter' (· ≠ ·) previous := by
  induction records generalizing previous with
  | nil => rfl
  | cons value records ih =>
    by_cases h : previous = value
    · subst value
      simpa [scan, emitted, List.destutter'] using ih previous
    · simp [scan, emitted, List.destutter', h, ih]

theorem scan_none (records : List ℕ) : scan none records = records.destutter (· ≠ ·) := by
  cases records with
  | nil => rfl
  | cons value records =>
    simpa [scan, emitted, List.destutter_cons'] using scan_some value records

theorem scan_eq_dedup (records : List ℕ) (h : records.Pairwise (· ≤ ·)) :
    scan none records = records.dedup := by
  rw [scan_none]
  exact h.destutter_eq_dedup

end NearCubicGates.Adapters.Code.DistinctRecords
