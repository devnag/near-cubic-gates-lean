import Proof.Supplier.RowMaskLoop

/-! The emitted mask positions are actual bounded native-child indices.
This identifies the physical word with the common coefficient consumer ABI. -/
namespace NearCubicWires.RepairOrdinary.RowMaskMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positions : ℕ→List Bool→List ℕ
  | _,[]=>[]
  | j,b::bs=>(if b then [j] else [])++positions (j+1) bs

theorem positions_length (j : ℕ) (bits : List Bool) : (positions j bits).length=bits.count true := by
  induction bits generalizing j with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [positions,ih]

theorem positions_bound (j : ℕ) (bits : List Bool) :
    ∀ i ∈ positions j bits, j ≤ i ∧ i < j+bits.length := by
  induction bits generalizing j with
  | nil => simp [positions]
  | cons b bs ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · cases b <;> simp only [Bool.false_eq_true,↓reduceIte,List.not_mem_nil,List.mem_singleton] at hi
      subst i
      simp
    · have h := ih (j+1) i hi
      simp only [List.length_cons]
      omega

theorem word_positions (j : ℕ) (bits : List Bool) :
    RowMaskLoop.word j bits=(positions j bits).flatMap RowIndexField.word := by
  induction bits generalizing j with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [RowMaskLoop.word,RowMaskBody.emitted,positions,ih]

def typed (N j : ℕ) (bits : List Bool) (h : j+bits.length≤N) : List (Fin N) :=
  (positions j bits).attach.map fun i=>⟨i.val,((positions_bound j bits i.val i.property).2).trans_le h⟩

theorem typed_values (N j : ℕ) (bits : List Bool) (h : j+bits.length≤N) :
    (typed N j bits h).map Fin.val=positions j bits := by
  simp [typed,List.map_map,Function.comp_def]

theorem typed_length (N j : ℕ) (bits : List Bool) (h : j+bits.length≤N) :
    (typed N j bits h).length=bits.count true := by
  simp [typed,positions_length]

theorem typed_word (N j : ℕ) (bits : List Bool) (h : j+bits.length≤N) :
    RowMaskLoop.word j bits=RowOccurrenceLoop.word (typed N j bits h) := by
  rw [word_positions,←typed_values N j bits h]
  simp [RowOccurrenceLoop.word,List.flatMap_map]

theorem typed_le (N j : ℕ) (bits : List Bool) (h : j+bits.length≤N) :
    (typed N j bits h).length≤bits.length := by
  rw [typed_length]
  exact List.count_le_length

theorem typed_full_le (N : ℕ) (bits : List Bool) (h : bits.length=N) :
    (typed N 0 bits (by omega)).length≤N := by
  simpa only [h] using typed_le N 0 bits (by omega)

end NearCubicWires.RepairOrdinary.RowMaskMeaning
