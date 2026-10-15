import Proof.MachineModel.OrdinaryRecordLoop

/-! The annotated-record loop consumes the exact existing rank-annotator
output word. This closes the encoding boundary, without assuming that its
production or the scalar bucket/mask inputs are free. -/
namespace NearCubicWires.RepairOrdinary.LabelledScan
open LocalBitMultitape
open RecordCell (config)
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexed (n : ℕ) : List (List Bool) → List RecordLoop.Record
  | [] => []
  | word :: words => (word, n) :: indexed (n + 1) words
def outputs (a b : ℕ) (mask : Bool) (n : ℕ) : List (List Bool) → List Bool
  | [] => []
  | _ :: words => LeftCell.selected a b n mask :: outputs a b mask (n + 1) words
@[simp] theorem indexed_length (n : ℕ) (words : List (List Bool)) : (indexed n words).length = words.length := by
  induction words generalizing n with
  | nil => rfl
  | cons word words ih => simp [indexed, ih]

theorem indexed_fields (width n : ℕ) (words : List (List Bool)) :
    RecordLoop.fields width (indexed n words) = (RankMeaning.annotated width n words).flatMap frame := by
  induction words generalizing n with
  | nil => rfl
  | cons word words ih => simp [RecordLoop.fields, indexed, RankMeaning.annotated, ← ih]

theorem indexed_stream (width n : ℕ) (words : List (List Bool)) :
    RecordLoop.stream width (indexed n words) = RankLoop.stream (RankMeaning.annotated width n words) := by
  rw [RecordLoop.stream, indexed_fields]
  rfl

theorem indexed_bits (a b n : ℕ) (mask : Bool) (words : List (List Bool)) :
    RecordLoop.bits a b mask (indexed n words) = outputs a b mask n words := by
  induction words generalizing n with
  | nil => rfl
  | cons word words ih => simp [RecordLoop.bits, indexed, outputs, ← ih]

theorem indexed_fits (width n : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) (hn : n + words.length < 2 ^ width) :
    ∀ r ∈ indexed n words, r.1.length = width ∧ r.2 < 2 ^ width := by
  induction words generalizing n with
  | nil => simp [indexed]
  | cons word words ih =>
    intro r hm
    simp only [indexed, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hw word (by simp), by simp only [List.length_cons] at hn; omega⟩
    · exact ih (n + 1) (fun w h => hw w (by simp [h])) (by simp only [List.length_cons] at hn; omega) r hm

theorem scan_run (width a b initialRank n : ℕ) (words : List (List Bool))
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool) (hw : 0 < width)
    (hfit : a + b < 2 ^ width) (hwords : ∀ word ∈ words, word.length = width)
    (hn : n + words.length < 2 ^ width) (hu : upper.length ≤ 2 * width + 1)
    (hr : recordBack.length ≤ 4 * width + 1) (hc : cloneBack.length ≤ 4 * width + 1) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * width + 1 ∧ finalRecord.length ≤ 4 * width + 1 ∧ finalClone.length ≤ 4 * width + 1 ∧
      ∃ r : ExecutionReceipt 16 43,
        runFrom RecordLoop.machine (words.length * (68 * width + 53) + 1)
          (config (test 41) width a b initialRank upper recordBack cloneBack mask
            (pre ++ RankLoop.stream (RankMeaning.annotated width n words)) pre.length out) = some r ∧
        r.final = config (stop 41) width a b finalRank finalUpper finalRecord finalClone mask
          (pre ++ RankLoop.stream (RankMeaning.annotated width n words))
          (pre.length + ((RankMeaning.annotated width n words).flatMap frame).length)
          (out ++ outputs a b mask n words) ∧
        r.steps = words.length * (68 * width + 53) + 1 ∧
        r.peakTapeCells ≤ (pre ++ RankLoop.stream (RankMeaning.annotated width n words)).length +
          104 * width + out.length + words.length + 53 := by
  simpa only [indexed_length, indexed_stream, indexed_fields, indexed_bits] using
    RecordLoop.loop_run width a b initialRank (indexed n words) pre upper recordBack cloneBack out mask hw hfit
      (indexed_fits width n words hwords hn) hu hr hc

end NearCubicWires.RepairOrdinary.LabelledScan
