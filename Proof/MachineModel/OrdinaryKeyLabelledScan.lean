import Proof.MachineModel.OrdinaryKeyLoop

/-! The keyed scan consumes the literal existing annotator encoding, with
sequential ranks and the preserved score/id words. -/
namespace NearCubicWires.RepairOrdinary.KeyLoop
open LocalBitMultitape SignedSortKey
open KeyCell (config)
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexed (n : ℕ) : List (ℤ × ℕ) → List Record
  | [] => []
  | (score, id) :: entries => (score, id, n) :: indexed (n + 1) entries
def words (S K : ℕ) (entries : List (ℤ × ℕ)) : List (List Bool) :=
  entries.map (fun e => RadixSemantics.word (encode S K e.1 e.2))

@[simp] theorem indexed_length (n : ℕ) (entries : List (ℤ × ℕ)) : (indexed n entries).length = entries.length := by
  induction entries generalizing n with
  | nil => rfl
  | cons e entries ih => rcases e with ⟨score, id⟩; simp [indexed, ih]

theorem indexed_fields (S K n : ℕ) (entries : List (ℤ × ℕ)) :
    fields S K (indexed n entries) = (RankMeaning.annotated (K + S + 1) n (words S K entries)).flatMap frame := by
  induction entries generalizing n with
  | nil => rfl
  | cons e entries ih =>
    rcases e with ⟨score, id⟩
    simpa [fields, indexed, words, word, RankMeaning.annotated] using
      congrArg (fun tail => frame (RadixSemantics.word (encode S K score id) ++ binary (K + S + 1) n) ++ tail) (ih (n + 1))

theorem indexed_stream (S K n : ℕ) (entries : List (ℤ × ℕ)) :
    stream S K (indexed n entries) = RankLoop.stream (RankMeaning.annotated (K + S + 1) n (words S K entries)) := by
  rw [stream, indexed_fields]
  rfl

theorem indexed_fits (W n : ℕ) (entries : List (ℤ × ℕ)) (hn : n + entries.length < 2 ^ W) :
    ∀ r ∈ indexed n entries, r.2.2 < 2 ^ W := by
  induction entries generalizing n with
  | nil => simp [indexed]
  | cons e entries ih =>
    rcases e with ⟨score, id⟩
    intro r hm
    simp only [indexed, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only [List.length_cons] at hn
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hn
    · exact ih (n + 1) (by simp only [List.length_cons] at hn; omega) r hm

theorem labelled_run (S K I inner cap a b initialRank n : ℕ) (entries : List (ℤ × ℕ))
    (pre upper recordBack cloneBack out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hn : n + entries.length < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : recordBack.length ≤ 4 * (K + S + 1) + 1)
    (hc : cloneBack.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ cap) (hck : 2 * K ≤ cap) :
    let W := K + S + 1
    let annotated := RankMeaning.annotated W n (words S K entries)
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * W + 1 ∧ finalRecord.length ≤ 4 * W + 1 ∧ finalClone.length ≤ 4 * W + 1 ∧
      ∃ r : ExecutionReceipt 20 55,
        runFrom machine (entries.length * (68 * W + 4 * (I + K) + 63) + 1)
          (config (test 53) W a b initialRank upper recordBack cloneBack mask (pre ++ RankLoop.stream annotated) pre.length out K I inner cap) = some r ∧
        r.final = config (stop 53) W a b finalRank finalUpper finalRecord finalClone mask (pre ++ RankLoop.stream annotated)
          (pre.length + (annotated.flatMap frame).length) (out ++ output K I inner a b mask (indexed n entries)) K I inner cap ∧
        r.steps ≤ entries.length * (68 * W + 4 * (I + K) + 63) + 1 ∧
        r.peakTapeCells ≤ (pre ++ RankLoop.stream annotated).length + 104 * W + 8 * I + 6 * K + out.length +
          entries.length * (2 * (I + K) + 3) + cap + 64 := by
  simpa only [indexed_length, indexed_stream, indexed_fields] using
    loop_run S K I inner cap a b initialRank (indexed n entries) pre upper recordBack cloneBack out mask hfit
      (indexed_fits (K + S + 1) n entries hn) hu hr hc hci hck

end NearCubicWires.RepairOrdinary.KeyLoop
