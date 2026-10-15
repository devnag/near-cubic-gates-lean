import Proof.MachineModel.OrdinaryRankCarrier

/-! The exact output of the ordinary label scan contains the original word
followed by its sequential rank. This is the interface to the paper's ranks. -/
namespace NearCubicWires.RepairOrdinary.RankMeaning
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def annotated (width n : ℕ) : List (List Bool) → List (List Bool)
  | [] => []
  | word :: words => (word ++ SignedSortKey.binary width n) :: annotated width (n + 1) words

@[simp] theorem annotated_length (width n : ℕ) (words : List (List Bool)) :
    (annotated width n words).length = words.length := by
  induction words generalizing n with
  | nil => rfl
  | cons word words ih => simp [annotated, ih]

theorem output_stream (width n : ℕ) (words : List (List Bool)) :
    RankLoop.labels width n words ++ [false] = RankLoop.stream (annotated width n words) := by
  have h : RankLoop.labels width n words = (annotated width n words).flatMap frame := by
    induction words generalizing n with
    | nil => rfl
    | cons word words ih => simp [RankLoop.labels, annotated, ih]
  rw [h]
  rfl

theorem annotated_get (width n : ℕ) (words : List (List Bool)) (i : ℕ) (hi : i < words.length) :
    (annotated width n words).getD i [] = words[i] ++ SignedSortKey.binary width (n + i) := by
  induction i generalizing n words with
  | zero =>
    cases words with
    | nil => simp at hi
    | cons word words => simp [annotated, List.getD]
  | succ i ih =>
    cases words with
    | nil => simp at hi
    | cons word words =>
      have h := ih (n + 1) words (by simpa using hi)
      simpa [annotated, List.getD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem rank_value (width n : ℕ) (words : List (List Bool)) (i : ℕ) (hi : i < words.length)
    (hw : ∀ word ∈ words, word.length = width) (hn : n + words.length < 2 ^ width) :
    RadixSemantics.value (((annotated width n words).getD i []).drop width) = n + i := by
  rw [annotated_get width n words i hi]
  have hword := hw words[i] (List.getElem_mem hi)
  have hdrop : (words[i] ++ SignedSortKey.binary width (n + i)).drop width = SignedSortKey.binary width (n + i) := by
    rw [← hword]
    simp
  rw [hdrop, SignedSortKey.binary_value _ _ (by omega)]

theorem preserved_word (width n : ℕ) (words : List (List Bool)) (i : ℕ) (hi : i < words.length)
    (hw : ∀ word ∈ words, word.length = width) :
    ((annotated width n words).getD i []).take width = words[i] := by
  rw [annotated_get width n words i hi]
  have hword := hw words[i] (List.getElem_mem hi)
  rw [← hword]
  simp

end NearCubicWires.RepairOrdinary.RankMeaning
