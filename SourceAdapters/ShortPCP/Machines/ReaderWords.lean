import SourceAdapters.ShortPCP.TimeStages

/-!
# Single-run time, stage 3 (reader): word lemmas

Foundations for `Time.ReaderStage` (proof of `thm:short-pcp-ours`: the proof bits are read at the listed addresses). The reader's
input stream holds `frame u`, `u` a reader word: bit `p` of `u` is the odd cell `2p + 1` (`frame_odd`), the even cells
are `true` inside `u` and `false` at its end (`frame_even`), and writing an odd cell sets a bit of `u`
(`frame_write_odd`). A reader word is `1^s 0`, entries `1 U P V ++ frame (binary L a)` of `2L + 5` bits each
(`entry`, `entry_length`), `0`, and the rest; entry `i` starts at bit `s + 1 + i·(2L + 5)` (`entry_start`).
`U P V = 1 0 0`: not asked; `0 1 0`: asked, answer pending; `0 0 b`: answered `b` (`readerWord_eq`, `readWord_eq`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines.Reader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Adapters.ShortPCP.Time

/-- The odd cell `2p + 1` of a framed word is its bit `p`. -/
theorem frame_odd (u : List Bool) (p : ℕ) (hp : p < u.length) :
    readTapeBit (frame u) (2 * p + 1) = u.getD p false := by
  induction u generalizing p with
  | nil => simp at hp
  | cons b u ih =>
    cases p with
    | zero => simp [frame, readTapeBit]
    | succ p =>
      have := ih p (by simpa using hp)
      simp only [readTapeBit] at this ⊢
      rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring]
      simpa [frame] using this

/-- The even cell `2p` of a framed word: `true` inside the word, `false` at its end. -/
theorem frame_even (u : List Bool) (p : ℕ) : readTapeBit (frame u) (2 * p) = decide (p < u.length) := by
  induction u generalizing p with
  | nil => cases p <;> simp [frame, readTapeBit]
  | cons b u ih =>
    cases p with
    | zero => simp [frame, readTapeBit]
    | succ p =>
      have := ih p
      simp only [readTapeBit] at this ⊢
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring]
      simpa [frame] using this

/-- **Writing an odd cell sets a bit of the framed word.** -/
theorem frame_write_odd (u : List Bool) (p : ℕ) (hp : p < u.length) (b : Bool) :
    writeTapeBit (frame u) (2 * p + 1) b = frame (u.set p b) := by
  induction u generalizing p with
  | nil => simp at hp
  | cons c u ih =>
    cases p with
    | zero => simp [frame, writeTapeBit]
    | succ p =>
      have := ih p (by simpa using hp)
      rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring]
      simp only [frame, List.set_cons_succ]
      simp only [writeTapeBit] at this ⊢
      simpa using this

/-- One entry of the reader word (`1 U P V ++ frame (binary L a)`), `2L + 5` bits. -/
def entry (L a : ℕ) (U P V : Bool) : List Bool := true :: U :: P :: V :: frame (binary L a)

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]; ring

theorem entry_length (L a : ℕ) (U P V : Bool) : (entry L a U P V).length = 2 * L + 5 := by
  simp [entry, binary_length]

/-- The reader word in entries: every entry `1 1 0 0` (not asked). -/
theorem readerWord_eq (s L : ℕ) (xs : List ℕ) (rest : List Bool) :
    readerWord s L xs rest =
      List.replicate s true ++ false :: ((xs.map fun a => entry L a true false false).flatten ++ false :: rest) := by
  simp [readerWord, entry, List.flatMap]

/-- The read word in entries: entry `i` is `1 0 0 bᵢ`. -/
theorem readWord_eq (s L : ℕ) (xs : List ℕ) (ans rest : List Bool) :
    readWord s L xs ans rest = List.replicate s true ++ false ::
      ((List.zipWith (fun a b => entry L a false false b) xs ans).flatten ++ false :: rest) := by
  simp [readWord, entry]

/-- Entry `i` starts at bit `s + 1 + i·(2L + 5)` of a word in entries (all entries have `2L + 5` bits). -/
theorem entry_start (s L : ℕ) (es : List (List Bool)) (he : ∀ e ∈ es, e.length = 2 * L + 5) (i : ℕ)
    (hi : i < es.length) (rest : List Bool) :
    (List.replicate s true ++ false :: (es.flatten ++ false :: rest)).drop (s + 1 + i * (2 * L + 5)) =
      es[i] ++ ((es.drop (i + 1)).flatten ++ false :: rest) := by
  have hpre : (List.replicate s true ++ [false]).length = s + 1 := by simp
  rw [show List.replicate s true ++ false :: (es.flatten ++ false :: rest) =
    (List.replicate s true ++ [false]) ++ (es.flatten ++ false :: rest) by simp, ← hpre, ← List.drop_drop,
    List.drop_left]
  have htake : ((es.take i).flatten).length = i * (2 * L + 5) := by
    rw [List.length_flatten]
    have : ∀ l ∈ (es.take i), l.length = 2 * L + 5 := fun l hl => he l (List.mem_of_mem_take hl)
    rw [List.map_congr_left this]
    simp [Nat.min_eq_left hi.le, mul_comm]
  conv_lhs => rw [← List.take_append_drop i es, List.flatten_append, List.append_assoc, ← htake, List.drop_left]
  rw [List.drop_eq_getElem_cons hi, List.flatten_cons, List.append_assoc]

end NearCubicGates.Adapters.ShortPCP.Machines.Reader
