import Proof.Wire_3_5.UnionMachinePlan

/-! # C6 front utility: blank register tapes of a computed capacity

The register language (C5's `WM`) needs every register tape to hold exactly `regTape cap v`; a register at `0` is
`replicate (cap+1) false`. The front's stages each own FRESH (empty) tapes, so before a stage runs, its register tapes
are filled with `replicate (2W+3) false` from a unary count `1^W` (a width the front already holds; `2W + 2 ≥ 2W`
is the capacity C5's word passes need, `mapPass_spec`'s `2·|word| ≤ cap`).

**`fillP`** (FinalPass `Prog`): a forward loop over the count writing two blank cells per mark on every target and two
markers on an auxiliary tape, three more cells, one step back, then a backward loop on the marker tape that erases it
and walks every head back to `0` (at `0` the head stays, reads the erased marker, and the loop stops).
**`fillP_exec`**: from the count `1^W` at head `0` and blank targets and marker tape, every target and the marker tape
hold `replicate (2W+3) false` at head `0`; the count keeps its word (head at `W`); all other tapes are untouched.
Cost `11W + 20`.

Donors checked: base `SelectedErase` / `Scrub.erase_step` (needs a driver `1^R` and a padded log) and
`Scrub.entry_step` (needs the `UnaryCalc` workspace) fit a stage already inside the scrubbed layout; the front's fresh
stage tapes need neither, so this two-loop program is the smaller piece. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFill
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Tape lemmas -/

theorem writeTapeBit_end (l : List Bool) (v : Bool) : writeTapeBit l l.length v = l ++ [v] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [writeTapeBit, ih]

theorem write_replicate_end (n : ℕ) (b : Bool) : writeTapeBit (List.replicate n b) n b = List.replicate (n + 1) b := by
  have := writeTapeBit_end (List.replicate n b) b
  rw [List.length_replicate] at this
  rw [this, List.replicate_succ']

/-- Erasing the last marker of a marker prefix. -/
theorem write_marker (m r : ℕ) :
    writeTapeBit (List.replicate (m + 1) true ++ List.replicate r false) m false =
      List.replicate m true ++ List.replicate (r + 1) false := by
  induction m with
  | zero => simp [writeTapeBit, List.replicate_succ]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append]
    show true :: writeTapeBit (List.replicate (m + 1) true ++ List.replicate r false) m false = _
    rw [ih]
    rfl

theorem read_false (r i : ℕ) : readTapeBit (List.replicate r false) i = false := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem read_true (n i : ℕ) (h : i < n) : readTapeBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem read_true_ge (n i : ℕ) (h : n ≤ i) : readTapeBit (List.replicate n true) i = false := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i => exact ih i (by omega)

theorem read_marker (m r i : ℕ) (h : i < m) : readTapeBit (List.replicate m true ++ List.replicate r false) i = true := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem read_marker_ge (m r i : ℕ) (h : m ≤ i) :
    readTapeBit (List.replicate m true ++ List.replicate r false) i = false := by
  induction m generalizing i with
  | zero => exact read_false r i
  | succ m ih =>
    cases i with
    | zero => omega
    | succ i => exact ih i (by omega)

variable {t : ℕ} (cnt aux : Fin t) (tgt : Fin t → Bool)

/-! ## The program -/

/-- The targets and the marker tape (moved together). -/
def side (i : Fin t) : Prop := tgt i = true ∨ i = aux

instance (i : Fin t) : Decidable (side aux tgt i) := by unfold side; infer_instance

/-- Write one cell on every target (`false`) and the marker tape (`true`). -/
def wOne : Fin t → Option Bool := fun i => if tgt i then some false else if i = aux then some true else none

/-- Forward body: two cells on every target and marker, one count mark consumed. -/
def fwdBody : Prog t :=
  .seq (.act (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay))
    (.act (wOne aux tgt) (fun i => if side aux tgt i ∨ i = cnt then .right else .stay))

/-- One more cell on every target and marker. -/
def extraOne : Prog t := .act (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay)

/-- One step left on the targets and the marker. -/
def stepLeft : Prog t := .act (fun _ => none) (fun i => if side aux tgt i then .left else .stay)

/-- Backward body: erase the marker, every target and the marker step left. -/
def bwdBody : Prog t :=
  .act (fun i => if i = aux then some false else none) (fun i => if side aux tgt i ∨ i = cnt then .left else .stay)

/-- **The fill program.** -/
def fillP : Prog t :=
  .seq (.loop cnt (fwdBody cnt aux tgt))
    (.seq (extraOne aux tgt) (.seq (extraOne aux tgt) (.seq (extraOne aux tgt)
      (.seq (stepLeft aux tgt) (.loop aux (bwdBody cnt aux tgt))))))

/-! ## The run -/

section Run
variable (H0 : Fin t → ℕ) (A0 : Fin t → List Bool)
variable (hca : cnt ≠ aux) (hct : tgt cnt = false) (hat : tgt aux = false)

/-- After `j` forward rounds (and `e` extra cells): the count's head at `j`, every target and the marker at
`2j + e` cells, head at the end. -/
def stF (j e : ℕ) : Bank t :=
  ⟨fun i => if i = cnt then j else if side aux tgt i then 2 * j + e else H0 i,
   fun i => if tgt i then List.replicate (2 * j + e) false else if i = aux then List.replicate (2 * j + e) true
     else A0 i⟩

/-- Backward: `m` markers left, the rest erased, every target and the marker at head `m - 1` (clamped). -/
def stB (W m : ℕ) : Bank t :=
  ⟨fun i => if i = cnt then W - (2 * W + 3 - m) else if side aux tgt i then m - 1 else H0 i,
   fun i => if tgt i then List.replicate (2 * W + 3) false
     else if i = aux then List.replicate m true ++ List.replicate (2 * W + 3 - m) false else A0 i⟩

include hca hct hat in
theorem fwd_step (j : ℕ) : Exec (fwdBody cnt aux tgt) (stF cnt aux tgt H0 A0 j 0) (stF cnt aux tgt H0 A0 (j + 1) 0) 3 := by
  have e := Exec.seq (Exec.act (stF cnt aux tgt H0 A0 j 0) (wOne aux tgt)
      (fun i => if side aux tgt i then .right else .stay))
    (Exec.act ((stF cnt aux tgt H0 A0 j 0).act (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay))
      (wOne aux tgt) (fun i => if side aux tgt i ∨ i = cnt then .right else .stay))
  have hcs : ¬ side aux tgt cnt := by simp [side, hct, hca]
  have heq : ((stF cnt aux tgt H0 A0 j 0).act (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay)).act
      (wOne aux tgt) (fun i => if side aux tgt i ∨ i = cnt then .right else .stay) = stF cnt aux tgt H0 A0 (j + 1) 0 := by
    apply Bank.ext'
    · intro i
      simp only [Bank.act, stF]
      by_cases hi : i = cnt
      · subst hi; simp [hcs, HeadMove.apply]
      · by_cases hs : side aux tgt i
        · simp only [hi, hs, if_true, if_false, or_false, HeadMove.apply]; omega
        · simp [hi, hs, HeadMove.apply]
    · intro i
      simp only [Bank.act, stF]
      by_cases ht : tgt i = true
      · have hs : side aux tgt i := Or.inl ht
        have hic : i ≠ cnt := by rintro rfl; rw [hct] at ht; cases ht
        simp only [wOne, ht, if_true, hs, hic, if_false, HeadMove.apply]
        rw [write_replicate_end, write_replicate_end]
        congr 1
      · by_cases hi : i = aux
        · subst hi
          have hs : side i tgt i := Or.inr rfl
          have hic : i ≠ cnt := fun h => hca h.symm
          simp only [wOne, hat, Bool.false_eq_true, if_false, if_true, hs, hic, HeadMove.apply]
          rw [write_replicate_end, write_replicate_end]
          congr 1
        · simp [wOne, ht, hi]
  rw [heq] at e
  exact e

include hca hct hat in
theorem fwd_loop (W : ℕ) (hcw : A0 cnt = List.replicate W true) :
    ∀ m j, j + m = W → Exec (.loop cnt (fwdBody cnt aux tgt)) (stF cnt aux tgt H0 A0 j 0)
      (stF cnt aux tgt H0 A0 W 0) (5 * m + 1)
  | 0, j, h => by
    have hj : j = W := by omega
    subst hj
    refine Exec.loopF ?_
    simp only [Bank.bit, stF, hct, Bool.false_eq_true, if_false, hca, if_true, hcw]
    exact read_true_ge j j le_rfl
  | m + 1, j, h => by
    have hb : (stF cnt aux tgt H0 A0 j 0).bit cnt = true := by
      simp only [Bank.bit, stF, hct, Bool.false_eq_true, if_false, hca, if_true, hcw]
      exact read_true W j (by omega)
    have := Exec.loopT hb (fwd_step cnt aux tgt H0 A0 hca hct hat j) (fwd_loop W hcw m (j + 1) (by omega))
    exact Exec.mono this (by omega)

include hca hct hat in
theorem extra_step (j e : ℕ) : Exec (extraOne aux tgt) (stF cnt aux tgt H0 A0 j e) (stF cnt aux tgt H0 A0 j (e + 1)) 1 := by
  have ex := Exec.act (stF cnt aux tgt H0 A0 j e) (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay)
  have hcs : ¬ side aux tgt cnt := by simp [side, hct, hca]
  have heq : (stF cnt aux tgt H0 A0 j e).act (wOne aux tgt) (fun i => if side aux tgt i then .right else .stay) =
      stF cnt aux tgt H0 A0 j (e + 1) := by
    apply Bank.ext'
    · intro i
      simp only [Bank.act, stF]
      by_cases hi : i = cnt
      · subst hi; simp [hcs, HeadMove.apply]
      · by_cases hs : side aux tgt i
        · simp only [hi, hs, if_true, if_false, HeadMove.apply]; omega
        · simp [hi, hs, HeadMove.apply]
    · intro i
      simp only [Bank.act, stF]
      by_cases ht : tgt i = true
      · have hic : i ≠ cnt := by rintro rfl; rw [hct] at ht; cases ht
        have hs : side aux tgt i := Or.inl ht
        simp only [wOne, ht, if_true, hic, hs, if_false]
        rw [write_replicate_end]; congr 1
      · by_cases hi : i = aux
        · subst hi
          have hic : i ≠ cnt := fun h => hca h.symm
          have hs : side i tgt i := Or.inr rfl
          simp only [wOne, hat, Bool.false_eq_true, if_false, if_true, hic, hs]
          rw [write_replicate_end]; congr 1
        · simp [wOne, ht, hi]
  rw [heq] at ex
  exact ex

include hca hct hat in
theorem stepLeft_step (W : ℕ) :
    Exec (stepLeft aux tgt) (stF cnt aux tgt H0 A0 W 3) (stB cnt aux tgt H0 A0 W (2 * W + 3)) 1 := by
  have ex := Exec.act (stF cnt aux tgt H0 A0 W 3) (fun _ => none) (fun i => if side aux tgt i then .left else .stay)
  have hcs : ¬ side aux tgt cnt := by simp [side, hct, hca]
  have heq : (stF cnt aux tgt H0 A0 W 3).act (fun _ => none) (fun i => if side aux tgt i then .left else .stay) =
      stB cnt aux tgt H0 A0 W (2 * W + 3) := by
    apply Bank.ext'
    · intro i
      simp only [Bank.act, stF, stB]
      by_cases hi : i = cnt
      · subst hi; simp [hcs, HeadMove.apply]
      · by_cases hs : side aux tgt i
        · simp only [hi, hs, if_true, if_false, HeadMove.apply]
        · simp [hi, hs, HeadMove.apply]
    · intro i
      simp only [Bank.act, stF, stB]
      by_cases ht : tgt i = true
      · simp [ht]
      · by_cases hi : i = aux
        · subst hi; simp [ht]
        · simp [ht, hi]
  rw [heq] at ex
  exact ex

include hca hct hat in
theorem bwd_step (W m : ℕ) (hm : m + 1 ≤ 2 * W + 3) :
    Exec (bwdBody cnt aux tgt) (stB cnt aux tgt H0 A0 W (m + 1)) (stB cnt aux tgt H0 A0 W m) 1 := by
  have ex := Exec.act (stB cnt aux tgt H0 A0 W (m + 1)) (fun i => if i = aux then some false else none)
    (fun i => if side aux tgt i ∨ i = cnt then .left else .stay)
  have hcs : ¬ side aux tgt cnt := by simp [side, hct, hca]
  have heq : (stB cnt aux tgt H0 A0 W (m + 1)).act (fun i => if i = aux then some false else none)
      (fun i => if side aux tgt i ∨ i = cnt then .left else .stay) = stB cnt aux tgt H0 A0 W m := by
    apply Bank.ext'
    · intro i
      simp only [Bank.act, stB]
      by_cases hi : i = cnt
      · subst hi; simp only [if_true, or_true, HeadMove.apply]; omega
      · by_cases hs : side aux tgt i
        · simp only [hi, hs, if_true, if_false, true_or, HeadMove.apply]; omega
        · simp [hi, hs, HeadMove.apply]
    · intro i
      simp only [Bank.act, stB]
      by_cases ht : tgt i = true
      · have hia : i ≠ aux := by rintro rfl; rw [hat] at ht; cases ht
        simp [ht, hia]
      · by_cases hi : i = aux
        · subst hi
          have hic : i ≠ cnt := fun h => hca h.symm
          have hs : side i tgt i := Or.inr rfl
          simp only [hat, Bool.false_eq_true, if_false, if_true, hic, hs, Nat.add_sub_cancel]
          rw [write_marker, show 2 * W + 3 - (m + 1) + 1 = 2 * W + 3 - m by omega]
        · simp [ht, hi]
  rw [heq] at ex
  exact ex

include hca hct hat in
theorem bwd_loop (W : ℕ) : ∀ m, m ≤ 2 * W + 3 →
    Exec (.loop aux (bwdBody cnt aux tgt)) (stB cnt aux tgt H0 A0 W m) (stB cnt aux tgt H0 A0 W 0) (3 * m + 1)
  | 0, _ => by
    refine Exec.loopF ?_
    simp only [Bank.bit, stB, hat, Bool.false_eq_true, if_false, if_true, (hca.symm : aux ≠ cnt)]
    have hs : side aux tgt aux := Or.inr rfl
    simp only [hs, if_true]
    exact read_marker_ge 0 _ _ (Nat.zero_le _)
  | m + 1, hm => by
    have hb : (stB cnt aux tgt H0 A0 W (m + 1)).bit aux = true := by
      simp only [Bank.bit, stB, hat, Bool.false_eq_true, if_false, if_true, (hca.symm : aux ≠ cnt)]
      have hs : side aux tgt aux := Or.inr rfl
      simp only [hs, if_true, Nat.add_sub_cancel]
      exact read_marker (m + 1) _ m (by omega)
    have := Exec.loopT hb (bwd_step cnt aux tgt H0 A0 hca hct hat W m (by omega)) (bwd_loop W m (by omega))
    exact Exec.mono this (by omega)

include hca hct hat in
/-- **The fill**: from the count `1^W` (head `0`) and blank targets and marker tape (heads `0`), every target and the
marker tape hold `replicate (2W+3) false` at head `0`, the count's head is at `W`, nothing else changes. -/
theorem fillP_exec (W : ℕ) (hcw : A0 cnt = List.replicate W true) (hH : ∀ i, i = cnt ∨ side aux tgt i → H0 i = 0)
    (hA : ∀ i, side aux tgt i → A0 i = []) :
    Exec (fillP cnt aux tgt) ⟨H0, A0⟩ (stB cnt aux tgt H0 A0 W 0) (11 * W + 20) := by
  have h0 : (⟨H0, A0⟩ : Bank t) = stF cnt aux tgt H0 A0 0 0 := by
    apply Bank.ext'
    · intro i
      simp only [stF]
      by_cases hi : i = cnt
      · subst hi; simp [hH i (Or.inl rfl)]
      · by_cases hs : side aux tgt i
        · simp [hi, hs, hH i (Or.inr hs)]
        · simp [hi, hs]
    · intro i
      simp only [stF]
      by_cases ht : tgt i = true
      · simp [ht, hA i (Or.inl ht)]
      · by_cases hi : i = aux
        · subst hi; simp [ht, hA i (Or.inr rfl)]
        · simp [ht, hi]
  rw [h0]
  have l1 := fwd_loop cnt aux tgt H0 A0 hca hct hat W hcw W 0 (by omega)
  have e1 := extra_step cnt aux tgt H0 A0 hca hct hat W 0
  have e2 := extra_step cnt aux tgt H0 A0 hca hct hat W 1
  have e3 := extra_step cnt aux tgt H0 A0 hca hct hat W 2
  have sl := stepLeft_step cnt aux tgt H0 A0 hca hct hat W
  have l2 := bwd_loop cnt aux tgt H0 A0 hca hct hat W (2 * W + 3) le_rfl
  refine Exec.mono (Exec.seq l1 (Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq sl l2))))) ?_
  omega

theorem stB_zero_A (W : ℕ) (i : Fin t) (hs : side aux tgt i) :
    (stB cnt aux tgt H0 A0 W 0).A i = List.replicate (2 * W + 3) false := by
  simp only [stB]
  by_cases ht : tgt i = true
  · simp [ht]
  · have hi : i = aux := hs.resolve_left ht
    subst hi; simp [ht]

theorem stB_zero_H (W : ℕ) (hca : cnt ≠ aux) (hct : tgt cnt = false) (i : Fin t) (hs : side aux tgt i) :
    (stB cnt aux tgt H0 A0 W 0).H i = 0 := by
  have hic : i ≠ cnt := by
    rintro rfl
    rcases hs with h | h
    · rw [hct] at h; cases h
    · exact hca h
  simp [stB, hic, hs]

end Run

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFill
