import Proof.Wire_3_5.CompilerMachineKit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Skipping one framed record -/

/-- Move the head across one framed word: state `0` reads a marker, `1` steps over a bit, `2` halts. -/
def skipM : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then ⟨1, fun _ => none, fun _ => .right⟩ else ⟨2, fun _ => none, fun _ => .right⟩)
    else if q.val = 1 then some ⟨0, fun _ => none, fun _ => .right⟩
    else none

theorem skip_mark (T : List Bool) (h : ℕ) (hr : readTapeBit T h = true) :
    step skipM ⟨0, ![h], ![T]⟩ = some ⟨1, ![h + 1], ![T]⟩ := by
  simp [step, skipM, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i; simp [applyAction]

theorem skip_bit (T : List Bool) (h : ℕ) : step skipM ⟨1, ![h], ![T]⟩ = some ⟨0, ![h + 1], ![T]⟩ := by
  simp [step, skipM]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i; simp [applyAction]

theorem skip_end (T : List Bool) (h : ℕ) (hr : readTapeBit T h = false) :
    step skipM ⟨0, ![h], ![T]⟩ = some ⟨2, ![h + 1], ![T]⟩ := by
  simp [step, skipM, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i; simp [applyAction]

theorem skip_timed (T post : List Bool) : ∀ (w pre : List Bool), T = pre ++ frame w ++ post →
    RecoveryExecution.Timed skipM (2 * w.length + 1) ⟨0, ![pre.length], ![T]⟩
      ⟨2, ![pre.length + 2 * w.length + 1], ![T]⟩
  | [], pre, hT => by
    have hr : readTapeBit T pre.length = false := by
      rw [hT]; simpa [frame] using Streaming.read_append pre post false
    simpa using RecoveryExecution.Timed.single (p := skipM) rfl (skip_end T pre.length hr)
  | a :: w, pre, hT => by
    have hr : readTapeBit T pre.length = true := by
      rw [hT]; simpa [frame, List.append_assoc] using Streaming.read_append pre (a :: frame w ++ post) true
    have t1 := RecoveryExecution.Timed.single (p := skipM) rfl (skip_mark T pre.length hr)
    have t2 := RecoveryExecution.Timed.single (p := skipM) rfl (skip_bit T (pre.length + 1))
    have tail := skip_timed T post w (pre ++ [true, a]) (by rw [hT]; simp [frame, List.append_assoc])
    have e : (pre ++ [true, a]).length = pre.length + 1 + 1 := by simp
    rw [e] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega,
      show pre.length + 1 + 1 + 2 * w.length + 1 = pre.length + 2 * (a :: w).length + 1 by simp; omega] at this

/-- **Skip one framed record**: the head moves from its first cell to the cell after it. -/
theorem skipStep (pre w post : List Bool) :
    Step skipM (2 * w.length + 1) ![pre.length] ![pre ++ frame w ++ post]
      ![pre.length + 2 * w.length + 1] ![pre ++ frame w ++ post] := by
  obtain ⟨r, hr, hf, hs⟩ := (skip_timed (pre ++ frame w ++ post) post w pre rfl).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-! ## A stream after a prefix -/

theorem read_stream_record_at (P : List Bool) (rs : List (List Bool)) (stale : List Bool) (j : ℕ) (hj : j < rs.length)
    (hne : rs[j] ≠ []) : readTapeBit (P ++ streamTape rs stale) (P.length + off rs j) = true := by
  have h := read_stream_record rs stale j hj hne
  unfold readTapeBit at h ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at *
  simpa using h

theorem read_stream_end_at (P : List Bool) (rs : List (List Bool)) (stale : List Bool) :
    readTapeBit (P ++ streamTape rs stale) (P.length + (rs.flatMap frame).length) = false := by
  have h := read_stream_end rs stale
  unfold readTapeBit at h ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at *
  simpa using h

/-- **`streamRun` for a stream after a prefix `P`**: the source tape holds `P ++ streamTape rs stale`, the cursor
starts at `P.length`. -/
theorem streamRunAt {t s : ℕ} (body : Machine t s) (src : Fin t) (P : List Bool) (rs : List (List Bool))
    (stale : List Bool) (hne : ∀ r ∈ rs, r ≠ []) {σ : Type} (f : σ → List Bool → σ) (s0 : σ)
    (bH : σ → ℕ → Fin t → ℕ) (bA : σ → Fin t → List Bool)
    (hsrcA : ∀ st, bA st src = P ++ streamTape rs stale) (hsrcH : ∀ st p, bH st p src = p) (c : ℕ)
    (hstep : ∀ j, j < rs.length → Step body c (bH ((rs.take j).foldl f s0) (P.length + off rs j))
      (bA ((rs.take j).foldl f s0)) (bH ((rs.take (j + 1)).foldl f s0) (P.length + off rs (j + 1)))
      (bA ((rs.take (j + 1)).foldl f s0))) :
    Step (StreamController.machine body src) (rs.length * (c + 2) + 1) (bH s0 P.length) (bA s0)
      (bH (rs.foldl f s0) (P.length + (rs.flatMap frame).length)) (bA (rs.foldl f s0)) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := rs.length
      H := fun j => bH ((rs.take j).foldl f s0) (P.length + off rs j)
      A := fun j => bA ((rs.take j).foldl f s0)
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA ((rs.take j).foldl f s0) src)
          (bH ((rs.take j).foldl f s0) (P.length + off rs j) src) = true
        rw [hsrcA, hsrcH]
        exact read_stream_record_at P rs stale j hj (hne _ (List.getElem_mem hj))
      halt := by
        show readTapeBit (bA ((rs.take rs.length).foldl f s0) src)
          (bH ((rs.take rs.length).foldl f s0) (P.length + off rs rs.length) src) = false
        rw [hsrcA, hsrcH, off_length]
        exact read_stream_end_at P rs stale }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  have e0 : W.H 0 = bH s0 P.length := by simp [W, off]
  have e1 : W.A 0 = bA s0 := by simp [W]
  have e2 : W.H W.bound = bH (rs.foldl f s0) (P.length + (rs.flatMap frame).length) := by
    simp only [W, List.take_length, off_length]
  have e3 : W.A W.bound = bA (rs.foldl f s0) := by simp only [W, List.take_length]
  rw [e0, e1, e2, e3] at hW
  exact hW

/-! ## A loop over a unary code -/

/-- The frame pairs of a unary code `a`: `[true, true]` per unit, then `[true, false]`. -/
def pairsTape (a : ℕ) : List Bool := (List.replicate a [true, true]).flatten ++ [true, false]

theorem read_pairs_unit (P post : List Bool) (a j : ℕ) (hj : j < a) :
    readTapeBit (P ++ pairsTape a ++ post) (P.length + 2 * j + 1) = true := by
  have e : P ++ pairsTape a ++ post =
      (P ++ (List.replicate j [true, true]).flatten ++ [true]) ++ true :: ((List.replicate (a - j - 1) [true, true]).flatten
        ++ [true, false] ++ post) := by
    have ha : a = j + 1 + (a - j - 1) := by omega
    conv_lhs => rw [pairsTape, ha, List.replicate_add, List.replicate_add]
    simp [List.append_assoc]
  rw [e]
  have := Streaming.read_append (P ++ (List.replicate j [true, true]).flatten ++ [true])
    ((List.replicate (a - j - 1) [true, true]).flatten ++ [true, false] ++ post) true
  simpa [List.length_flatten, List.sum_replicate, Nat.mul_comm, Nat.add_assoc] using this

theorem read_pairs_end (P post : List Bool) (a : ℕ) :
    readTapeBit (P ++ pairsTape a ++ post) (P.length + 2 * a + 1) = false := by
  have e : P ++ pairsTape a ++ post = (P ++ (List.replicate a [true, true]).flatten ++ [true]) ++ false :: post := by
    simp [pairsTape, List.append_assoc]
  rw [e]
  have := Streaming.read_append (P ++ (List.replicate a [true, true]).flatten ++ [true]) post false
  simpa [List.length_flatten, List.sum_replicate, Nat.mul_comm, Nat.add_assoc] using this

/-- **A uniform body once per unit of a unary code.** The code's pairs sit after a prefix `P` on the source tape, in
every bank; the source head reads the bit of pair `j` before pass `j`. -/
theorem unaryRun {t s : ℕ} (body : Machine t s) (src : Fin t) (P post : List Bool) (a : ℕ)
    (bH : ℕ → Fin t → ℕ) (bA : ℕ → Fin t → List Bool)
    (hsrcA : ∀ j, bA j src = P ++ pairsTape a ++ post) (hsrcH : ∀ j, bH j src = P.length + 2 * j + 1) (c : ℕ)
    (hstep : ∀ j, j < a → Step body c (bH j) (bA j) (bH (j + 1)) (bA (j + 1))) :
    Step (StreamController.machine body src) (a * (c + 2) + 1) (bH 0) (bA 0) (bH a) (bA a) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := a
      H := bH
      A := bA
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA j src) (bH j src) = true
        rw [hsrcA, hsrcH]
        exact read_pairs_unit P post a j hj
      halt := by
        show readTapeBit (bA a src) (bH a src) = false
        rw [hsrcA, hsrcH]
        exact read_pairs_end P post a }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  exact hW

end NearCubicWires.WireExponent3_5.CompilerMachine.Kit
