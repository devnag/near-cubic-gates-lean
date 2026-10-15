import Proof.Wire_3_5.ListMachinePrintMath
import Proof.Wire_3_5.ListMachineRecords

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.GF2 (write_mid)
open NearCubicWires.WireExponent3_5.ListMachine.Interp (pop)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## `PopEq`: the flag `[pop X = d]` -/

namespace PopEq
open NearCubicWires.WireExponent3_5.GF2.Three (act cfg)

/-- Tape 0 the framed bitmap, tape 1 the unary `d` (`1^d 0 …`), tape 2 the flag cell. State `0` reads a marker,
`1` a bit (a one moves the unary cursor), `2` halts. At the terminator the flag becomes `[the unary cursor is past
the ones]`. -/
def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 1 none none none .right .stay .stay else act 2 none none (some (!sc 1)) .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 0 none none none .right .right .stay else act 0 none none none .right .stay .stay)
    else none

theorem mark_step (X D C : List Bool) (hx hd hc : ℕ) (hr : readTapeBit X hx = true) :
    step machine (cfg 0 X D C hx hd hc) = some (cfg 1 X D C (hx + 1) hd hc) := by
  have := NearCubicWires.WireExponent3_5.GF2.Three.step_cfg machine 0 1 X D C hx hd hc none none none
    .right .stay .stay (by simp [machine, hr])
  simpa [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply] using this

theorem one_step (X D C : List Bool) (hx hd hc : ℕ) (hr : readTapeBit X hx = true) :
    step machine (cfg 1 X D C hx hd hc) = some (cfg 0 X D C (hx + 1) (hd + 1) hc) := by
  have := NearCubicWires.WireExponent3_5.GF2.Three.step_cfg machine 1 0 X D C hx hd hc none none none
    .right .right .stay (by simp [machine, hr])
  simpa [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply] using this

theorem zero_step (X D C : List Bool) (hx hd hc : ℕ) (hr : readTapeBit X hx = false) :
    step machine (cfg 1 X D C hx hd hc) = some (cfg 0 X D C (hx + 1) hd hc) := by
  have := NearCubicWires.WireExponent3_5.GF2.Three.step_cfg machine 1 0 X D C hx hd hc none none none
    .right .stay .stay (by simp [machine, hr])
  simpa [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply] using this

theorem end_step (X D : List Bool) (c : Bool) (hx hd : ℕ) (hr : readTapeBit X hx = false) :
    step machine (cfg 0 X D [c] hx hd 0) = some (cfg 2 X D [!readTapeBit D hd] hx hd 0) := by
  have := NearCubicWires.WireExponent3_5.GF2.Three.step_cfg machine 0 2 X D [c] hx hd 0 none none
    (some (!readTapeBit D hd)) .stay .stay .stay (by simp [machine, hr])
  simpa [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, writeTapeBit] using this

theorem timed (D : List Bool) (c : Bool) : ∀ (xs preX : List Bool) (k : ℕ),
    Timed machine (2 * xs.length + 1) (cfg 0 (preX ++ frame xs) D [c] preX.length k 0)
      (cfg 2 (preX ++ frame xs) D [!readTapeBit D (k + pop xs)] (preX.length + 2 * xs.length) (k + pop xs) 0) := by
  intro xs
  induction xs with
  | nil =>
    intro preX k
    have hs := end_step (preX ++ frame []) D c preX.length k
      (by simpa [frame] using Streaming.read_append preX [] false)
    simpa [frame, pop] using Timed.single (p := machine) rfl hs
  | cons x xs ih =>
    intro preX k
    have hr1 : readTapeBit (preX ++ frame (x :: xs)) preX.length = true := by
      simpa [frame] using Streaming.read_append preX (x :: frame xs) true
    have hrx : readTapeBit (preX ++ frame (x :: xs)) (preX.length + 1) = x := by
      simpa [frame] using Streaming.read_append (preX ++ [true]) (frame xs) x
    have e0 : preX ++ frame (x :: xs) = preX ++ [true, x] ++ frame xs := by simp [frame]
    have t1 := Timed.single (p := machine) rfl (mark_step _ D [c] preX.length k 0 hr1)
    have tail := ih (preX ++ [true, x]) (k + x.toNat)
    rw [← e0] at tail
    have el : (preX ++ [true, x]).length = preX.length + 1 + 1 := by simp
    rw [el] at tail
    have ek : k + x.toNat + pop xs = k + pop (x :: xs) := by cases x <;> simp [pop, Nat.add_comm, Nat.add_left_comm]
    rw [ek, show preX.length + 1 + 1 + 2 * xs.length = preX.length + 2 * (x :: xs).length by simp; omega]
      at tail
    cases x
    · have t2 := Timed.single (p := machine) rfl (zero_step _ D [c] (preX.length + 1) k 0 hrx)
      have := (t1.trans t2).trans tail
      simpa [show 1 + 1 + (2 * xs.length + 1) = 2 * (false :: xs).length + 1 by simp; omega] using this
    · have t2 := Timed.single (p := machine) rfl (one_step _ D [c] (preX.length + 1) k 0 hrx)
      have := (t1.trans t2).trans tail
      simpa [show 1 + 1 + (2 * xs.length + 1) = 2 * (true :: xs).length + 1 by simp; omega] using this

/-- **The flag `[pop X = d]`** of a bitmap with at most `d` ones, against the unary `1^d 0 …`. -/
theorem run (xs : List Bool) (d : ℕ) (tail : List Bool) (c : Bool) (hd : pop xs ≤ d) :
    Step machine (2 * xs.length + 1) ![0, 0, 0] ![frame xs, List.replicate d true ++ false :: tail, [c]]
      ![2 * xs.length, pop xs, 0]
      ![frame xs, List.replicate d true ++ false :: tail, [decide (pop xs = d)]] := by
  have t := timed (List.replicate d true ++ false :: tail) c xs [] 0
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at t
  have hread : readTapeBit (List.replicate d true ++ false :: tail) (pop xs) = decide (pop xs < d) := by
    rcases Nat.lt_or_eq_of_le hd with h | h
    · obtain ⟨e, he⟩ : ∃ e, d = pop xs + 1 + e := ⟨d - pop xs - 1, by omega⟩
      have e1 : List.replicate d true ++ false :: tail =
          List.replicate (pop xs) true ++ true :: (List.replicate e true ++ false :: tail) := by
        rw [he, List.replicate_add, List.replicate_add]
        simp [List.append_assoc]
      rw [e1]
      have := Streaming.read_append (List.replicate (pop xs) true)
        (List.replicate e true ++ false :: tail) true
      simp only [List.length_replicate] at this
      rw [this, decide_eq_true h]
    · subst h
      have := Streaming.read_append (List.replicate (pop xs) true) tail false
      simp only [List.length_replicate] at this
      rw [this]
      simp
  rw [hread] at t
  obtain ⟨r, hr, hf, _⟩ := t.run rfl
  refine ⟨r, hr, by rw [hf]; rfl, ?_, by omega⟩
  rw [hf]
  have e : (!decide (pop xs < d)) = decide (pop xs = d) := by
    rw [Bool.eq_iff_iff]; simp; omega
  simp only [cfg, e]

end PopEq

/-! ## One-tape steps -/

namespace One

def cfg {s : ℕ} (q : Fin s) (A : List Bool) (h : ℕ) : Configuration 1 s := ⟨q, ![h], ![A]⟩

theorem step_cfg {s : ℕ} (p : Machine 1 s) (q next : Fin s) (A : List Bool) (h : ℕ) (w : Option Bool) (m : HeadMove)
    (hr : p.rule q ![readTapeBit A h] = some ⟨next, ![w], ![m]⟩) :
    step p (cfg q A h) = some (cfg next (NearCubicWires.WireExponent3_5.GF2.Two.wr A h w) (m.apply h)) := by
  have hs : (cfg q A h).scanned = ![readTapeBit A h] := by
    funext i; fin_cases i; rfl
  unfold step
  rw [hs]
  change (p.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i; cases w <;> rfl

end One

/-! ## `Seek`: the cursor of a framed word to its terminator -/

namespace Seek
open One (cfg)

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then ⟨1, ![none], ![.right]⟩ else ⟨2, ![none], ![.stay]⟩)
    else if q.val = 1 then some ⟨0, ![none], ![.right]⟩
    else none

theorem mark_step (A : List Bool) (h : ℕ) (hr : readTapeBit A h = true) :
    step machine (cfg 0 A h) = some (cfg 1 A (h + 1)) := by
  have := One.step_cfg machine 0 1 A h none .right (by simp [machine, hr])
  simpa [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] using this

theorem bit_step (A : List Bool) (h : ℕ) : step machine (cfg 1 A h) = some (cfg 0 A (h + 1)) := by
  have := One.step_cfg machine 1 0 A h none .right (by simp [machine])
  simpa [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] using this

theorem end_step (A : List Bool) (h : ℕ) (hr : readTapeBit A h = false) :
    step machine (cfg 0 A h) = some (cfg 2 A h) := by
  have := One.step_cfg machine 0 2 A h none .stay (by simp [machine, hr])
  simpa [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] using this

theorem timed (tail : List Bool) : ∀ (w pre : List Bool),
    Timed machine (2 * w.length + 1) (cfg 0 (pre ++ frame w ++ tail) pre.length)
      (cfg 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length)) := by
  intro w
  induction w with
  | nil =>
    intro pre
    have hr : readTapeBit (pre ++ frame [] ++ tail) pre.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre tail false
    simpa using Timed.single (p := machine) rfl (end_step _ _ hr)
  | cons a w ih =>
    intro pre
    have hr : readTapeBit (pre ++ frame (a :: w) ++ tail) pre.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre (a :: (frame w ++ tail)) true
    have t1 := Timed.single (p := machine) rfl (mark_step _ _ hr)
    have t2 := Timed.single (p := machine) rfl (bit_step (pre ++ frame (a :: w) ++ tail) (pre.length + 1))
    have tail' := ih (pre ++ [true, a])
    have e0 : pre ++ [true, a] ++ frame w ++ tail = pre ++ frame (a :: w) ++ tail := by simp [frame]
    rw [e0, show (pre ++ [true, a]).length = pre.length + 1 + 1 by simp,
      show pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (a :: w).length by simp; omega] at tail'
    have := (t1.trans t2).trans tail'
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

/-- **Seek**: from the start of `frame w`, the cursor stops on its terminator, the tape unchanged. -/
theorem run (pre w tail : List Bool) :
    Step machine (2 * w.length + 1) ![pre.length] ![pre ++ frame w ++ tail]
      ![pre.length + 2 * w.length] ![pre ++ frame w ++ tail] := by
  obtain ⟨r, hr, hf, _⟩ := (timed tail w pre).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end Seek

/-! ## `UExtend`: `frame (1^i)` to `frame (1^{i+1})` at its terminator -/

theorem write_overlay_last (P B : List Bool) (b c : Bool) :
    writeTapeBit (overlay (P ++ [b]) B) P.length c = overlay (P ++ [c]) B := by
  unfold overlay
  simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
  exact write_mid P _ b c

theorem frame_ones_succ (i : ℕ) :
    frame (List.replicate (i + 1) true) = Streaming.marks (List.replicate i true) ++ [true, true, false] := by
  rw [List.replicate_succ', Streaming.frame_append]
  simp [frame]

theorem frame_ones (i : ℕ) : frame (List.replicate i true) = Streaming.marks (List.replicate i true) ++ [false] := by
  have := Streaming.frame_append (List.replicate i true) []
  simpa [frame] using this

namespace UExtend
open One (cfg)

def machine : Machine 1 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q _ =>
    if q.val = 0 then some ⟨1, ![some true], ![.right]⟩
    else if q.val = 1 then some ⟨2, ![some true], ![.right]⟩
    else if q.val = 2 then some ⟨3, ![some false], ![.stay]⟩
    else none

/-- **UExtend**: at the terminator of `frame (1^i)` (over any backing), the word `frame (1^{i+1})`; the cursor ends on
the new terminator. -/
theorem run (i : ℕ) (B : List Bool) :
    Step machine 3 ![2 * i] ![overlay (frame (List.replicate i true)) B]
      ![2 * i + 2] ![overlay (frame (List.replicate (i + 1) true)) B] := by
  rw [frame_ones, frame_ones_succ]
  set P := Streaming.marks (List.replicate i true) with hP
  have hPl : P.length = 2 * i := by simp [hP]
  have e1 : writeTapeBit (overlay (P ++ [false]) B) (2 * i) true = overlay (P ++ [true]) B := by
    rw [← hPl]; exact write_overlay_last P B false true
  have e2 : writeTapeBit (overlay (P ++ [true]) B) (2 * i + 1) true = overlay (P ++ [true, true]) B := by
    have := overlay_write (P ++ [true]) B true
    simp only [List.length_append, List.length_singleton, hPl, List.append_assoc, List.singleton_append] at this
    exact this
  have e3 : writeTapeBit (overlay (P ++ [true, true]) B) (2 * i + 1 + 1) false =
      overlay (P ++ [true, true, false]) B := by
    have := overlay_write (P ++ [true, true]) B false
    simp only [List.length_append, List.length_cons, List.length_nil, hPl, List.append_assoc,
      List.cons_append, List.nil_append] at this
    simpa [Nat.add_assoc] using this
  have hs1 := One.step_cfg machine 0 1 (overlay (P ++ [false]) B) (2 * i) (some true) .right (by simp [machine])
  have hs2 := One.step_cfg machine 1 2 (overlay (P ++ [true]) B) (2 * i + 1) (some true) .right (by simp [machine])
  have hs3 := One.step_cfg machine 2 3 (overlay (P ++ [true, true]) B) (2 * i + 1 + 1) (some false) .stay
    (by simp [machine])
  simp only [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] at hs1 hs2 hs3
  rw [e1] at hs1
  rw [e2] at hs2
  rw [e3] at hs3
  have t := ((Timed.single (p := machine) rfl hs1).trans (Timed.single (p := machine) rfl hs2)).trans
    (Timed.single (p := machine) rfl hs3)
  obtain ⟨r, hr, hf, _⟩ := t.run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf]; simp [One.cfg]

end UExtend

/-! ## `Put b`: append one bit at the cursor -/

namespace Put
open One (cfg)

def machine (b : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, ![some b], ![.right]⟩ else none

theorem run (b : Bool) (out B : List Bool) :
    Step (machine b) 1 ![out.length] ![overlay out B] ![(out ++ [b]).length] ![overlay (out ++ [b]) B] := by
  have hs := One.step_cfg (machine b) 0 1 (overlay out B) out.length (some b) .right (by simp [machine])
  simp only [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr, overlay_write] at hs
  obtain ⟨r, hr, hf, _⟩ := (Timed.single (p := machine b) rfl hs).run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [One.cfg]
  · rw [hf]; rfl

end Put

end NearCubicWires.WireExponent3_5.ListMachine.Print
