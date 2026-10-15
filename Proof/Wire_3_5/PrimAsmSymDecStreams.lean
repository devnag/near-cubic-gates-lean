import Proof.Wire_3_5.PrimAsmSymDecNums

/-! # PA (d)-SYM decode, part 5: the cell's streams (the request's length, the unit index, rewinds)

The decode reads its request `frame w` (stream `0`) and its unit index `1^j` (stream `2`) and must leave both heads at
`0` (`FiltSetupIface2.FsIn2`, `CellUnit.DecOK`'s callers). `frame w` is `w`'s bits as marked pairs, closed by `false`,
and the request's tail is arbitrary, so the decode measures the request first.

* `measW` / **`meas_spec`**: from head `0` on `frame w`, the head at `2|w|` and `|w|` added to a register;
* `readUW` / **`readU_spec`**: from head `0` on `1^j`, the head at `j` and `j` added to a register;
* `frame_append`, `readTapeBit_append`.

Paper quantities of the main type: the request word's length and the unit index `j` of the writer's loop. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

section Streams
variable {ns nr : ℕ} (cap : ℕ)

theorem frame_append (pre w : List Bool) : frame (pre ++ w) = pre.flatMap (fun b => [true, b]) ++ frame w := by
  induction pre with
  | nil => simp
  | cons b pre ih => simp [frame, ih]

theorem flatMap_pair_length (pre : List Bool) : (pre.flatMap (fun b => [true, b])).length = 2 * pre.length := by
  induction pre with
  | nil => simp
  | cons b pre ih => simp [ih]; ring

theorem readTapeBit_append (l r : List Bool) : readTapeBit (l ++ r) l.length = readTapeBit r 0 := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]

/-- Measure a framed word: over each marked pair, two steps and one count. -/
def measW (s : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whs s (.seq (.fwd s) (.seq (.fwd s) (.inc c)))

theorem meas_loop (s : Fin (ns + 1)) (c : Fin nr) : ∀ (w pre : List Bool) (v : ℕ) (σ : WState ns nr),
    σ.st s = frame (pre ++ w) → σ.sh s = 2 * pre.length → σ.val c = v → v + w.length ≤ cap →
    WExec cap (measW s c) σ ((σ.seth s (2 * (pre ++ w).length)).setv c (v + w.length)) (9 * w.length + 1)
  | [], pre, v, σ, hst, hsh, hv, _ => by
    have hb : wbit σ s = false := by
      unfold wbit
      rw [hst, hsh, frame_append, ← flatMap_pair_length, readTapeBit_append]
      rfl
    have e : (σ.seth s (2 * (pre ++ []).length)).setv c (v + ([] : List Bool).length) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = s
        · subst hi; simp [hsh]
        · simp [Function.update_apply, hi]
      · rfl
      · funext r; by_cases hr : r = c
        · subst hr; simp [hv]
        · simp [Function.update_apply, hr]
      · rfl
    rw [e]
    exact WExec.whsF hb
  | b :: w, pre, v, σ, hst, hsh, hv, hc => by
    have hb : wbit σ s = true := by
      unfold wbit
      rw [hst, hsh, frame_append, ← flatMap_pair_length, readTapeBit_append]
      rfl
    have f1 := WExec.fwd (cap := cap) s σ
    have f2 := WExec.fwd (cap := cap) s (σ.seth s (σ.sh s + 1))
    have f3 := WExec.inc (cap := cap) c ((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1))
      (by simp [hv]; simp at hc; omega)
    have ih := meas_loop s c w (pre ++ [b]) (v + 1)
      ((((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1))).setv c
        (((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1)).val c + 1))
      (by simp [hst]) (by simp [hsh]; ring) (by simp [hv]) (by simp at hc; omega)
    have h := WExec.whsT hb (WExec.seq f1 (WExec.seq f2 f3)) ih
    refine WExec.cast cap h ?_ (by simp; ring_nf; omega)
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = c
      · subst hr; simp [hv]; omega
      · simp [Function.update_apply, hr]
    · rfl

/-- **Measuring the request**: from head `0` on `frame w`, the head at `2|w|` and `|w|` added to the register. -/
theorem meas_spec (s : Fin (ns + 1)) (c : Fin nr) (w : List Bool) (v : ℕ) (σ : WState ns nr) (hst : σ.st s = frame w)
    (hsh : σ.sh s = 0) (hv : σ.val c = v) (hc : v + w.length ≤ cap) :
    WExec cap (measW s c) σ ((σ.seth s (2 * w.length)).setv c (v + w.length)) (9 * w.length + 1) := by
  have := meas_loop cap s c w [] v σ (by simpa using hst) (by simpa using hsh) hv hc
  simpa using this

/-- Read a unary count: over each mark, one step and one count. -/
def readUW (s : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whs s (.seq (.fwd s) (.inc c))

theorem readU_loop (s : Fin (ns + 1)) (c : Fin nr) (j : ℕ) : ∀ (m : ℕ) (v : ℕ) (σ : WState ns nr),
    σ.st s = List.replicate j true → σ.sh s + m = j → σ.val c = v → v + m ≤ cap →
    WExec cap (readUW s c) σ ((σ.seth s j).setv c (v + m)) (7 * m + 1)
  | 0, v, σ, hst, hsh, hv, _ => by
    have hb : wbit σ s = false := by
      unfold wbit readTapeBit
      rw [hst, List.getD_eq_default _ _ (by simp; omega)]
    have e : (σ.seth s j).setv c (v + 0) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = s
        · subst hi; simp; omega
        · simp [Function.update_apply, hi]
      · rfl
      · funext r; by_cases hr : r = c
        · subst hr; simp [hv]
        · simp [Function.update_apply, hr]
      · rfl
    rw [e]
    exact WExec.whsF hb
  | m + 1, v, σ, hst, hsh, hv, hc => by
    have hb : wbit σ s = true := by
      unfold wbit readTapeBit
      rw [hst, List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    have f1 := WExec.fwd (cap := cap) s σ
    have f2 := WExec.inc (cap := cap) c (σ.seth s (σ.sh s + 1)) (by simp [hv]; omega)
    have ih := readU_loop s c j m (v + 1) ((σ.seth s (σ.sh s + 1)).setv c ((σ.seth s (σ.sh s + 1)).val c + 1))
      (by simp [hst]) (by simp; omega) (by simp [hv]) (by omega)
    have h := WExec.whsT hb (WExec.seq f1 f2) ih
    refine WExec.cast cap h ?_ (by ring_nf; omega)
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = c
      · subst hr; simp [hv]; omega
      · simp [Function.update_apply, hr]
    · rfl

/-- **Reading the unit index**: from head `0` on `1^j`, the head at `j` and `j` added to the register. -/
theorem readU_spec (s : Fin (ns + 1)) (c : Fin nr) (j v : ℕ) (σ : WState ns nr) (hst : σ.st s = List.replicate j true)
    (hsh : σ.sh s = 0) (hv : σ.val c = v) (hc : v + j ≤ cap) :
    WExec cap (readUW s c) σ ((σ.seth s j).setv c (v + j)) (7 * j + 1) :=
  readU_loop cap s c j j v σ hst (by omega) hv hc

end Streams

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
