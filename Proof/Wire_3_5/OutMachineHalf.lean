import Proof.Wire_3_5.OutMachineIface
import Proof.Wire_3_5.UnionMachineBinW

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Half
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ} (cap : ℕ)

/-- One coordinate: from bit `i`'s marker, read two cells on, write that bit over bit `i`, step to the next marker. -/
def halfStep (A : Fin (ns + 1)) (R : Fin nr) : WM ns nr :=
  .seq (.fwd A) (.seq (.fwd A) (.seq (.fwd A) (.seq
    (.ifs A (.seq (.bwd A) (.seq (.bwd A) (.wr A true))) (.seq (.bwd A) (.seq (.bwd A) (.wr A false))))
    (.seq (.fwd A) (.seq (.inc R) (.inc R))))))

/-- **`A := a / 2`**: the read-ahead loop over the markers, then back by the counter `R`. -/
def halfW (A : Fin (ns + 1)) (R : Fin nr) : WM ns nr := .seq (.whs A (halfStep A R)) (WM.rewind A R)

theorem frameP_app (u w : List Bool) : frameP (u ++ w) = frameP u ++ frameP w := by
  simp [frameP, List.flatMap_append]

theorem readTapeBit_ge (l : List Bool) (p : ℕ) (h : l.length ≤ p) : readTapeBit l p = false := by
  unfold readTapeBit
  exact List.getD_eq_default _ _ h

/-- The read-ahead: three cells past bit `i`'s marker is bit `i + 1`, or a blank past the end. -/
theorem rd_next (pre xs : List Bool) (x : Bool) :
    readTapeBit (frameP pre ++ frameP (x :: xs) ++ [false]) (2 * pre.length + 3) = xs.headD false := by
  cases xs with
  | nil =>
    apply readTapeBit_ge
    simp
  | cons y ys =>
    have e : frameP pre ++ frameP (x :: y :: ys) ++ [false] =
        (frameP pre ++ [true, x, true]) ++ y :: (frameP ys ++ [false]) := by simp
    have hl : 2 * pre.length + 3 = (frameP pre ++ [true, x, true]).length := by
      rw [List.length_append, frameP_length]; rfl
    rw [e, hl, readTapeBit_mid]
    rfl

theorem rd_marker (pre xs : List Bool) (x : Bool) :
    readTapeBit (frameP pre ++ frameP (x :: xs) ++ [false]) (2 * pre.length) = true := by
  have e : frameP pre ++ frameP (x :: xs) ++ [false] = frameP pre ++ true :: (x :: (frameP xs ++ [false])) := by simp
  rw [e, ← frameP_length, readTapeBit_mid]

theorem rd_end (w : List Bool) : readTapeBit (frameP w ++ [false]) (2 * w.length) = false := by
  rw [← frameP_length, readTapeBit_mid]

theorem wr_bit (pre xs : List Bool) (x b : Bool) :
    writeTapeBit (frameP pre ++ frameP (x :: xs) ++ [false]) (2 * pre.length + 1) b =
      frameP (pre ++ [b]) ++ frameP xs ++ [false] := by
  have e : frameP pre ++ frameP (x :: xs) ++ [false] = (frameP pre ++ [true]) ++ x :: (frameP xs ++ [false]) := by
    simp
  have hl : 2 * pre.length + 1 = (frameP pre ++ [true]).length := by
    rw [List.length_append, frameP_length]; rfl
  rw [e, hl, writeTapeBit_mid']
  simp [frameP_app]

theorem fwd_to (A : Fin (ns + 1)) (τ : WState ns nr) (x : ℕ) :
    WExec cap (.fwd A) (τ.seth A x) (τ.seth A (x + 1)) 1 := by
  have h := WExec.fwd (cap := cap) A (τ.seth A x)
  rwa [wseth_sh_self, wseth_seth] at h

theorem bwd_to (A : Fin (ns + 1)) (τ : WState ns nr) (x : ℕ) :
    WExec cap (.bwd A) (τ.seth A (x + 1)) (τ.seth A x) 1 := by
  have h := WExec.bwd (cap := cap) A (τ.seth A (x + 1))
  rwa [wseth_sh_self, Nat.add_sub_cancel, wseth_seth] at h

/-- One coordinate of the halving. -/
theorem halfStep_spec (A : Fin (ns + 1)) (R : Fin nr) (pre xs : List Bool) (x : Bool) (σ : WState ns nr)
    (hA : σ.st A = frameP pre ++ frameP (x :: xs) ++ [false]) (hh : σ.sh A = 2 * pre.length)
    (hR : σ.val R + 2 ≤ cap) :
    WExec cap (halfStep A R) σ
      (((σ.sets A (frameP (pre ++ [xs.headD false]) ++ frameP xs ++ [false])).seth A (2 * pre.length + 2)).setv R
        (σ.val R + 2)) 22 := by
  have e0 : σ = σ.seth A (2 * pre.length) := by rw [← hh, wseth_same]
  have s1 := fwd_to cap A σ (2 * pre.length)
  have s2 := fwd_to cap A σ (2 * pre.length + 1)
  have s3 := fwd_to cap A σ (2 * pre.length + 1 + 1)
  have hbit : wbit (σ.seth A (2 * pre.length + 1 + 1 + 1)) A = xs.headD false := by
    rw [wsbit_seth, hA]; exact rd_next pre xs x
  have t1 := bwd_to cap A σ (2 * pre.length + 1 + 1)
  have t2 := bwd_to cap A σ (2 * pre.length + 1)
  have t3 := WExec.wr (cap := cap) A (xs.headD false) (σ.seth A (2 * pre.length + 1))
  have ew : (σ.seth A (2 * pre.length + 1)).sets A (writeTapeBit ((σ.seth A (2 * pre.length + 1)).st A)
      ((σ.seth A (2 * pre.length + 1)).sh A) (xs.headD false)) =
      (σ.sets A (frameP (pre ++ [xs.headD false]) ++ frameP xs ++ [false])).seth A (2 * pre.length + 1) := by
    rw [wseth_sh_self, WState.seth_st, hA, wr_bit]; rfl
  rw [ew] at t3
  have br := WExec.seq t1 (WExec.seq t2 t3)
  have hif : WExec cap (.ifs A (.seq (.bwd A) (.seq (.bwd A) (.wr A true)))
      (.seq (.bwd A) (.seq (.bwd A) (.wr A false)))) (σ.seth A (2 * pre.length + 1 + 1 + 1))
      ((σ.sets A (frameP (pre ++ [xs.headD false]) ++ frameP xs ++ [false])).seth A (2 * pre.length + 1))
      (1 + 1 + (1 + 1 + 1) + 1) := by
    cases hb : xs.headD false
    · rw [hb] at hbit br; exact WExec.ifsF hbit br
    · rw [hb] at hbit br; exact WExec.ifsT hbit br
  set τ := σ.sets A (frameP (pre ++ [xs.headD false]) ++ frameP xs ++ [false]) with hτ
  have u1 := fwd_to cap A τ (2 * pre.length + 1)
  have u2 := WExec.inc (cap := cap) R (τ.seth A (2 * pre.length + 1 + 1)) (by simp [hτ]; omega)
  have u3 := WExec.inc (cap := cap) R ((τ.seth A (2 * pre.length + 1 + 1)).setv R
    ((τ.seth A (2 * pre.length + 1 + 1)).val R + 1)) (by simp [hτ]; omega)
  have all := WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq hif (WExec.seq u1 (WExec.seq u2 u3)))))
  rw [← e0] at all
  refine WExec.cast cap all ?_ (by omega)
  rw [wsetv_setv]
  simp only [hτ, WState.seth_val, WState.sets_val, wsetv_val_self]

/-- **The halving loop**: from bit `|pre|`'s marker, the bits `x :: xs` are shifted down one place (a blank `false`
enters at the top); the head ends on the end marker, `R` counts the moves. -/
theorem halfLoop_spec (A : Fin (ns + 1)) (R : Fin nr) :
    ∀ (xs pre : List Bool) (x : Bool) (σ : WState ns nr),
      σ.st A = frameP pre ++ frameP (x :: xs) ++ [false] → σ.sh A = 2 * pre.length →
      σ.val R + 2 * (xs.length + 1) ≤ cap →
      WExec cap (.whs A (halfStep A R)) σ
        (((σ.sets A (frameP (pre ++ xs ++ [false]) ++ [false])).seth A (2 * (pre.length + xs.length + 1))).setv R
          (σ.val R + 2 * (xs.length + 1))) (24 * (xs.length + 1) + 1)
  | [], pre, x, σ, hA, hh, hR => by
    have s := halfStep_spec cap A R pre [] x σ hA hh (by simpa using hR)
    have hm : wbit σ A = true := by unfold wbit; rw [hA, hh]; exact rd_marker pre [] x
    have he : wbit (((σ.sets A (frameP (pre ++ [([] : List Bool).headD false]) ++ frameP [] ++ [false])).seth A
        (2 * pre.length + 2)).setv R (σ.val R + 2)) A = false := by
      rw [wsbit_setv, wsbit_seth]
      simp only [WState.sets_st, Function.update_self, List.headD_nil, frameP_nil, List.append_nil]
      have := rd_end (pre ++ [false])
      simpa [Nat.mul_add] using this
    refine WExec.cast cap (WExec.whsT hm s (WExec.whsF he)) ?_ (by omega)
    simp [Nat.mul_add]
  | y :: ys, pre, x, σ, hA, hh, hR => by
    have s := halfStep_spec cap A R pre (y :: ys) x σ hA hh (by simp at hR; omega)
    have hm : wbit σ A = true := by unfold wbit; rw [hA, hh]; exact rd_marker pre (y :: ys) x
    set σ1 := ((σ.sets A (frameP (pre ++ [(y :: ys).headD false]) ++ frameP (y :: ys) ++ [false])).seth A
      (2 * pre.length + 2)).setv R (σ.val R + 2) with hσ1
    have ih := halfLoop_spec A R ys (pre ++ [y]) y σ1 (by simp [hσ1]) (by simp [hσ1]; omega)
      (by simp [hσ1] at hR ⊢; omega)
    refine WExec.cast cap (WExec.whsT hm s ih) ?_ (by simp; omega)
    simp only [hσ1]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> simp; omega
    · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> simp
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> simp; omega

theorem binary_half (W a : ℕ) (ha : a < 2 ^ (W + 1)) :
    binary (W + 1) (a / 2) = binary W (a / 2) ++ [false] := by
  rw [UnionMachine.BinW.binary_snoc]
  have h : a / 2 / 2 ^ W = 0 := by
    apply Nat.div_eq_of_lt
    rw [pow_succ] at ha
    omega
  simp [h]

/-- **`A := a / 2`** on a framed `W`-bit word. -/
theorem halfW_spec (A : Fin (ns + 1)) (R : Fin nr) (W a : ℕ) (σ : WState ns nr) (hA : NumOn σ A W a)
    (hR : σ.val R = 0) (ha : a < 2 ^ W) (hc : 2 * W ≤ cap) :
    WExec cap (halfW A R) σ (σ.sets A (frame (binary W (a / 2)))) (34 * W + 3) := by
  cases W with
  | zero =>
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    have hb : wbit σ A = false := by unfold wbit; rw [hA.1, hA.2]; rfl
    have r := wrewind_spec cap A R 0 σ hR (by omega)
    have e : (σ.setv R 0).seth A (σ.sh A - 0) = σ := by
      rw [Nat.sub_zero, ← hR, wsetv_same, wseth_same]
    rw [e] at r
    refine WExec.cast cap (WExec.seq (WExec.whsF hb) r) ?_ (by omega)
    rw [← hA.1]; exact (wsets_same σ A).symm
  | succ W =>
    have hbin : binary (W + 1) a = (a % 2 == 1) :: binary W (a / 2) := rfl
    have hA' : σ.st A = frameP [] ++ frameP ((a % 2 == 1) :: binary W (a / 2)) ++ [false] := by
      rw [hA.1, hbin, frame_eq_frameP]; simp
    have l := halfLoop_spec cap A R (binary W (a / 2)) [] (a % 2 == 1) σ hA' (by simp [hA.2])
      (by simp [hR]; omega)
    set σ1 := ((σ.sets A (frameP ([] ++ binary W (a / 2) ++ [false]) ++ [false])).seth A
      (2 * (([] : List Bool).length + (binary W (a / 2)).length + 1))).setv R
        (σ.val R + 2 * ((binary W (a / 2)).length + 1)) with hσ1
    have r := wrewind_spec cap A R (2 * (W + 1)) σ1 (by simp [hσ1, hR]) (by simp [hσ1, hR]; omega)
    refine WExec.cast cap (WExec.seq l r) ?_ (by simp; omega)
    simp only [hσ1]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h <;> simp [h, hA.2]
    · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> simp [frame_eq_frameP, binary_half W a ha]
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h <;> simp [h, hR]

end NearCubicWires.WireExponent3_5.FinalPass.Out.Half
