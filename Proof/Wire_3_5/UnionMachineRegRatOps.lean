import Proof.Wire_3_5.SelectionMachineScanW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.Round (subO geN mapS_sub mapS_ge mapS_keepA mapS_shl)

variable {ns nr : ℕ}

/-! ## Value lemmas -/

/-- The final carry of a pass does not depend on what it writes. -/
theorem mapS_snd (out out' nxt : Bool → Bool → Bool → Bool) :
    ∀ (as bs : List Bool) (c : Bool), (mapS out nxt as bs c).2 = (mapS out' nxt as bs c).2
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, c => by
    simp only [mapS]
    exact mapS_snd out out' nxt as bs (nxt a b c)

/-- The subtractor's final carry is `1` (no borrow) when `b ≤ a < 2^W`. -/
theorem mapS_sub_carry (w x y : ℕ) (hyx : y ≤ x) (hx : x < 2 ^ w) :
    (mapS subO geN (binary w x) (binary w y) true).2 = true := by
  rw [mapS_snd subO keepA geN, mapS_ge w x y true]
  have e1 : x % 2 ^ w = x := Nat.mod_eq_of_lt hx
  have e2 : y % 2 ^ w = y := Nat.mod_eq_of_lt (by omega)
  simp [e1, e2, hyx]

/-- The comparator's final carry at carry-in `0`, over `b` against `a`, is `[a < b]`. -/
theorem mapS_lt_carry (w x y : ℕ) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    (mapS keepA geN (binary w y) (binary w x) false).2 = decide (x < y) := by
  rw [mapS_ge w y x false]
  have e1 : x % 2 ^ w = x := Nat.mod_eq_of_lt hx
  have e2 : y % 2 ^ w = y := Nat.mod_eq_of_lt hy
  rw [e1, e2]
  simp only [Bool.not_false, Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega)

/-- The one-writer's final carry is `0` on a nonempty word. -/
theorem mapS_one_snd : ∀ (as bs : List Bool), as.length = bs.length → 1 ≤ as.length →
    (mapS oneOut oneNxt as bs true).2 = false
  | [], _, _, h1 => by simp at h1
  | a :: as, b :: bs, h, _ => by
    simp only [mapS, oneNxt]
    rw [mapS_zero_state as bs (by simpa using h)]
  | _ :: _, [], h, _ => by simp at h

/-! ## The ops -/

def addB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := addTOT B A F R

def incB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := incCNT A B F R

def zeroB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := zeroCNT A B F R

/-- `A := a − b` (carry-in `1`, the carry returns to `0`). -/
def subB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (.inc F) (.seq (mapPass subO geN A B F R) (.dec F))

/-- `F := [a < b]` (both words kept). -/
def ltB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass keepA geN B A F R

/-- `A := b`. -/
def copyB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass copyOut keepS A B F R

/-- `A := 1`. -/
def oneB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (.inc F) (mapPass oneOut oneNxt A B F R)

/-- `A := 2a mod 2^W` (the carry out is cleared). -/
def shlB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (mapPass shOut shNxt A B F R) (setFlag F false)

section Ops
variable (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R)
include hAB hFR

theorem addB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hab : a + b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (addB A B F R) σ (σ.sets A (frame (binary W (a + b)))) (41 * W + 3) :=
  addTOT_spec cap W (Ne.symm hAB) hFR σ b a hB hA hF hR hab hcap

theorem incB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (incB A B F R) σ (σ.sets A (frame (binary W (a + 1)))) (41 * W + 7) :=
  incCNT_spec cap W hAB hFR σ a b hA hB hF hR ha hcap

theorem zeroB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (zeroB A B F R) σ (σ.sets A (frame (binary W 0))) (41 * W + 3) :=
  zeroCNT_spec cap W hAB hFR σ a b hA hB hF hR hcap

theorem subB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hba : b ≤ a) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (subB A B F R) σ (σ.sets A (frame (binary W (a - b)))) (41 * W + 9) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  set σ1 := σ.setv F (σ.val F + 1) with hσ1
  have h2 := mapPass_spec cap subO geN A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] true σ1
    (by simp) (by simp [hσ1, hA.1, frame_eq_frameP]) (by simp [hσ1, hA.2]) (by simp [hσ1, hB.1, frame_eq_frameP])
    (by simp [hσ1, hB.2]) (by simp [hσ1, hF]) (by simp [hσ1, Ne.symm hFR, hR]) (by simp; omega)
  rw [mapS_sub W a b hba ha, mapS_sub_carry W a b hba ha] at h2
  set σ2 := (σ1.sets A (frameP (binary W (a - b)) ++ [false])).setv F true.toNat with hσ2
  have h3 := WExec.dec (cap := cap) F σ2 (by simp [hσ2]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [hσ2, hσ1, WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
  · funext x; simp only [hσ2, hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

theorem ltB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (ltB A B F R) σ (σ.setv F (decide (a < b)).toNat) (41 * W + 3) := by
  have h := mapPass_spec cap keepA geN B A F R (Ne.symm hAB) hFR (by omega) (binary W b) (binary W a) [] [false]
    false σ (by simp) (by simp [hB.1, frame_eq_frameP]) hB.2 (by simp [hA.1, frame_eq_frameP]) hA.2
    (by simp [hF]) hR (by simp; omega)
  rw [mapS_keepA geN _ _ _ (by simp), mapS_lt_carry W a b ha hb] at h
  refine WExec.cast cap h ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp [hB.1, frame_eq_frameP]
  · rfl
  · rfl

theorem copyB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (copyB A B F R) σ (σ.sets A (frame (binary W b))) (41 * W + 3) := by
  have h := mapPass_spec cap copyOut keepS A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false]
    false σ (by simp) (by simp [hA.1, frame_eq_frameP]) hA.2 (by simp [hB.1, frame_eq_frameP]) hB.2
    (by simp [hF]) hR (by simp; omega)
  rw [mapS_copy _ _ _ (by simp)] at h
  refine WExec.cast cap h ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
  · funext x; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

theorem oneB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hW : 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (oneB A B F R) σ (σ.sets A (frame (binary W 1))) (41 * W + 7) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  set σ1 := σ.setv F (σ.val F + 1) with hσ1
  have h2 := mapPass_spec cap oneOut oneNxt A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] true σ1
    (by simp) (by simp [hσ1, hA.1, frame_eq_frameP]) (by simp [hσ1, hA.2]) (by simp [hσ1, hB.1, frame_eq_frameP])
    (by simp [hσ1, hB.2]) (by simp [hσ1, hF]) (by simp [hσ1, Ne.symm hFR, hR]) (by simp; omega)
  rw [mapS_one _ _ (by simp) (by simp; omega), mapS_one_snd _ _ (by simp) (by simp; omega)] at h2
  simp only [binary_length] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [hσ1, WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
  · funext x; simp only [hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

theorem shlB_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (shlB A B F R) σ (σ.sets A (frame (binary W (2 * a)))) (41 * W + 8) := by
  have h1 := mapPass_spec cap shOut shNxt A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false]
    false σ (by simp) (by simp [hA.1, frame_eq_frameP]) hA.2 (by simp [hB.1, frame_eq_frameP]) hB.2
    (by simp [hF]) hR (by simp; omega)
  rw [mapS_shl W a (binary W b) false (by simp)] at h1
  set c := (mapS shOut shNxt (binary W a) (binary W b) false).2 with hc
  set σ1 := (σ.sets A (frameP (binary W (2 * a + false.toNat)) ++ [false])).setv F c.toNat with hσ1
  have h2 := setFlag_spec cap F false c σ1 (by simp [hσ1]) (by omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [hσ1, WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP,
      Bool.toNat_false, Nat.add_zero]
  · funext x; simp only [hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

end Ops

end NearCubicWires.WireExponent3_5.UnionMachine.RegRat
