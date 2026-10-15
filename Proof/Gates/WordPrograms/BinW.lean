import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.UnionMachineRegRatMul
import Proof.Wire_3_5.OutMachineHalf
import Proof.Wire_3_5.UnionMachineRoundDiv

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms.BinW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Round (mapS_shl mapS_shl_carry mapS_keepA binary_mod)

variable {ns nr : ℕ}

/-! ## The number format -/

theorem binary_inj (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) : binary W a = binary W b ↔ a = b := by
  constructor
  · intro h
    rw [← binary_value W a ha, ← binary_value W b hb, h]
  · rintro rfl; rfl

theorem numOn_sets_self (σ : WState ns nr) (X : Fin (ns + 1)) (W v : ℕ) (h : σ.sh X = 0) :
    NumOn (σ.sets X (frame (binary W v))) X W v := ⟨by simp, by simpa using h⟩

theorem numOn_sets_ne {σ : WState ns nr} {X Y : Fin (ns + 1)} {W v : ℕ} (h : NumOn σ Y W v) (hXY : Y ≠ X)
    (l : List Bool) : NumOn (σ.sets X l) Y W v := ⟨by simp [Function.update_of_ne hXY, h.1], by simpa using h.2⟩

theorem numOn_setv {σ : WState ns nr} {Y : Fin (ns + 1)} {W v : ℕ} (h : NumOn σ Y W v) (r : Fin nr) (x : ℕ) :
    NumOn (σ.setv r x) Y W v := ⟨by simpa using h.1, by simpa using h.2⟩

theorem frame_frameP (W v : ℕ) : frame (binary W v) = frameP (binary W v) ++ false :: [] := frame_eq_frameP _

theorem sets_sets (σ : WState ns nr) (i : Fin (ns + 1)) (x y : List Bool) : (σ.sets i x).sets i y = σ.sets i y :=
  WState.eq rfl (by simp) rfl rfl

theorem sets_same {σ : WState ns nr} {i : Fin (ns + 1)} {x : List Bool} (h : σ.st i = x) : σ.sets i x = σ :=
  WState.eq rfl (by rw [← h]; simp) rfl rfl

theorem setv_same {σ : WState ns nr} {r : Fin nr} {x : ℕ} (h : σ.val r = x) : σ.setv r x = σ := by
  rw [← h]; exact wsetv_same σ r

section Facade
variable (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R)

/-- `A := 0` (`B`: any width-`W` word). -/
def zero (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (zeroB A B F R)
/-- `A := 1`. -/
def one (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (oneB A B F R)
/-- `A := a + 1`. -/
def inc (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (incB A B F R)
/-- `A := a + b`. -/
def add (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (addB A B F R)
/-- `A := a − b` (`b ≤ a`). -/
def sub (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (subB A B F R)
/-- `F := [a < b]`. -/
def lt (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (ltB A B F R)
/-- `A := b`. -/
def copy (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (copyB A B F R)
/-- `A := 2a mod 2^W`. -/
def shl (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (shlB A B F R)
/-- `A := ⌊a / 2⌋`. -/
def half (A : Fin (ns + 1)) (R : Fin nr) : WMX ns nr := .wm (NearCubicWires.WireExponent3_5.FinalPass.Out.Half.halfW A R)
/-- `C := a·b` (scratch word `S` ends at `0`, scratch registers `F R G`). -/
def mul (A B C S : Fin (ns + 1)) (F R G : Fin nr) : WMX ns nr := .wm (mulB A B C S F R G)

include hAB hFR

theorem zero_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (zero A B F R) σ (σ.sets A (frame (binary W 0))) (41 * W + 3) :=
  WXExec.wm (zeroB_spec cap W hAB hFR σ a b hA hB hF hR hcap)

theorem one_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hW : 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (one A B F R) σ (σ.sets A (frame (binary W 1))) (41 * W + 7) :=
  WXExec.wm (oneB_spec cap W hAB hFR σ a b hA hB hF hR hW hcap)

theorem inc_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (ha : a + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (inc A B F R) σ (σ.sets A (frame (binary W (a + 1)))) (41 * W + 7) :=
  WXExec.wm (incB_spec cap W hAB hFR σ a b hA hB hF hR ha hcap)

theorem add_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hab : a + b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (add A B F R) σ (σ.sets A (frame (binary W (a + b)))) (41 * W + 3) :=
  WXExec.wm (addB_spec cap W hAB hFR σ a b hA hB hF hR hab hcap)

theorem sub_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hba : b ≤ a) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (sub A B F R) σ (σ.sets A (frame (binary W (a - b)))) (41 * W + 9) :=
  WXExec.wm (subB_spec cap W hAB hFR σ a b hA hB hF hR hba ha hcap)

theorem lt_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (lt A B F R) σ (σ.setv F (decide (a < b)).toNat) (41 * W + 3) :=
  WXExec.wm (ltB_spec cap W hAB hFR σ a b hA hB hF hR ha hb hcap)

theorem copy_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (copy A B F R) σ (σ.sets A (frame (binary W b))) (41 * W + 3) :=
  WXExec.wm (copyB_spec cap W hAB hFR σ a b hA hB hF hR hcap)

theorem shl_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (shl A B F R) σ (σ.sets A (frame (binary W (2 * a)))) (41 * W + 8) :=
  WXExec.wm (shlB_spec cap W hAB hFR σ a b hA hB hF hR hcap)

omit hAB hFR in
theorem half_spec (σ : WState ns nr) (a : ℕ) (hA : NumOn σ A W a) (hR : σ.val R = 0) (ha : a < 2 ^ W)
    (hcap : 2 * W ≤ cap) : WXExec cap (half A R) σ (σ.sets A (frame (binary W (a / 2)))) (34 * W + 3) :=
  WXExec.wm (NearCubicWires.WireExponent3_5.FinalPass.Out.Half.halfW_spec cap A R W a σ hA hR ha hcap)

omit hAB hFR in
theorem mul_spec {C S : Fin (ns + 1)} {G : Fin nr} (hAB : A ≠ B) (hAC : A ≠ C) (hAS : A ≠ S) (hBC : B ≠ C)
    (hBS : B ≠ S) (hCS : C ≠ S) (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G) (σ : WState ns nr) (a b c s : ℕ)
    (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hC : NumOn σ C W c) (hS : NumOn σ S W s) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hG : σ.val G = 0) (hab : a * b < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (mul A B C S F R G) σ ((σ.sets C (frame (binary W (a * b)))).sets S (frame (binary W 0)))
      (mulCost W) :=
  WXExec.wm (mulB_spec cap W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b c s hA hB hC hS hF hR hG hab hb hcap)

end Facade

theorem mulCost_le (W : ℕ) : mulCost W ≤ 300 * (W + 1) ^ 2 := by
  unfold mulCost; nlinarith

/-! ## Shift with carry in and carry out -/

/-- `A := 2a + c mod 2^W` with carry-in `c = F`, and `F :=` the bit shifted out. -/
def shlcW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass shOut shNxt A B F R

theorem shlcW_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (c : Bool) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = c.toNat) (hR : σ.val R = 0)
    (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (shlcW A B F R) σ ((σ.sets A (frame (binary W (2 * a + c.toNat)))).setv F
      (decide (2 ^ W ≤ 2 * a + c.toNat)).toNat) (41 * W + 3) := by
  have h := mapPass_spec cap shOut shNxt A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] c σ
    (by simp) (by rw [hA.1, frame_frameP]) hA.2 (by rw [hB.1, frame_frameP]) hB.2 hF hR (by simp; omega)
  rw [mapS_shl W a _ c (by simp), mapS_shl_carry W a _ c (by simp) ha, binary_length] at h
  rw [frame_frameP]
  exact WExec.mono h (by omega)

/-- `A := 2a + c mod 2^W`, `F :=` the bit shifted out (`F` holds the carry-in `c` before). -/
def shlc (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (shlcW A B F R)

theorem shlc_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (c : Bool) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = c.toNat) (hR : σ.val R = 0)
    (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (shlc A B F R) σ ((σ.sets A (frame (binary W (2 * a + c.toNat)))).setv F
      (decide (2 ^ W ≤ 2 * a + c.toNat)).toNat) (41 * W + 3) :=
  WXExec.wm (shlcW_spec cap W hAB hFR σ a b c hA hB hF hR ha hcap)

/-! ## Equality -/

/-- The equality pass's state: still equal so far. -/
def eqN (a b c : Bool) : Bool := c && (a == b)

theorem mapS_eq : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA eqN as bs c).2 = (c && decide (as = bs))
  | [], [], c, _ => by simp [mapS]
  | a :: as, b :: bs, c, h => by
    simp only [mapS]
    rw [mapS_eq as bs _ (by simpa using h)]
    cases a <;> cases b <;> cases c <;> simp [eqN]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- `F := [a = b]` (both words kept). -/
def eqW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (.inc F) (mapPass keepA eqN A B F R)

theorem eqW_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W)
    (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (eqW A B F R) σ (σ.setv F (decide (a = b)).toNat) (41 * W + 7) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  rw [hF] at h1
  have h2 := mapPass_spec cap keepA eqN A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] true
    (σ.setv F 1) (by simp) (by simp [hA.1, frame_frameP]) (by simpa using hA.2) (by simp [hB.1, frame_frameP])
    (by simpa using hB.2) (by simp) (by simp [Ne.symm hFR, hR]) (by simp; omega)
  rw [mapS_keepA eqN _ _ _ (by simp), mapS_eq _ _ _ (by simp), binary_length] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  have e : decide (binary W a = binary W b) = decide (a = b) := by
    simp only [binary_inj W a b ha hb]
  rw [Bool.true_and, e]
  apply WState.eq
  · rfl
  · simp [← frame_frameP, ← hA.1]
  · simp
  · rfl

/-- `F := [a = b]`. -/
def eq (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (eqW A B F R)

theorem eq_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W)
    (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (eq A B F R) σ (σ.setv F (decide (a = b)).toNat) (41 * W + 7) :=
  WXExec.wm (eqW_spec cap W hAB hFR σ a b hA hB hF hR ha hb hcap)

/-! ## The width of a word into a register -/

/-- Walk the frame of `A`, counting its bits into `K` and `T`. -/
def widthLoop (A : Fin (ns + 1)) (K T : Fin nr) : WM ns nr :=
  .whs A (.seq (.fwd A) (.seq (.fwd A) (.seq (.inc K) (.inc T))))

/-- Walk back by `T`. -/
def backLoop (A : Fin (ns + 1)) (T : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (.seq (.bwd A) (.bwd A)))

/-- `K := W`, the width of the word on `A` (scratch `T`). -/
def widthW (A : Fin (ns + 1)) (K T : Fin nr) : WM ns nr := .seq (widthLoop A K T) (backLoop A T)

section Width
variable (cap : ℕ) {A : Fin (ns + 1)} {K T : Fin nr} (hKT : K ≠ T)
include hKT

theorem widthLoop_spec (W a : ℕ) (hW : W ≤ cap) : ∀ (m k : ℕ) (σ : WState ns nr), k + m = W →
    σ.st A = frame (binary W a) → σ.sh A = 2 * k → σ.val K = k → σ.val T = k →
    WExec cap (widthLoop A K T) σ (((σ.seth A (2 * W)).setv K W).setv T W) (13 * m + 1)
  | 0, k, σ, hk, hA, hAh, hK, hT => by
    have hb : wbit σ A = false := by
      unfold wbit; rw [hA, hAh, show k = W by omega]; exact frame_end W a
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
  | m + 1, k, σ, hk, hA, hAh, hK, hT => by
    have hb : wbit σ A = true := by
      unfold wbit; rw [hA, hAh]; exact frame_marker W a k (by omega)
    have h1 := WExec.fwd (cap := cap) A σ
    have h2 := WExec.fwd (cap := cap) A (σ.seth A (σ.sh A + 1))
    have h3 := WExec.inc (cap := cap) K ((σ.seth A (σ.sh A + 1)).seth A ((σ.seth A (σ.sh A + 1)).sh A + 1))
      (by simp; omega)
    set σ3 := ((σ.seth A (σ.sh A + 1)).seth A ((σ.seth A (σ.sh A + 1)).sh A + 1)) with hσ3
    have h4 := WExec.inc (cap := cap) T (σ3.setv K (σ3.val K + 1)) (by simp [hσ3, Ne.symm hKT]; omega)
    set τ := (σ3.setv K (σ3.val K + 1)).setv T ((σ3.setv K (σ3.val K + 1)).val T + 1) with hτ
    have ih := widthLoop_spec W a hW m (k + 1) τ (by omega) (by simp [hτ, hσ3, hA]) (by simp [hτ, hσ3, hAh]; omega)
      (by simp [hτ, hσ3, hKT, hK]) (by simp [hτ, hσ3, Ne.symm hKT, hT])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ih) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [hτ, hσ3, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext j; simp only [hτ, hσ3, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl

omit hKT in
theorem backLoop_spec : ∀ (j : ℕ) (σ : WState ns nr), σ.val T = j → σ.sh A = 2 * j → j ≤ cap →
    WExec cap (backLoop A T) σ ((σ.setv T 0).seth A 0) (7 * j + 1)
  | 0, σ, hT, hAh, _ => by
    refine WExec.cast cap (WExec.whrF hT) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext i; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
  | j + 1, σ, hT, hAh, hj => by
    have h1 := WExec.dec (cap := cap) T σ (by omega)
    have h2 := WExec.bwd (cap := cap) A (σ.setv T (σ.val T - 1))
    have h3 := WExec.bwd (cap := cap) A ((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1))
    set τ := ((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1)).seth A
      (((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1)).sh A - 1) with hτ
    have ih := backLoop_spec j τ (by simp [hτ, hT]) (by simp [hτ, hAh]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [hτ, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext i; simp only [hτ, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl

/-- **`K := W`**, the width of the number on `A`; `T` scratch (`0` before and after). -/
theorem widthW_spec (W a : ℕ) (σ : WState ns nr) (hA : NumOn σ A W a) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hW : W ≤ cap) : WExec cap (widthW A K T) σ (σ.setv K W) (20 * W + 3) := by
  have h1 := widthLoop_spec cap hKT W a hW W 0 σ (by omega) hA.1 (by simp [hA.2]) hK hT
  set τ := ((σ.seth A (2 * W)).setv K W).setv T W with hτ
  have h2 := backLoop_spec cap (A := A) (T := T) W τ (by simp [hτ]) (by simp [hτ]) hW
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext i; simp only [hτ, WState.seth_sh, WState.setv_sh, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all [hA.2]
  · rfl
  · funext i; simp only [hτ, WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  · rfl

end Width

/-- `K := W` (as a `WMX` instruction). -/
def width (A : Fin (ns + 1)) (K T : Fin nr) : WMX ns nr := .wm (widthW A K T)

theorem width_spec (cap : ℕ) {A : Fin (ns + 1)} {K T : Fin nr} (hKT : K ≠ T) (W a : ℕ) (σ : WState ns nr)
    (hA : NumOn σ A W a) (hK : σ.val K = 0) (hT : σ.val T = 0) (hW : W ≤ cap) :
    WXExec cap (width A K T) σ (σ.setv K W) (20 * W + 3) :=
  WXExec.wm (widthW_spec cap hKT W a σ hA hK hT hW)

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] zero one inc add sub lt copy shl half mul shlcW shlc eqW eq widthW width

end NearCubicGates.Close.WordPrograms.BinW
