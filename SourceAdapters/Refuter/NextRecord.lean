import SourceAdapters.Refuter.CodeHeader

/-!
# Incrementing the witness field in place (input 7, the record codec, part 5)

proof of `cor:framed-refuter`: "For the second simulation, when `i<s`, it prepares `fr(x_{i+1})` … Parsing the outer
record, incrementing its witness field …". The field `z = w_i` holds `i` in binary, most significant bit
first (`unrank`), so its last cell is the least significant bit. `incr` walks back from
the last field cell flipping ones to zeros until it writes a one over the first zero (the carry chain of
`i+1`); if all `g` bits were ones (`i = s−1`, the last record) it sets the flag `LS` instead.
`testBit_succ_carry` is the arithmetic of the carry chain.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-! ## The carry chain -/

theorem testBit_succ_carry : ∀ (k i : ℕ), (∀ m < k, i.testBit m = true) → i.testBit k = false →
    ∀ m, (i + 1).testBit m = if m < k then false else if m = k then true else i.testBit m := by
  intro k
  induction k with
  | zero =>
    intro i _ hz m
    have he : i % 2 = 0 := by
      have := Nat.testBit_zero i ▸ hz; simpa using this
    cases m with
    | zero => simp [Nat.testBit_zero, Nat.add_mod, he]
    | succ m =>
      simp only [Nat.not_lt_zero, if_false, Nat.add_one_ne_zero, Nat.testBit_succ]
      congr 1; omega
  | succ k ih =>
    intro i hones hz m
    have ho : i % 2 = 1 := by
      have := hones 0 (by omega); rw [Nat.testBit_zero] at this; simpa using this
    have hh : (i + 1) / 2 = i / 2 + 1 := by omega
    cases m with
    | zero => simp [Nat.testBit_zero, Nat.add_mod, ho]
    | succ m =>
      rw [Nat.testBit_succ, hh, ih (i / 2) (fun m hm => by rw [Nat.testBit_div_two]; exact hones _ (by omega))
        (by rw [Nat.testBit_div_two]; exact hz) m, Nat.testBit_div_two]
      by_cases h1 : m < k
      · simp [h1, show m + 1 < k + 1 by omega]
      · by_cases h2 : m = k
        · subst h2; simp
        · simp [h1, h2, show ¬ m + 1 < k + 1 by omega]

theorem all_ones_last (g i : ℕ) (hi : i < 2 ^ g) (h : ∀ m < g, i.testBit m = true) : i + 1 = 2 ^ g := by
  have : i = 2 ^ g - 1 := by
    apply Nat.eq_of_testBit_eq; intro m
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hm : m < g
    · simp [hm, h m hm]
    · simp only [hm, decide_false]
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  omega

theorem not_all_ones (g i : ℕ) (hi : i < 2 ^ g) (k : ℕ) (hk : k < g) (hz : i.testBit k = false) : i + 1 < 2 ^ g := by
  rcases Nat.lt_or_ge (i + 1) (2 ^ g) with h | h
  · exact h
  · exfalso
    have : i = 2 ^ g - 1 := by omega
    rw [this, Nat.testBit_two_pow_sub_one] at hz
    simp [hk] at hz

/-! ## Writing one framed cell -/

theorem frame_set : ∀ (l : List Bool) (j : ℕ), j < l.length → ∀ b : Bool,
    writeTapeBit (RepairOrdinary.frame l) (2 * j + 1) b = RepairOrdinary.frame (l.set j b)
  | [], j, h, _ => absurd h (by simp)
  | a :: l, 0, _, b => by simp [RepairOrdinary.frame, writeTapeBit]
  | a :: l, j + 1, h, b => by
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring]
    simp only [RepairOrdinary.frame, writeTapeBit, List.set_cons_succ]
    rw [frame_set l j (by simp at h; omega) b]

theorem rd_frame_data (l : List Bool) (j : ℕ) (h : j < l.length) :
    readTapeBit (RepairOrdinary.frame l) (2 * j + 1) = l[j] := by
  rw [frame_eq_fpre, rd_fpre_data _ _ h]

/-- The list after clearing its last `k` entries. -/
def clrL (l : List Bool) : ℕ → List Bool
  | 0 => l
  | k + 1 => (clrL l k).set (l.length - 1 - k) false

@[simp] theorem clrL_length (l : List Bool) : ∀ k, (clrL l k).length = l.length
  | 0 => rfl
  | k + 1 => by simp [clrL, clrL_length l k]

theorem clrL_get (l : List Bool) : ∀ k j (h : j < (clrL l k).length),
    (clrL l k)[j] = if l.length - k ≤ j then false else l[j]'(by simpa using h)
  | 0, j, h => by
    have : j < l.length := by simpa using h
    simp [clrL]; intro h'; omega
  | k + 1, j, h => by
    simp only [clrL, List.getElem_set]
    split_ifs with h1 h2 h3 <;> first | rfl | (simp only [clrL_get l k] ; split_ifs <;> first | rfl | omega) | omega

/-! ## The increment loop -/

/-- `σ` with input stream `fr(l)` at head `xh` and the counters `TD = d`, `CONT = c`, `LS = ls`. -/
def ist (σ : St) (l : List Bool) (xh d c ls : ℕ) : St :=
  ⟨Function.update σ.sh sIN xh, Function.update σ.st sIN (RepairOrdinary.frame l),
   Function.update (Function.update (Function.update σ.val rTD d) rCONT c) rLS ls, σ.cell⟩

section Ist
variable (σ : St) (l : List Bool) (xh d c ls : ℕ)
@[simp] theorem ist_st_in : (ist σ l xh d c ls).st sIN = RepairOrdinary.frame l := by simp [ist]
@[simp] theorem ist_sh_in : (ist σ l xh d c ls).sh sIN = xh := by simp [ist]
@[simp] theorem ist_td : (ist σ l xh d c ls).val rTD = d := by simp [ist, Function.update_apply]
@[simp] theorem ist_cont : (ist σ l xh d c ls).val rCONT = c := by simp [ist, Function.update_apply]
@[simp] theorem ist_ls : (ist σ l xh d c ls).val rLS = ls := by simp [ist]
theorem ist_setv_td (v : ℕ) : (ist σ l xh d c ls).setv rTD v = ist σ l xh v c ls := by
  unfold ist WState.setv; congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
theorem ist_setv_cont (v : ℕ) : (ist σ l xh d c ls).setv rCONT v = ist σ l xh d v ls := by
  unfold ist WState.setv; congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
theorem ist_setv_ls (v : ℕ) : (ist σ l xh d c ls).setv rLS v = ist σ l xh d c v := by
  unfold ist WState.setv; congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
theorem ist_seth (h : ℕ) : (ist σ l xh d c ls).seth sIN h = ist σ l h d c ls := by
  unfold ist WState.seth; congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
theorem ist_sets (l' : List Bool) :
    (ist σ l xh d c ls).sets sIN (RepairOrdinary.frame l') = ist σ l' xh d c ls := by
  unfold ist WState.sets; congr 1; funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
end Ist

def incBody : Pg :=
  .ifs sIN (.seq (WMX.wr sIN false) (.seq (WMX.bwd sIN) (.seq (WMX.bwd sIN) (.seq (WMX.dec rTD)
    (.ifr rTD WMX.skip (.seq (clr rCONT) (WMX.inc rLS)))))))
    (.seq (WMX.wr sIN true) (clr rCONT))

def incLoop : Pg := .whr rCONT incBody

/-- One carry step over a one bit at field position `j` (from the right). -/
theorem incBody_one (σ : St) (L : List Bool) (N g j : ℕ) (hN : L.length = N) (hj : j < g) (hg : g ≤ N)
    (hb : L[N - 1 - j]'(by omega) = true) (hcap : g + 2 ≤ cap) :
    WXExec cap incBody (ist σ (clrL L j) (2 * N - 1 - 2 * j) (g - j) 1 0)
      (if j + 1 < g then ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 1 0
        else ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 0 1) 20 := by
  have hpos : 2 * N - 1 - 2 * j = 2 * (N - 1 - j) + 1 := by omega
  have hrd : wbit (ist σ (clrL L j) (2 * N - 1 - 2 * j) (g - j) 1 0) sIN = true := by
    simp only [wbit, ist_st_in, ist_sh_in, hpos]
    rw [rd_frame_data _ _ (by simp; omega), clrL_get, if_neg (by omega)]
    simpa using hb
  have w1 := WXExec.wr cap sIN false (ist σ (clrL L j) (2 * N - 1 - 2 * j) (g - j) 1 0)
  rw [ist_st_in, ist_sh_in, hpos, frame_set _ _ (by simp; omega), ← hpos,
    show N - 1 - j = (L.length - 1 - j) by omega, ist_sets] at w1
  have w2 := WXExec.bwd cap sIN (ist σ ((clrL L j).set (L.length - 1 - j) false) (2 * N - 1 - 2 * j) (g - j) 1 0)
  rw [ist_sh_in, ist_seth] at w2
  have w3 := WXExec.bwd cap sIN (ist σ ((clrL L j).set (L.length - 1 - j) false) (2 * N - 1 - 2 * j - 1) (g - j) 1 0)
  rw [ist_sh_in, ist_seth] at w3
  have w4 := WXExec.dec cap rTD (ist σ ((clrL L j).set (L.length - 1 - j) false) (2 * N - 1 - 2 * j - 1 - 1) (g - j) 1 0)
    (by simp; omega)
  rw [ist_td, ist_setv_td] at w4
  have hcl : (clrL L j).set (L.length - 1 - j) false = clrL L (j + 1) := rfl
  rw [hcl] at w1 w2 w3 w4
  have hx : 2 * N - 1 - 2 * j - 1 - 1 = 2 * N - 1 - 2 * (j + 1) := by omega
  rw [hx] at w3 w4
  have hd : g - j - 1 = g - (j + 1) := by omega
  rw [hd] at w4
  by_cases hlast : j + 1 < g
  · rw [if_pos hlast]
    have w5 : WXExec cap (.ifr rTD WMX.skip (.seq (clr rCONT) (WMX.inc rLS)))
        (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 1 0)
        (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 1 0) 1 :=
      WXExec.ifrT (by simp; omega) (WXExec.skip cap _)
    exact (WXExec.ifsT hrd (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 (WXExec.seq w4 w5))))).mono (by omega)
  · rw [if_neg hlast]
    have c1 := clr_spec cap rCONT (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 1 0) (by simp; omega)
    rw [ist_setv_cont, ist_cont] at c1
    have c2 := WXExec.inc cap rLS (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 0 0) (by simp; omega)
    rw [ist_setv_ls, ist_ls] at c2
    have w5 : WXExec cap (.ifr rTD WMX.skip (.seq (clr rCONT) (WMX.inc rLS)))
        (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 1 0)
        (ist σ (clrL L (j + 1)) (2 * N - 1 - 2 * (j + 1)) (g - (j + 1)) 0 (0 + 1)) _ :=
      WXExec.ifrF (by simp; omega) (WXExec.seq c1 c2)
    exact (WXExec.ifsT hrd (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 (WXExec.seq w4 w5))))).mono (by omega)

/-- The carry step over the first zero bit at field position `k`. -/
theorem incBody_zero (σ : St) (L : List Bool) (N g k : ℕ) (hN : L.length = N) (hk : k < g) (hg : g ≤ N)
    (hb : L[N - 1 - k]'(by omega) = false) (hcap : g + 2 ≤ cap) :
    WXExec cap incBody (ist σ (clrL L k) (2 * N - 1 - 2 * k) (g - k) 1 0)
      (ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) (g - k) 0 0) 20 := by
  have hpos : 2 * N - 1 - 2 * k = 2 * (N - 1 - k) + 1 := by omega
  have hrd : wbit (ist σ (clrL L k) (2 * N - 1 - 2 * k) (g - k) 1 0) sIN = false := by
    simp only [wbit, ist_st_in, ist_sh_in, hpos]
    rw [rd_frame_data _ _ (by simp; omega), clrL_get, if_neg (by omega)]
    simpa using hb
  have w1 := WXExec.wr cap sIN true (ist σ (clrL L k) (2 * N - 1 - 2 * k) (g - k) 1 0)
  rw [ist_st_in, ist_sh_in, hpos, frame_set _ _ (by simp; omega), ← hpos, ist_sets] at w1
  have c1 := clr_spec cap rCONT (ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) (g - k) 1 0) (by simp; omega)
  rw [ist_setv_cont, ist_cont] at c1
  exact (WXExec.ifsF hrd (WXExec.seq w1 c1)).mono (by omega)

theorem incLoop_all (σ : St) (L : List Bool) (N g : ℕ) (hN : L.length = N) (hg1 : 1 ≤ g) (hg : g ≤ N)
    (hb : ∀ m < g, L[N - 1 - m]'(by omega) = true) (hcap : g + 2 ≤ cap) :
    WXExec cap incLoop (ist σ L (2 * N - 1) g 1 0) (ist σ (clrL L g) (2 * N - 1 - 2 * g) 0 0 1) (g * 22 + 1) := by
  have e := whrE cap (r := rCONT) (body := incBody)
    (fun j => if j < g then ist σ (clrL L j) (2 * N - 1 - 2 * j) (g - j) 1 0
      else ist σ (clrL L g) (2 * N - 1 - 2 * g) 0 0 1) g 20
    (fun j hj => by simp [hj])
    (by simp)
    (fun j hj => by
      have := incBody_one cap σ L N g j hN hj hg (hb j hj) hcap
      simp only [hj, if_true]
      by_cases h1 : j + 1 < g
      · simpa [h1] using this
      · rw [if_neg h1] at this
        simp only [h1, if_false]
        have e1 : j + 1 = g := by omega
        rw [e1, Nat.sub_self] at this
        exact this)
  simp only [show (0 < g) by omega, if_true, Nat.mul_zero, Nat.sub_zero, if_neg (lt_irrefl g)] at e
  exact e

theorem incLoop_zero (σ : St) (L : List Bool) (N g k : ℕ) (hN : L.length = N) (hk : k < g) (hg : g ≤ N)
    (hb : ∀ m < k, L[N - 1 - m]'(by omega) = true) (hz : L[N - 1 - k]'(by omega) = false) (hcap : g + 2 ≤ cap) :
    WXExec cap incLoop (ist σ L (2 * N - 1) g 1 0)
      (ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) (g - k) 0 0) ((k + 1) * 22 + 1) := by
  have e := whrE cap (r := rCONT) (body := incBody)
    (fun j => if j ≤ k then ist σ (clrL L j) (2 * N - 1 - 2 * j) (g - j) 1 0
      else ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) (g - k) 0 0) (k + 1) 20
    (fun j hj => by simp [show j ≤ k by omega])
    (by simp)
    (fun j hj => by
      by_cases h1 : j < k
      · have := incBody_one cap σ L N g j hN (by omega) hg (hb j h1) hcap
        rw [if_pos (by omega : j + 1 < g)] at this
        simpa [show j ≤ k by omega, show j + 1 ≤ k by omega] using this
      · have e1 : j = k := by omega
        subst e1
        have := incBody_zero cap σ L N g j hN hk hg hz hcap
        simpa using this)
  simp only [Nat.zero_le, if_true, Nat.mul_zero, Nat.sub_zero, show ¬ (k + 1 ≤ k) by omega, if_false] at e
  exact e

def incr : Pg :=
  .seq (fwdK sIN rTE rTB) (.seq (fwdK sIN rTE rTB) (.seq (WMX.bwd sIN) (.seq (addR rS rTD rTA) (.seq (WMX.inc rCONT)
    (.seq incLoop (clr rTD))))))

theorem ist_self (σ : St) (L : List Bool) (hX : σ.st sIN = RepairOrdinary.frame L) (hh : σ.sh sIN = 0)
    (hd : σ.val rTD = 0) (hc : σ.val rCONT = 0) (hl : σ.val rLS = 0) : ist σ L 0 0 0 0 = σ := by
  unfold ist; cases σ
  simp only at hX hh hd hc hl ⊢
  congr 1
  · funext j; by_cases hj : j = sIN <;> simp_all [Function.update_apply]
  · funext j; by_cases hj : j = sIN <;> simp_all [Function.update_apply]
  · funext r; simp only [Function.update_apply]; split_ifs <;> simp_all

/-- The incremented field, or the last-record flag. -/
def incrOut (σ : St) (L : List Bool) (N g : ℕ) (k : Option ℕ) : St :=
  match k with
  | none => ist σ (clrL L g) (2 * N - 1 - 2 * g) 0 0 1
  | some k => ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) 0 0 0

set_option maxHeartbeats 400000 in
/-- **The increment** (proof of `cor:framed-refuter`): `k = some k` when the field has a zero `k` places from its end
after `k` ones, `none` when it is all ones. -/
theorem incr_spec (σ : St) (L : List Bool) (N g : ℕ) (hN : L.length = N) (hg1 : 1 ≤ g) (hg : g ≤ N)
    (hX : σ.st sIN = RepairOrdinary.frame L) (hh : σ.sh sIN = 0) (hE : σ.val rTE = N) (hS : σ.val rS = g)
    (hd : σ.val rTD = 0) (hc : σ.val rCONT = 0) (hl : σ.val rLS = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0)
    (hcap : 4 * N + 8 ≤ cap) (k : Option ℕ)
    (hk : match k with
      | none => ∀ m < g, L[N - 1 - m]'(by omega) = true
      | some k => k < g ∧ (∀ m < k, L[N - 1 - m]'(by omega) = true) ∧ L[N - 1 - k]'(by omega) = false) :
    ∃ c, WXExec cap incr σ (incrOut σ L N g k) c ∧ c ≤ 100 * (N + 1) := by
  have hs := ist_self σ L hX hh hd hc hl
  have f1 := fwdK_spec cap (S := sIN) (K := rTE) (K2 := rTB) (by decide) (ist σ L 0 0 0 0)
    (by simp [ist, Function.update_apply, hTB]) (by simp [ist, Function.update_apply, hE]; omega)
  rw [ist_sh_in, show (ist σ L 0 0 0 0).val rTE = N by simp [ist, Function.update_apply, hE], ist_seth] at f1
  have f2 := fwdK_spec cap (S := sIN) (K := rTE) (K2 := rTB) (by decide) (ist σ L (0 + N) 0 0 0)
    (by simp [ist, Function.update_apply, hTB]) (by simp [ist, Function.update_apply, hE]; omega)
  rw [ist_sh_in, show (ist σ L (0 + N) 0 0 0).val rTE = N by simp [ist, Function.update_apply, hE], ist_seth,
    show 0 + N + N = 2 * N by omega] at f2
  have f3 := WXExec.bwd cap sIN (ist σ L (2 * N) 0 0 0)
  rw [ist_sh_in, ist_seth] at f3
  have f4 := addR_spec cap (A := rS) (B := rTD) (T := rTA) (by decide) (by decide) (by decide) (ist σ L (2 * N - 1) 0 0 0)
    (by simp [ist, Function.update_apply, hTA]) (by simp [ist, Function.update_apply, hS]; omega)
  rw [ist_td, show (ist σ L (2 * N - 1) 0 0 0).val rS = g by simp [ist, Function.update_apply, hS], ist_setv_td,
    Nat.zero_add] at f4
  have f5 := WXExec.inc cap rCONT (ist σ L (2 * N - 1) g 0 0) (by simp; omega)
  rw [ist_cont, ist_setv_cont, Nat.zero_add] at f5
  match k, hk with
  | none, hk =>
    have f6 := incLoop_all cap σ L N g hN hg1 hg hk (by omega)
    have f7 := clr_spec cap rTD (ist σ (clrL L g) (2 * N - 1 - 2 * g) 0 0 1) (by simp)
    rw [ist_setv_td] at f7
    have E := WXExec.seq f1 (WXExec.seq f2 (WXExec.seq f3 (WXExec.seq f4 (WXExec.seq f5 (WXExec.seq f6 f7)))))
    rw [hs] at E
    refine ⟨_, E, ?_⟩
    simp; omega
  | some k, ⟨hk1, hk2, hk3⟩ =>
    have f6 := incLoop_zero cap σ L N g k hN hk1 hg hk2 hk3 (by omega)
    have f7 := clr_spec cap rTD (ist σ ((clrL L k).set (N - 1 - k) true) (2 * N - 1 - 2 * k) (g - k) 0 0) (by simp; omega)
    rw [ist_setv_td, ist_td] at f7
    have E := WXExec.seq f1 (WXExec.seq f2 (WXExec.seq f3 (WXExec.seq f4 (WXExec.seq f5 (WXExec.seq f6 f7)))))
    rw [hs] at E
    refine ⟨_, E, ?_⟩
    omega

/-! ## The records of `i` and `i+1` -/

theorem record_prefix (M : OrdinaryWeakMachine) (N i i' : ℕ) (j : Fin N) (hj : j.val < N - N / 16) :
    record M N i j = record M N i' j := by
  unfold record
  split_ifs <;> first | rfl | omega

theorem record_bit (M : OrdinaryWeakMachine) (N i m : ℕ) (hm : m < N / 16) (hN : 1 ≤ N)
    (hv : machineIndex M + 2 + N / 16 ≤ N) :
    (List.ofFn (record M N i))[N - 1 - m]'(by simp; omega) = i.testBit m := by
  simp only [List.getElem_ofFn, record, unrank]
  have hp : ¬ (N - 1 - m) + 1 < N - N / 16 := by omega
  have hq : ¬ (N - 1 - m) + 1 = N - N / 16 := by omega
  split_ifs with h1 h2 <;> first | omega | (congr 1; omega)

/-- **The next record** (proof of `cor:framed-refuter`): the carry chain of `i+1` on the field of `x_i` gives `x_{i+1}`. -/
theorem record_incr (M : OrdinaryWeakMachine) (N i k : ℕ) (hk : k < N / 16) (hv : machineIndex M + 2 + N / 16 ≤ N)
    (hones : ∀ m < k, i.testBit m = true) (hz : i.testBit k = false) :
    (clrL (List.ofFn (record M N i)) k).set (N - 1 - k) true = List.ofFn (record M N (i + 1)) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_set, clrL_length, List.length_ofFn] at h1
  rw [List.getElem_set, clrL_get]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hc := testBit_succ_carry k i hones hz
  by_cases hj : j < N - N / 16
  · rw [if_neg (by omega), if_neg (by omega)]
    exact record_prefix M N i (i + 1) ⟨j, h1⟩ hj
  · obtain ⟨m, hm, rfl⟩ : ∃ m, m < N / 16 ∧ j = N - 1 - m := ⟨N - 1 - j, by omega, by omega⟩
    have r1 := record_bit M (N) (i + 1) m hm (by omega) hv
    have r0 := record_bit M (N) i m hm (by omega) hv
    simp only [List.getElem_ofFn] at r1 r0
    rw [r1, hc m]
    by_cases a1 : m < k
    · rw [if_neg (by omega), if_pos (by omega), if_pos a1]
    · by_cases a2 : m = k
      · subst a2; rw [if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]
      · rw [if_neg (by omega), if_neg (by omega), if_neg a1, if_neg a2, r0]

end NearCubicGates.Adapters.Refuter.Mach
