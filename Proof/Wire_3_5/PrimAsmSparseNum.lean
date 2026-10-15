import Proof.Wire_3_5.PrimAsmUnaryPow
import Proof.Wire_3_5.PrimAsmStarNums
import Proof.Wire_3_5.LedgerSparse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow

/-! ## The schedule over the integers -/

section Ref
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- `ζ = a/b`. -/
def zA (ζ : ℚ) : ℕ := ζ.num.toNat
def zB (ζ : ℚ) : ℕ := ζ.den
/-- `c₁ = b − a` (so `1 − ζ = c₁/b`) and `c₂ = b − 2a` (so `1/2 − ζ = c₂/(2b)`). -/
def c1 (ζ : ℚ) : ℕ := zB ζ - zA ζ
def c2 (ζ : ℚ) : ℕ := zB ζ - 2 * zA ζ

include h0 in
theorem zA_cast : ((zA ζ : ℕ) : ℚ) = (ζ.num : ℚ) := by
  have : 0 < ζ.num := Rat.num_pos.mpr h0
  unfold zA; rw [← Int.cast_natCast, Int.toNat_of_nonneg this.le]

include h0 in
theorem zeta_eq : ζ = (zA ζ : ℚ) / (zB ζ : ℚ) := by
  rw [zA_cast h0]; unfold zB; exact (Rat.num_div_den ζ).symm

theorem zB_pos : 0 < zB ζ := ζ.den_pos

include h0 h1 in
theorem two_zA_lt : 2 * zA ζ < zB ζ := by
  have hb : (0 : ℚ) < zB ζ := by exact_mod_cast zB_pos
  have h := zeta_eq h0
  have : (zA ζ : ℚ) / zB ζ < 1 / 2 := h ▸ h1
  rw [div_lt_iff₀ hb] at this
  have : (2 * zA ζ : ℚ) < zB ζ := by linarith
  exact_mod_cast this

include h0 h1 in
theorem c1_pos : 0 < c1 ζ := by have := two_zA_lt h0 h1; unfold c1; omega

include h0 h1 in
theorem c2_pos : 0 < c2 ζ := by have := two_zA_lt h0 h1; unfold c2; omega

include h0 h1 in
theorem one_sub_eq : 1 - ζ = (c1 ζ : ℚ) / zB ζ := by
  have hb : (0 : ℚ) < zB ζ := by exact_mod_cast zB_pos
  have hle : zA ζ ≤ zB ζ := by have := two_zA_lt h0 h1; omega
  unfold c1; rw [Nat.cast_sub hle]; conv_lhs => rw [zeta_eq h0]
  field_simp

include h0 h1 in
theorem half_sub_eq : 1 / 2 - ζ = (c2 ζ : ℚ) / (2 * zB ζ) := by
  have hb : (0 : ℚ) < zB ζ := by exact_mod_cast zB_pos
  have hle : 2 * zA ζ ≤ zB ζ := (two_zA_lt h0 h1).le
  unfold c2; rw [Nat.cast_sub hle]; conv_lhs => rw [zeta_eq h0]
  push_cast; field_simp

include h0 h1 in
theorem eps_eq (t : ℕ) : Schedule.eps ζ t =
    ((c1 ζ ^ (t - 1) * c2 ζ : ℕ) : ℚ) / ((zB ζ ^ (t - 1) * (2 * zB ζ) : ℕ) : ℚ) := by
  unfold Schedule.eps
  rw [one_sub_eq h0 h1, half_sub_eq h0 h1, div_pow]
  push_cast
  rw [div_mul_div_comm]

include h0 h1 in
/-- **The schedule's condition over the integers.** -/
theorem good_iff (L t : ℕ) (ht : 1 ≤ t) : Schedule.Good ζ L t ↔
    c1 ζ ^ (16 * (t - 1)) * c2 ζ ^ 16 * L ^ 3 ≤ zB ζ ^ (16 * (t - 1)) * (2 * zB ζ) ^ 16 := by
  have hb : 0 < zB ζ := zB_pos
  have hden : (0 : ℚ) < ((zB ζ ^ (t - 1) * (2 * zB ζ) : ℕ) : ℚ) := by
    have : 0 < zB ζ ^ (t - 1) * (2 * zB ζ) := by positivity
    exact_mod_cast this
  have key : Schedule.eps ζ t ^ 16 * (L : ℚ) ^ 3 ≤ 1 ↔
      (c1 ζ ^ (t - 1) * c2 ζ) ^ 16 * L ^ 3 ≤ (zB ζ ^ (t - 1) * (2 * zB ζ)) ^ 16 := by
    rw [eps_eq h0 h1, div_pow, div_mul_eq_mul_div, div_le_one (pow_pos hden 16)]
    constructor <;> intro h <;> exact_mod_cast h
  have e1 : (c1 ζ ^ (t - 1) * c2 ζ) ^ 16 * L ^ 3 = c1 ζ ^ (16 * (t - 1)) * c2 ζ ^ 16 * L ^ 3 := by ring
  have e2 : (zB ζ ^ (t - 1) * (2 * zB ζ)) ^ 16 = zB ζ ^ (16 * (t - 1)) * (2 * zB ζ) ^ 16 := by ring
  unfold Schedule.Good
  rw [key, e1, e2]
  exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

/-- `⌈p/q⌉₊ = ⌈p/q⌉` of naturals. -/
theorem natCeil_div (p q : ℕ) (hq : 0 < q) : ⌈((p : ℚ) / q)⌉₊ = (p + q - 1) / q := by
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hlo := Nat.lt_div_mul_add (a := p + q - 1) hq
  have hhi := Nat.div_mul_le_self (p + q - 1) q
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hqq]
    have : p ≤ (p + q - 1) / q * q := by omega
    exact_mod_cast this
  · by_contra hlt
    have hlt' := not_le.mp hlt
    have h1 : ⌈((p : ℚ) / q)⌉₊ ≤ (p + q - 1) / q - 1 := by omega
    rw [Nat.ceil_le, div_le_iff₀ hqq] at h1
    have h3 : p ≤ ((p + q - 1) / q - 1) * q := by exact_mod_cast h1
    have e : ((p + q - 1) / q - 1) * q = (p + q - 1) / q * q - q := by rw [Nat.sub_mul, Nat.one_mul]
    have hcq : 1 * q ≤ (p + q - 1) / q * q := Nat.mul_le_mul_right q (by omega)
    omega

include h0 h1 in
/-- **`Λ̄_t = ⌈2/e_t⌉ = ⌈4b^t/(c₁^{t−1}c₂)⌉`** for `t ≥ 1`. -/
theorem lambda_eq (t : ℕ) (ht : 1 ≤ t) :
    ⌈((2 : ℕ) : ℚ) / Schedule.eps ζ t⌉₊ =
      (4 * zB ζ ^ t + c1 ζ ^ (t - 1) * c2 ζ - 1) / (c1 ζ ^ (t - 1) * c2 ζ) := by
  have hc : 0 < c1 ζ ^ (t - 1) * c2 ζ := Nat.mul_pos (pow_pos (c1_pos h0 h1) _) (c2_pos h0 h1)
  rw [← natCeil_div _ _ hc]
  congr 1
  rw [eps_eq h0 h1, div_div_eq_mul_div]
  congr 1
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  push_cast
  ring

end Ref

/-! ## The register program -/

section Machine
variable {ns nr : ℕ} (cap : ℕ)

/-- `R 0 := R 0 · R 1` (through `R 2`); `R = (x, m, t, u, w)`, scratch at `0`. -/
def mulByW (R : Fin 5 ↪ Fin nr) : WM ns nr := .seq (mulAddW R) (.seq (WM.clear (R 0)) (WM.move (R 2) (R 0)))

theorem mulByW_spec (R : Fin 5 ↪ Fin nr) (σ : WState ns nr) (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0)
    (h4 : σ.val (R 4) = 0) (hc : σ.val (R 0) * σ.val (R 1) ≤ cap) (ha : σ.val (R 0) ≤ cap) (hb : σ.val (R 1) ≤ cap) :
    WExec cap (mulByW R) σ (σ.setv (R 0) (σ.val (R 0) * σ.val (R 1))) (3 * UnaryPow.sq cap) := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h1 := mulAddW_sq cap R σ h3 h4 hb (by rw [h2]; omega) ha
  rw [h2, Nat.zero_add] at h1
  have g0 : (σ.setv (R 2) (σ.val (R 0) * σ.val (R 1))).val (R 0) = σ.val (R 0) := by
    simp [Function.update_apply, hne (show (0 : Fin 5) ≠ 2 by decide)]
  have h2' := wclear_spec cap (R 0) (σ.val (R 0)) _ g0 (by rw [g0]; exact ha)
  have h3' := wmove_spec cap (R 2) (R 0) (hne (by decide)) (σ.val (R 0) * σ.val (R 1))
    ((σ.setv (R 2) (σ.val (R 0) * σ.val (R 1))).setv (R 0) 0)
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 0 by decide)])
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 0 by decide)]; omega)
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 0 by decide)]; omega)
  have hs := lin_le_sq cap
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2' h3')) ?_ (by nlinarith)
  wgen_eq [h2]

/-! ### Specs with the values named (so the chained states carry no register reads) -/

theorem incN0 (r : Fin nr) (c : ℕ) (σ : WState ns nr) (hr : σ.val r = 0) (hc : c ≤ cap) :
    WExec cap (StarNums.incN r c) σ (σ.setv r c) (UnaryPow.sq cap) := by
  have h := StarNums.incN_spec cap r c σ (by omega)
  rw [hr, Nat.zero_add] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem inc1 (r : Fin nr) (v : ℕ) (σ : WState ns nr) (hr : σ.val r = v) (hv : v < cap) :
    WExec cap (.inc r) σ (σ.setv r (v + 1)) (UnaryPow.sq cap) := by
  have h := WExec.inc (cap := cap) r σ (by omega)
  rw [hr] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem dec1 (r : Fin nr) (v : ℕ) (σ : WState ns nr) (hr : σ.val r = v) (hv : v ≤ cap) :
    WExec cap (.dec r) σ (σ.setv r (v - 1)) (UnaryPow.sq cap) := by
  have h := WExec.dec (cap := cap) r σ (by omega)
  rw [hr] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem clear1 (r : Fin nr) (v : ℕ) (σ : WState ns nr) (hr : σ.val r = v) (hv : v ≤ cap) :
    WExec cap (WM.clear r) σ (σ.setv r 0) (UnaryPow.sq cap) := by
  have h := wclear_spec cap r v σ hr (by omega)
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem mulBy1 (R : Fin 5 ↪ Fin nr) (x m : ℕ) (σ : WState ns nr) (hx : σ.val (R 0) = x) (hm : σ.val (R 1) = m)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (hc : x * m ≤ cap) (ha : x ≤ cap)
    (hb : m ≤ cap) : WExec cap (mulByW R) σ (σ.setv (R 0) (x * m)) (3 * UnaryPow.sq cap) := by
  have h := mulByW_spec cap R σ h2 h3 h4 (by rw [hx, hm]; exact hc) (by rw [hx]; exact ha) (by rw [hm]; exact hb)
  rw [hx, hm] at h
  exact h

theorem mulAdd1 (R : Fin 5 ↪ Fin nr) (x m c : ℕ) (σ : WState ns nr) (hx : σ.val (R 0) = x) (hm : σ.val (R 1) = m)
    (hc0 : σ.val (R 2) = c) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (hc : c + x * m ≤ cap) (ha : x ≤ cap)
    (hb : m ≤ cap) : WExec cap (mulAddW R) σ (σ.setv (R 2) (c + x * m)) (UnaryPow.sq cap) := by
  have h := UnaryPow.mulAddW_sq cap R σ h3 h4 (by rw [hm]; exact hb) (by rw [hc0, hx, hm]; exact hc)
    (by rw [hx]; exact ha)
  rw [hx, hm, hc0] at h
  exact h

theorem pow1 (R : Fin 5 ↪ Fin nr) (b e : ℕ) (σ : WState ns nr) (hb0 : σ.val (R 0) = b) (h1 : σ.val (R 1) = 0)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (hc1 : 1 ≤ cap) (hb : b ≤ cap)
    (hbe : b ^ e ≤ cap) : WExec cap (UnaryPow.powConstW R e) σ (σ.setv (R 1) (b ^ e)) ((e + 1) * (4 * UnaryPow.sq cap)) := by
  have h := UnaryPow.powConstW_spec cap R e σ h1 h2 h3 h4 hc1 (by rw [hb0]; exact hb)
    (by rw [hb0]; exact UnaryPow.pow_le_of hc1 hbe)
  rw [hb0] at h
  exact h

theorem gt1 (R : Fin 6 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha0 : σ.val (R 0) = a) (hb0 : σ.val (R 1) = b)
    (hf : σ.val (R 2) = 0) (ht : σ.val (R 3) = 0) (hu : σ.val (R 4) = 0) (hw : σ.val (R 5) = 0) (ha : a ≤ cap)
    (hb : b ≤ cap) (hc1 : 1 ≤ cap) :
    WExec cap (gtFlagW R) σ (σ.setv (R 2) (if b < a then 1 else 0)) (UnaryPow.sq cap) := by
  have h := gtFlagW_spec cap R σ hf ht hu hw (by rw [ha0]; exact ha) (by rw [hb0]; exact hb) hc1
  rw [ha0, hb0] at h
  have hs : 100 * cap + 100 ≤ UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
  exact WExec.mono h (by omega)

theorem copy1 (a b t : Fin nr) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (v : ℕ) (σ : WState ns nr)
    (ha0 : σ.val a = v) (hb : σ.val b = 0) (ht : σ.val t = 0) (hv : v ≤ cap) :
    WExec cap (FinalPass.Hash4.wcopyR a b t) σ (σ.setv b v) (UnaryPow.sq cap) := by
  have h := FinalPass.Hash4.wcopyR_spec cap a b t hab hat hbt σ hb ht (by rw [ha0]; exact hv)
  rw [ha0] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem ceilDiv1 (R : Fin 12 ↪ Fin nr) (a d : ℕ) (σ : WState ns nr) (ha0 : σ.val (R 0) = a) (hd0 : σ.val (R 1) = d)
    (hz : ∀ i : Fin 12, 2 ≤ i.val → σ.val (R i) = 0) (hd : 1 ≤ d) (hcap : a + d ≤ cap) :
    WExec cap (UnaryPow.ceilDivW R) σ (σ.setv (R 2) ((a + d - 1) / d)) (5 * UnaryPow.sq cap) := by
  have h := UnaryPow.ceilDivW_spec cap R σ hz (by rw [hd0]; exact hd) (by rw [ha0, hd0]; exact hcap)
  rw [ha0, hd0] at h
  exact h

/-! The block `G : Fin 24 ↪ Fin nr`: `0` L (kept), `1` t, `2` A, `3` B, `4` N, `5` D, `6` F, `7` c₁^16, `8` b^16,
`9` b, `10` c₁, `11` Λ̄ (out), `12` s (out), `13` product temp, `14 … 23` scratch. -/

def mA : Fin 5 ↪ Fin 24 := ⟨![2, 7, 13, 14, 15], by decide⟩
def mB : Fin 5 ↪ Fin 24 := ⟨![3, 8, 13, 14, 15], by decide⟩
def mN : Fin 5 ↪ Fin 24 := ⟨![4, 9, 13, 14, 15], by decide⟩
def mD : Fin 5 ↪ Fin 24 := ⟨![5, 10, 13, 14, 15], by decide⟩
def fAB : Fin 6 ↪ Fin 24 := ⟨![2, 3, 6, 14, 15, 16], by decide⟩
def pL : Fin 5 ↪ Fin 24 := ⟨![0, 2, 14, 15, 16], by decide⟩
def mA' : Fin 5 ↪ Fin 24 := ⟨![2, 17, 13, 14, 15], by decide⟩
def mN' : Fin 5 ↪ Fin 24 := ⟨![4, 17, 13, 14, 15], by decide⟩
def mD' : Fin 5 ↪ Fin 24 := ⟨![5, 17, 13, 14, 15], by decide⟩
def cdv : Fin 12 ↪ Fin 24 := ⟨![4, 5, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩
def sqL : Fin 5 ↪ Fin 24 := ⟨![11, 17, 12, 14, 15], by decide⟩
def mS' : Fin 5 ↪ Fin 24 := ⟨![12, 17, 13, 14, 15], by decide⟩

@[simp] theorem mA_apply (i : Fin 5) : mA i = ![2, 7, 13, 14, 15] i := rfl
@[simp] theorem mB_apply (i : Fin 5) : mB i = ![3, 8, 13, 14, 15] i := rfl
@[simp] theorem mN_apply (i : Fin 5) : mN i = ![4, 9, 13, 14, 15] i := rfl
@[simp] theorem mD_apply (i : Fin 5) : mD i = ![5, 10, 13, 14, 15] i := rfl
@[simp] theorem fAB_apply (i : Fin 6) : fAB i = ![2, 3, 6, 14, 15, 16] i := rfl
@[simp] theorem pL_apply (i : Fin 5) : pL i = ![0, 2, 14, 15, 16] i := rfl
@[simp] theorem mA'_apply (i : Fin 5) : mA' i = ![2, 17, 13, 14, 15] i := rfl
@[simp] theorem mN'_apply (i : Fin 5) : mN' i = ![4, 17, 13, 14, 15] i := rfl
@[simp] theorem mD'_apply (i : Fin 5) : mD' i = ![5, 17, 13, 14, 15] i := rfl
@[simp] theorem cdv_apply (i : Fin 12) : cdv i = ![4, 5, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21] i := rfl
@[simp] theorem sqL_apply (i : Fin 5) : sqL i = ![11, 17, 12, 14, 15] i := rfl
@[simp] theorem mS'_apply (i : Fin 5) : mS' i = ![12, 17, 13, 14, 15] i := rfl

/-! ### Block states: the registers of `G` as one function (for cheap state equalities) -/

open Classical in
/-- `σ` with the registers of the block `G` replaced by the values `v`. -/
noncomputable def blk {K : ℕ} (G : Fin K ↪ Fin nr) (σ : WState ns nr) (v : Fin K → ℕ) : WState ns nr :=
  ⟨σ.sh, σ.st, fun r => if h : ∃ i, G i = r then v h.choose else σ.val r, σ.cell⟩

theorem blk_val {K : ℕ} (G : Fin K ↪ Fin nr) (σ : WState ns nr) (v : Fin K → ℕ) (i : Fin K) :
    (blk G σ v).val (G i) = v i := by
  have h : ∃ j, G j = G i := ⟨i, rfl⟩
  show (if h : ∃ j, G j = G i then v h.choose else σ.val (G i)) = v i
  rw [dif_pos h]
  exact congrArg v (G.injective h.choose_spec)

theorem setv_blk {K : ℕ} (G : Fin K ↪ Fin nr) (σ : WState ns nr) (v : Fin K → ℕ) (i : Fin K) (x : ℕ) :
    (blk G σ v).setv (G i) x = blk G σ (Function.update v i x) := by
  refine WState.eq rfl rfl ?_ rfl
  funext r
  by_cases h : ∃ j, G j = r
  · obtain ⟨j, rfl⟩ := h
    rw [blk_val]
    by_cases hij : j = i
    · subst hij; simp
    · rw [WState.setv_val, Function.update_of_ne (G.injective.ne hij), blk_val, Function.update_of_ne hij]
  · have hne : ∀ k, r ≠ G k := fun k hk => h ⟨k, hk.symm⟩
    rw [WState.setv_val, Function.update_of_ne (hne i)]
    show (if h : ∃ j, G j = r then v h.choose else σ.val r) =
      (if h : ∃ j, G j = r then Function.update v i x h.choose else σ.val r)
    rw [dif_neg h, dif_neg h]

theorem blk_base {K : ℕ} (G : Fin K ↪ Fin nr) (σ : WState ns nr) : blk G σ (fun j => σ.val (G j)) = σ := by
  refine WState.eq rfl rfl ?_ rfl
  funext r
  show (if h : ∃ j, G j = r then σ.val (G h.choose) else σ.val r) = σ.val r
  split_ifs with h
  · rw [h.choose_spec]
  · rfl

theorem setv_base {K : ℕ} (G : Fin K ↪ Fin nr) (σ : WState ns nr) (i : Fin K) (x : ℕ) :
    σ.setv (G i) x = blk G σ (Function.update (fun j => σ.val (G j)) i x) := by
  conv_lhs => rw [← blk_base G σ]
  exact setv_blk G σ _ i x

/-- The search's flag at round `k`: `[B_k < A_k]`, i.e. `t = k + 1` is not yet good. -/
def sFlag (ζ : ℚ) (L k : ℕ) : ℕ :=
  if (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k < L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k then 1 else 0

/-- The search's state at round `k` (`t = k + 1`). -/
def sState (ζ : ℚ) (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (L k : ℕ) : WState ns nr :=
  (((((((((σ.setv (G 7) (c1 ζ ^ 16)).setv (G 8) (zB ζ ^ 16)).setv (G 9) (zB ζ)).setv (G 10) (c1 ζ)).setv (G 1)
    (k + 1)).setv (G 2) (L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k)).setv (G 3) ((2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k)).setv
    (G 4) (zB ζ * zB ζ ^ k)).setv (G 5) (c1 ζ ^ k)).setv (G 6) (sFlag ζ L k)

/-- **Initialization**: the constants, `t = 1`, `A = L³c₂^{16}`, `B = (2b)^{16}`, `N = b`, `D = 1`, the flag. -/
def sInit (ζ : ℚ) (G : Fin 24 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (G 7) (c1 ζ ^ 16)) (.seq (StarNums.incN (G 8) (zB ζ ^ 16)) (.seq (StarNums.incN (G 9) (zB ζ))
  (.seq (StarNums.incN (G 10) (c1 ζ)) (.seq (.inc (G 1)) (.seq (powConstW (pL.trans G) 3)
  (.seq (StarNums.incN (G 17) (c2 ζ ^ 16)) (.seq (mulByW (mA'.trans G)) (.seq (WM.clear (G 17))
  (.seq (StarNums.incN (G 3) ((2 * zB ζ) ^ 16)) (.seq (StarNums.incN (G 4) (zB ζ)) (.seq (.inc (G 5))
  (gtFlagW (fAB.trans G)))))))))))))

/-- **One round**: `t += 1`, `A ·= c₁^{16}`, `B ·= b^{16}`, `N ·= b`, `D ·= c₁`, the flag again. -/
def sBody (G : Fin 24 ↪ Fin nr) : WM ns nr :=
  .seq (.dec (G 6)) (.seq (.inc (G 1)) (.seq (mulByW (mA.trans G)) (.seq (mulByW (mB.trans G))
  (.seq (mulByW (mN.trans G)) (.seq (mulByW (mD.trans G)) (gtFlagW (fAB.trans G)))))))

def sFinish (ζ : ℚ) (Cδ : ℕ) (G : Fin 24 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (G 17) 4) (.seq (mulByW (mN'.trans G)) (.seq (WM.clear (G 17))
  (.seq (StarNums.incN (G 17) (c2 ζ)) (.seq (mulByW (mD'.trans G)) (.seq (WM.clear (G 17))
  (.seq (UnaryPow.ceilDivW (cdv.trans G)) (.seq (FinalPass.Hash4.wcopyR (G 11) (G 17) (G 14))
  (.seq (mulAddW (sqL.trans G)) (.seq (WM.clear (G 17)) (.seq (StarNums.incN (G 17) Cδ)
  (.seq (mulByW (mS'.trans G)) (.seq (WM.clear (G 17))
  (.seq (WM.clear (G 1)) (.seq (WM.clear (G 2)) (.seq (WM.clear (G 3)) (.seq (WM.clear (G 4)) (.seq (WM.clear (G 5))
  (.seq (WM.clear (G 7)) (.seq (WM.clear (G 8)) (.seq (WM.clear (G 9)) (WM.clear (G 10))))))))))))))))))))))

/-- **The sparse count**: `G 11 := Λ̄(q)`, `G 12 := s(q)` from `G 0 = L(q)`. -/
def sparseM (ζ : ℚ) (Cδ : ℕ) (G : Fin 24 ↪ Fin nr) : WM ns nr :=
  .seq (sInit ζ G) (.seq (.whr (G 6) (sBody G)) (sFinish ζ Cδ G))

/-- Sequencing within a budget of `N` units: the first part within `c` units, the rest within `N − c − 1`. -/
theorem seqD {P Q : WM ns nr} {σ ρ τ : WState ns nr} (N c : ℕ) {n : ℕ} (h1 : WExec cap P σ ρ n)
    (hn : n ≤ c * UnaryPow.sq cap) (hc : c + 1 ≤ N) (h2 : WExec cap Q ρ τ ((N - c - 1) * UnaryPow.sq cap)) :
    WExec cap (.seq P Q) σ τ (N * UnaryPow.sq cap) := by
  have hs := UnaryPow.sq_ge cap
  refine WExec.mono (WExec.seq h1 h2) ?_
  have e : (N - c - 1) * UnaryPow.sq cap + c * UnaryPow.sq cap + UnaryPow.sq cap = N * UnaryPow.sq cap := by
    rw [← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  omega

/-- The last part of a chain within the remaining budget. -/
theorem endD {P : WM ns nr} {σ τ τ' : WState ns nr} (N c : ℕ) {n : ℕ} (h : WExec cap P σ τ' n) (e : τ' = τ)
    (hn : n ≤ c * UnaryPow.sq cap) (hc : c ≤ N) : WExec cap P σ τ (N * UnaryPow.sq cap) :=
  WExec.cast cap h e (le_trans hn (Nat.mul_le_mul_right _ hc))

theorem sInit_spec (ζ : ℚ) (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (L : ℕ) (hL : σ.val (G 0) = L)
    (hz : ∀ i : Fin 24, i ≠ 0 → σ.val (G i) = 0) (hc1 : 1 ≤ cap)
    (hK1 : c1 ζ ^ 16 ≤ cap) (hK2 : zB ζ ^ 16 ≤ cap) (hb : zB ζ ≤ cap) (hcc : c1 ζ ≤ cap)
    (hL3 : L ^ 3 ≤ cap) (hc2 : c2 ζ ^ 16 ≤ cap) (hA : L ^ 3 * c2 ζ ^ 16 ≤ cap) (hB : (2 * zB ζ) ^ 16 ≤ cap)
    (hL1 : L ≤ cap) :
    WExec cap (sInit ζ G) σ (sState ζ G σ L 0) (60 * UnaryPow.sq cap) := by
  unfold sInit
  refine seqD cap _ 1 (incN0 cap (G 7) _ σ (hz 7 (by decide)) hK1) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 8) _ _ (by simp [hz]) hK2) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 9) _ _ (by simp [hz]) hb) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 10) _ _ (by simp [hz]) hcc) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (inc1 cap (G 1) 0 _ (by simp [hz]) (by omega)) (by omega) (by norm_num) ?_
  refine seqD cap _ 16 (pow1 cap (pL.trans G) L 3 _ (by simp [hz, hL]) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hL1 hL3) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 17) _ _ (by simp [hz]) hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mA'.trans G) (L ^ 3) (c2 ζ ^ 16) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hA hL3 hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 17) (c2 ζ ^ 16) _ (by simp) hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 3) _ _ (by simp [hz]) hB) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 4) _ _ (by simp [hz]) hb) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (inc1 cap (G 5) 0 _ (by simp [hz]) (by omega)) (by omega) (by norm_num) ?_
  refine endD cap _ 1 (gt1 cap (fAB.trans G) (L ^ 3 * c2 ζ ^ 16) ((2 * zB ζ) ^ 16) _ (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by simp [hz]) (by simp [hz]) hA hB hc1) ?_ (by omega) (by norm_num)
  unfold sState sFlag
  simp only [Function.Embedding.trans_apply, pL_apply, mA'_apply, fAB_apply, Matrix.cons_val]
  clear hc1 hK1 hK2 hb hcc hL3 hc2 hA hB hL1 hL
  have hb0 := setv_base G σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

theorem sBody_spec (ζ : ℚ) (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (L k : ℕ)
    (hz : ∀ i : Fin 24, i ≠ 0 → σ.val (G i) = 0) (hc1 : 1 ≤ cap) (hf : sFlag ζ L k = 1)
    (hK1 : c1 ζ ^ 16 ≤ cap) (hK2 : zB ζ ^ 16 ≤ cap) (hb : zB ζ ≤ cap) (hcc : c1 ζ ≤ cap) (hT : k + 2 ≤ cap)
    (hA : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ (k + 1) ≤ cap) (hB : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ (k + 1) ≤ cap)
    (hN : zB ζ * zB ζ ^ (k + 1) ≤ cap) (hD : c1 ζ ^ (k + 1) ≤ cap)
    (hAk : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k ≤ cap) (hBk : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k ≤ cap)
    (hNk : zB ζ * zB ζ ^ k ≤ cap) (hDk : c1 ζ ^ k ≤ cap) :
    WExec cap (sBody G) (sState ζ G σ L k) (sState ζ G σ L (k + 1)) (30 * UnaryPow.sq cap) := by
  have eA : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k * c1 ζ ^ 16 = L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ (k + 1) := by ring
  have eB : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k * zB ζ ^ 16 = (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ (k + 1) := by ring
  have eN : zB ζ * zB ζ ^ k * zB ζ = zB ζ * zB ζ ^ (k + 1) := by ring
  have eD : c1 ζ ^ k * c1 ζ = c1 ζ ^ (k + 1) := by ring
  unfold sBody
  refine seqD cap _ 1 (dec1 cap (G 6) 1 _ (by simp [sState, hf]) hc1) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (inc1 cap (G 1) (k + 1) _ (by simp [sState]) (by omega)) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mA.trans G) (L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k) (c1 ζ ^ 16) _
    (by simp [sState]) (by simp [sState]) (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz])
    (by rw [eA]; exact hA) hAk hK1) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mB.trans G) ((2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k) (zB ζ ^ 16) _
    (by simp [sState]) (by simp [sState]) (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz])
    (by rw [eB]; exact hB) hBk hK2) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mN.trans G) (zB ζ * zB ζ ^ k) (zB ζ) _
    (by simp [sState]) (by simp [sState]) (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz])
    (by rw [eN]; exact hN) hNk hb) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mD.trans G) (c1 ζ ^ k) (c1 ζ) _
    (by simp [sState]) (by simp [sState]) (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz])
    (by rw [eD]; exact hD) hDk hcc) (by omega) (by norm_num) ?_
  refine endD cap _ 1 (gt1 cap (fAB.trans G) (L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k * c1 ζ ^ 16)
    ((2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k * zB ζ ^ 16) _ (by simp) (by simp) (by simp [sState, hz])
    (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz]) (by rw [eA]; exact hA)
    (by rw [eB]; exact hB) hc1) ?_ (by omega) (by norm_num)
  rw [eA, eB, eN, eD]
  unfold sState sFlag
  simp only [Function.Embedding.trans_apply, mA_apply, mB_apply, mN_apply, mD_apply, fAB_apply, Matrix.cons_val]
  clear hc1 hK1 hK2 hb hcc hT hA hB hN hD hAk hBk hNk hDk eA eB eN eD hf hz
  have hb0 := setv_base G σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply]

theorem sFinish_spec (ζ : ℚ) (Cδ : ℕ) (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (L k : ℕ)
    (hz : ∀ i : Fin 24, i ≠ 0 → σ.val (G i) = 0) (hf : sFlag ζ L k = 0) (hc2p : 1 ≤ c2 ζ)
    (hcp : 1 ≤ c1 ζ) (hK1 : c1 ζ ^ 16 ≤ cap) (hK2 : zB ζ ^ 16 ≤ cap) (hb : zB ζ ≤ cap) (hcc : c1 ζ ≤ cap)
    (hc2 : c2 ζ ≤ cap) (hCδ : Cδ ≤ cap) (h4 : 4 ≤ cap) (hT : k + 1 ≤ cap)
    (hAk : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ k ≤ cap) (hBk : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ k ≤ cap)
    (hN4 : zB ζ * zB ζ ^ k * 4 ≤ cap) (hNk : zB ζ * zB ζ ^ k ≤ cap)
    (hD : c1 ζ ^ k * c2 ζ ≤ cap) (hDk : c1 ζ ^ k ≤ cap)
    (hsum : zB ζ * zB ζ ^ k * 4 + c1 ζ ^ k * c2 ζ ≤ cap)
    (hsq : zB ζ * zB ζ ^ k * 4 * (zB ζ * zB ζ ^ k * 4) * Cδ ≤ cap)
    (hsq2 : zB ζ * zB ζ ^ k * 4 * (zB ζ * zB ζ ^ k * 4) ≤ cap) (hbp : 1 ≤ zB ζ) :
    WExec cap (sFinish ζ Cδ G) (sState ζ G σ L k)
      ((σ.setv (G 11) ((zB ζ * zB ζ ^ k * 4 + c1 ζ ^ k * c2 ζ - 1) / (c1 ζ ^ k * c2 ζ))).setv (G 12)
        ((zB ζ * zB ζ ^ k * 4 + c1 ζ ^ k * c2 ζ - 1) / (c1 ζ ^ k * c2 ζ) *
          ((zB ζ * zB ζ ^ k * 4 + c1 ζ ^ k * c2 ζ - 1) / (c1 ζ ^ k * c2 ζ)) * Cδ))
      (60 * UnaryPow.sq cap) := by
  set N4 := zB ζ * zB ζ ^ k * 4 with hN4d
  set Dc := c1 ζ ^ k * c2 ζ with hDcd
  set lam := (N4 + Dc - 1) / Dc with hlam
  have hD1 : 1 ≤ Dc := Nat.mul_pos (pow_pos hcp k) hc2p
  have hN1 : 1 ≤ N4 := by
    have : 1 ≤ zB ζ * zB ζ ^ k := Nat.mul_pos hbp (pow_pos hbp k)
    omega
  have hlamN : lam ≤ N4 := by
    rw [hlam]
    apply Nat.div_le_of_le_mul
    obtain ⟨a', ha'⟩ : ∃ a', N4 = a' + 1 := ⟨N4 - 1, by omega⟩
    obtain ⟨d', hd'⟩ : ∃ d', Dc = d' + 1 := ⟨Dc - 1, by omega⟩
    rw [ha', hd', show a' + 1 + (d' + 1) - 1 = a' + d' + 1 by omega]; nlinarith
  have hll : lam * lam ≤ N4 * N4 := Nat.mul_le_mul hlamN hlamN
  have hllC : lam * lam * Cδ ≤ cap := le_trans (Nat.mul_le_mul_right _ hll) hsq
  have hl : lam ≤ cap := by omega
  have hll' : lam * lam ≤ cap := le_trans hll hsq2
  unfold sFinish
  refine seqD cap _ 1 (incN0 cap (G 17) 4 _ (by simp [sState, hz]) h4) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mN'.trans G) (zB ζ * zB ζ ^ k) 4 _ (by simp [sState]) (by simp [hN4d, hDcd, hlam])
    (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz]) hN4 hNk h4) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 17) 4 _ (by simp [hN4d, hDcd, hlam]) h4) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 17) (c2 ζ) _ (by simp [hN4d, hDcd, hlam]) hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mD'.trans G) (c1 ζ ^ k) (c2 ζ) _ (by simp [sState]) (by simp [hN4d, hDcd, hlam])
    (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz]) hD hDk hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 17) (c2 ζ) _ (by simp [hN4d, hDcd, hlam]) hc2) (by omega) (by norm_num) ?_
  refine seqD cap _ 5 (ceilDiv1 cap (cdv.trans G) N4 Dc _ (by simp [hN4d, hDcd, hlam]) (by simp [hN4d, hDcd, hlam])
    (by intro i hi; fin_cases i <;> simp at hi <;> simp [sState, hz]) hD1 hsum) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (copy1 cap (G 11) (G 17) (G 14) (by simp [hN4d, hDcd, hlam]) (by simp [hN4d, hDcd, hlam]) (by simp [hN4d, hDcd, hlam]) lam _ (by simp [hN4d, hDcd, hlam])
    (by simp [sState, hz]) (by simp [sState, hz]) hl) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (mulAdd1 cap (sqL.trans G) lam lam 0 _ (by simp [hN4d, hDcd, hlam]) (by simp [hN4d, hDcd, hlam]) (by simp [sState, hz])
    (by simp [sState, hz]) (by simp [sState, hz]) (by omega) hl hl) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 17) lam _ (by simp [hN4d, hDcd, hlam]) hl) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (incN0 cap (G 17) Cδ _ (by simp [hN4d, hDcd, hlam]) hCδ) (by omega) (by norm_num) ?_
  refine seqD cap _ 3 (mulBy1 cap (mS'.trans G) (0 + lam * lam) Cδ _ (by simp [hN4d, hDcd, hlam]) (by simp [hN4d, hDcd, hlam])
    (by simp [sState, hz]) (by simp [sState, hz]) (by simp [sState, hz]) (by rw [Nat.zero_add]; exact hllC)
    (by omega) hCδ) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 17) Cδ _ (by simp [hN4d, hDcd, hlam]) hCδ) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 1) (k + 1) _ (by simp [sState]) hT) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 2) _ _ (by simp [sState]) hAk) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 3) _ _ (by simp [sState]) hBk) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 4) N4 _ (by simp [hN4d, hDcd, hlam]) hN4) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 5) Dc _ (by simp [hN4d, hDcd, hlam]) hD) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 7) _ _ (by simp [sState]) hK1) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 8) _ _ (by simp [sState]) hK2) (by omega) (by norm_num) ?_
  refine seqD cap _ 1 (clear1 cap (G 9) _ _ (by simp [sState]) hb) (by omega) (by norm_num) ?_
  refine endD cap _ 1 (clear1 cap (G 10) _ _ (by simp [sState]) hcc) ?_ (by omega) (by norm_num)
  unfold sState
  simp only [Function.Embedding.trans_apply, mN'_apply, mD'_apply, cdv_apply, sqL_apply, mS'_apply,
    Matrix.cons_val]
  have hb0 := setv_base G σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, hf, hlam]

end Machine

/-! ## The search terminates at the ledger's `t(q)` -/

section Top
variable {ns nr : ℕ} (cap : ℕ)
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

include h0 h1 in
theorem sFlag_zero_iff (L k : ℕ) : sFlag ζ L k = 0 ↔ Schedule.Good ζ L (k + 1) := by
  unfold sFlag
  rw [good_iff h0 h1 L (k + 1) (by omega), Nat.add_sub_cancel, ← pow_mul, ← pow_mul]
  have e1 : c1 ζ ^ (16 * k) * c2 ζ ^ 16 * L ^ 3 = L ^ 3 * c2 ζ ^ 16 * c1 ζ ^ (16 * k) := by ring
  have e2 : zB ζ ^ (16 * k) * (2 * zB ζ) ^ 16 = (2 * zB ζ) ^ 16 * zB ζ ^ (16 * k) := by ring
  rw [e1, e2]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h (not_lt.mpr h')⟩
  · exact ⟨fun _ => not_lt.mp h, fun _ => rfl⟩

theorem mono_mul_pow (a x : ℕ) (hx : 1 ≤ x) {k m : ℕ} (h : k ≤ m) : a * x ^ k ≤ a * x ^ m :=
  Nat.mul_le_mul_left a (Nat.pow_le_pow_right hx h)

/-- Every value the program holds, at the last round `m = t(q) − 1`. -/
def sparseBound (ζ : ℚ) (Cδ L m : ℕ) : ℕ :=
  L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m + (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ m +
    zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) * Cδ + zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) +
    zB ζ * zB ζ ^ m * 4 + c1 ζ ^ m * c2 ζ + c1 ζ ^ 16 + zB ζ ^ 16 + c2 ζ ^ 16 + (2 * zB ζ) ^ 16 + Cδ + L ^ 3 + L +
    zB ζ + c1 ζ + c2 ζ + c1 ζ ^ m + m + 8

include h0 h1 in
theorem sLoop_spec (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (L Cδ : ℕ) (hz : ∀ i : Fin 24, i ≠ 0 → σ.val (G i) = 0)
    (hcap : sparseBound ζ Cδ L (Schedule.sched ζ h0 h1 L - 1) ≤ cap) :
    WExec cap (.whr (G 6) (sBody G)) (sState ζ G σ L 0) (sState ζ G σ L (Schedule.sched ζ h0 h1 L - 1))
      ((Schedule.sched ζ h0 h1 L - 1) * (30 * UnaryPow.sq cap + 2) + 1) := by
  set m := Schedule.sched ζ h0 h1 L - 1 with hm
  have hpos : 1 ≤ Schedule.sched ζ h0 h1 L := (Schedule.sched_spec h0 h1 L).1
  have hc1p : 1 ≤ c1 ζ := c1_pos h0 h1
  have hbp : 1 ≤ zB ζ := zB_pos
  have hK1p : 1 ≤ c1 ζ ^ 16 := Nat.one_le_pow _ _ hc1p
  have hK2p : 1 ≤ zB ζ ^ 16 := Nat.one_le_pow _ _ hbp
  unfold sparseBound at hcap
  refine flagLoop cap (G 6) (sBody G) _ m (fun k => sState ζ G σ L k) ?_ ?_ ?_
  · intro k hk
    have hng : ¬ Schedule.Good ζ L (k + 1) := Nat.find_min (Schedule.exists_good h0 h1 L)
      (show k + 1 < Schedule.sched ζ h0 h1 L by omega)
    have := (sFlag_zero_iff h0 h1 L k).not.mpr hng
    simpa [sState] using this
  · have hg : Schedule.Good ζ L (m + 1) := by
      rw [show m + 1 = Schedule.sched ζ h0 h1 L by omega]; exact Schedule.sched_spec h0 h1 L
    simpa [sState] using (sFlag_zero_iff h0 h1 L m).mpr hg
  · intro k hk
    have hng : ¬ Schedule.Good ζ L (k + 1) := Nat.find_min (Schedule.exists_good h0 h1 L)
      (show k + 1 < Schedule.sched ζ h0 h1 L by omega)
    have hf : sFlag ζ L k = 1 := by
      have := (sFlag_zero_iff h0 h1 L k).not.mpr hng
      unfold sFlag at this ⊢; split_ifs at this ⊢ <;> omega
    have a1 := mono_mul_pow (L ^ 3 * c2 ζ ^ 16) _ hK1p (show k + 1 ≤ m by omega)
    have a0 := mono_mul_pow (L ^ 3 * c2 ζ ^ 16) _ hK1p (show k ≤ m by omega)
    have b1 := mono_mul_pow ((2 * zB ζ) ^ 16) _ hK2p (show k + 1 ≤ m by omega)
    have b0 := mono_mul_pow ((2 * zB ζ) ^ 16) _ hK2p (show k ≤ m by omega)
    have n1 := mono_mul_pow (zB ζ) _ hbp (show k + 1 ≤ m by omega)
    have n0 := mono_mul_pow (zB ζ) _ hbp (show k ≤ m by omega)
    have d1 : c1 ζ ^ (k + 1) ≤ c1 ζ ^ m := Nat.pow_le_pow_right hc1p (by omega)
    have d0 : c1 ζ ^ k ≤ c1 ζ ^ m := Nat.pow_le_pow_right hc1p (by omega)
    have nm : zB ζ * zB ζ ^ m ≤ zB ζ * zB ζ ^ m * 4 := by omega
    exact sBody_spec cap ζ G σ L k hz (by omega) hf (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

include h0 h1 in

theorem sparse_spec (Cδ : ℕ) (G : Fin 24 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hL : σ.val (G 0) = Ledger.Lq q)
    (hz : ∀ i : Fin 24, i ≠ 0 → σ.val (G i) = 0)
    (hcap : sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap) :
    WExec cap (sparseM ζ Cδ G) σ
      ((σ.setv (G 11) (Ledger.rowBLambda h0 h1 2 q)).setv (G 12) (Ledger.rowBSparse h0 h1 2 Cδ q))
      ((Ledger.rowBt h0 h1 q + 5) * (40 * UnaryPow.sq cap)) := by
  set L := Ledger.Lq q with hLd
  have ht : Ledger.rowBt h0 h1 q = Schedule.sched ζ h0 h1 L := rfl
  rw [ht] at hcap ⊢
  set t := Schedule.sched ζ h0 h1 L with htd
  have hpos : 1 ≤ t := (Schedule.sched_spec h0 h1 L).1
  set m := t - 1 with hm
  have hc1p : 1 ≤ c1 ζ := c1_pos h0 h1
  have hc2p : 1 ≤ c2 ζ := c2_pos h0 h1
  have hbp : 1 ≤ zB ζ := zB_pos
  have hK1p : 1 ≤ c1 ζ ^ 16 := Nat.one_le_pow _ _ hc1p
  have hK2p : 1 ≤ zB ζ ^ 16 := Nat.one_le_pow _ _ hbp
  have hcap' := hcap
  unfold sparseBound at hcap'
  have a0 := mono_mul_pow (L ^ 3 * c2 ζ ^ 16) _ hK1p (Nat.zero_le m)
  have b0 := mono_mul_pow ((2 * zB ζ) ^ 16) _ hK2p (Nat.zero_le m)
  simp only [pow_zero, Nat.mul_one] at a0 b0
  have hL1 : L ≤ cap := by omega
  have hI := sInit_spec cap ζ G σ L hL hz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hL1
  have hLp := sLoop_spec cap h0 h1 G σ L Cδ hz hcap
  have hfm : sFlag ζ L m = 0 := by
    have hg : Schedule.Good ζ L (m + 1) := by
      rw [show m + 1 = t by omega]; exact Schedule.sched_spec h0 h1 L
    exact (sFlag_zero_iff h0 h1 L m).mpr hg
  have hF := sFinish_spec cap ζ Cδ G σ L m hz hfm hc2p hc1p (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hbp
  have hs := UnaryPow.sq_ge cap
  refine WExec.cast cap (WExec.seq hI (WExec.seq hLp hF)) ?_ ?_
  · have e4 : zB ζ * zB ζ ^ m * 4 = 4 * zB ζ ^ t := by
      rw [show t = m + 1 by omega, pow_succ]; ring
    have hlam : Ledger.rowBLambda h0 h1 2 q =
        (zB ζ * zB ζ ^ m * 4 + c1 ζ ^ m * c2 ζ - 1) / (c1 ζ ^ m * c2 ζ) := by
      unfold Ledger.rowBLambda
      rw [ht, lambda_eq h0 h1 t hpos, e4]
    have hsp : Ledger.rowBSparse h0 h1 2 Cδ q = Ledger.rowBLambda h0 h1 2 q * Ledger.rowBLambda h0 h1 2 q * Cδ := by
      unfold Ledger.rowBSparse; ring
    rw [hsp, hlam]
  · have hmt : m ≤ t := by omega
    have := Nat.mul_le_mul_right (30 * UnaryPow.sq cap + 2) hmt
    nlinarith

end Top

end NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
