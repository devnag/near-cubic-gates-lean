import Proof.Gates.CellsSys.SplitSpec
import Proof.Gates.CellsSys.Sem
import Proof.Gates.Cells.InputLen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN)

section B
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

theorem mem_cellN_of_params {x : ℕ} (hx : x ∈ paramsN p) : x ∈ cellN c p wt := by
  unfold CounterMachine.cellN; simp [hx]

theorem lt_of_bits {Big x : ℕ} (hb : ∀ v ∈ cellN c p wt, natBitLength v ≤ Big) (hx : x ∈ cellN c p wt) :
    x < 2 ^ Big :=
  lt_of_lt_of_le (lt_natBitLength x) (Nat.pow_le_pow_right (by norm_num) (hb x hx))

section Bits
variable {c p wt} {Big : ℕ} (hb : ∀ v ∈ cellN c p wt, natBitLength v ≤ Big)
include hb

theorem M1_lt : p.M1 < 2 ^ Big := lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN]))
theorem A_lt : p.A < 2 ^ Big := lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN]))
theorem Lam_lt : p.Lambda < 2 ^ Big := lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN]))
theorem hE_lt : p.hE < 2 ^ Big := lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN]))
theorem J_lt : p.J < 2 ^ Big := lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN]))
theorem factor_lt (f : ℕ) (hf : f ∈ p.factors) : f < 2 ^ Big :=
  lt_of_bits c p wt hb (mem_cellN_of_params c p wt (by simp [paramsN, hf]))

theorem factor_getD_lt (t : ℕ) : p.factors.getD t 0 < 2 ^ Big := by
  rcases Nat.lt_or_ge t p.factors.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact factor_lt hb _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; positivity

theorem tailProd_toNat_le (j : ℕ) : (tailProd p j).toNat ≤ 2 ^ (Big * p.J) := by
  have e : tailProd p j = ((∏ t ∈ Finset.Ico j (p.J - 1), p.factors.getD t 0 : ℕ) : ℤ) := by
    unfold tailProd rateOf; push_cast; rfl
  rw [e, Int.toNat_natCast]
  calc ∏ t ∈ Finset.Ico j (p.J - 1), p.factors.getD t 0 ≤ (2 ^ Big) ^ (Finset.Ico j (p.J - 1)).card :=
        Finset.prod_le_pow_card _ _ _ (fun t _ => (factor_getD_lt hb t).le)
    _ ≤ (2 ^ Big) ^ p.J := Nat.pow_le_pow_right (by positivity) (by simp; omega)
    _ = 2 ^ (Big * p.J) := by rw [← pow_mul]

theorem factors_sum_le (hJ : p.factors.length = p.J - 1) : p.factors.sum ≤ p.J * 2 ^ Big := by
  have := List.sum_le_card_nsmul p.factors (2 ^ Big) (fun f hf => (factor_lt hb f hf).le)
  rw [smul_eq_mul, hJ] at this
  exact this.trans (Nat.mul_le_mul_right _ (by omega))

end Bits

/-! ## Forms and digits -/

theorem stageForm_abs (w : List Bool) (h : decodeWitness c p w = some wt) (s r : ℕ) (hs : s < p.J)
    (hr : r < roleCount c.kind) (z : BitInput c.n) : |stageForm c wt r s z| ≤ (c.W : ℤ) := by
  obtain ⟨vs, hvs, hbd⟩ := coef_shape c p wt w h s r hs hr
  have hsum : ((wt.coef s r).map Int.natAbs).sum ≤ c.W := by
    rw [hvs]
    exact (sum_natAbs_coef _ vs hbd).trans (by have := topWeight_le_W c r; unfold NCircuit.topWeight at this; omega)
  have h1 := linForm_abs_le (circ c r).gates (wt.coef s r) z
  have hW : (((wt.coef s r).map Int.natAbs).sum : ℤ) ≤ c.W := by exact_mod_cast hsum
  unfold stageForm; linarith

theorem scoreForm_abs (r : ℕ) (z : BitInput c.n) : |scoreForm c r z| ≤ (c.W : ℤ) := by
  have h1 := score_abs_le (circ c r) z
  have hW : ((circ c r).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r
  unfold scoreForm; linarith

theorem digit_abs (w : List Bool) (h : decodeWitness c p w = some wt) (r j : ℕ) (hj : j < p.J)
    (hr : r < roleCount c.kind) (z : BitInput c.n) :
    |digit c p wt r j z| ≤ ((1 + p.factors.sum) * c.W : ℕ) := by
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  unfold digit
  cases j with
  | zero =>
    simp only [CountingCore.proposedDigit]
    have := stageForm_abs c p wt w h 0 r (by omega) hr z
    nlinarith [Nat.zero_le p.factors.sum, Nat.zero_le c.W]
  | succ j =>
    simp only [CountingCore.proposedDigit]
    have h1 := stageForm_abs c p wt w h (j + 1) r hj hr z
    have h2 := stageForm_abs c p wt w h j r (by omega) hr z
    have ha := rateOf_le p j
    have ha0 := rateOf_nonneg p j
    calc _ ≤ |stageForm c wt r (j + 1) z| + |rateOf p j * stageForm c wt r j z| := abs_sub _ _
      _ = |stageForm c wt r (j + 1) z| + rateOf p j * |stageForm c wt r j z| := by
          rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ c.W + p.factors.sum * c.W := by
          have := mul_le_mul ha h2 (abs_nonneg _) (by positivity)
          linarith
      _ = _ := by ring

/-! ## The value bound -/

/-- The exponent of the value bound. -/
def E1 (Big : ℕ) : ℕ := Big * p.J + Big + p.J + 4 * c.n + 8

theorem n4_le (n : ℕ) : 2 * n ^ 4 ≤ 2 ^ (4 * n + 1) := by
  have h : n ^ 4 ≤ 2 ^ (4 * n) := by
    calc n ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 4
      _ = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm]
  calc 2 * n ^ 4 ≤ 2 * 2 ^ (4 * n) := by omega
    _ = 2 ^ (4 * n + 1) := by ring

theorem J1_le (J : ℕ) : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self

section Glob
variable {S : SolveMachine} {C : Ctx} {Big : ℕ} (G : Glob S C c p wt y Big)
include G

theorem W_le : c.W ≤ 2 * c.n ^ 4 := by
  obtain ⟨B1, B2, hadm⟩ := G.adm
  exact hadm.2.2.2.2.2.2.1

theorem W_le_pow : c.W ≤ 2 ^ (4 * c.n + 1) := (W_le c p wt y G).trans (n4_le c.n)

theorem hE_ge : 1 ≤ p.hE := by obtain ⟨cT, hs⟩ := G.spec; exact hE_pos c p hs

theorem A_pos' : 0 < p.A := by obtain ⟨cT, hs⟩ := G.spec; exact A_pos hs

theorem M1_ge : 1 ≤ p.M1 := by
  obtain ⟨cT, hs⟩ := G.spec; obtain ⟨B1, B2, hadm⟩ := G.adm; exact M1_pos c p hadm hs

theorem J_ge : 1 ≤ p.J := by obtain ⟨cT, hs⟩ := G.spec; exact hs.J_pos

theorem J_le_n : p.J ≤ c.n + 1 := by
  obtain ⟨cT, hs⟩ := G.spec; obtain ⟨B1, B2, hadm⟩ := G.adm
  exact (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)

theorem hE_le_n : p.hE ≤ c.n := by
  obtain ⟨cT, hs⟩ := G.spec
  rw [hs.hE_eq]; have := P_le_n c p hs; omega

theorem ctr_abs (rj : Role c × Fin p.J) : |ctr c p wt y rj| ≤ (2 ^ (p.J + Big + 4 * c.n + 1) : ℕ) := by
  obtain ⟨w, hw⟩ := G.dec
  obtain ⟨cT, hs⟩ := G.spec
  have h1 := digit_abs c p wt w hw rj.1.val rj.2.val rj.2.isLt rj.1.isLt (extend wt.I y (zeroPoint wt.I))
  have hf := factors_sum_le G.bits (factors_length hs)
  have hW := W_le_pow c p wt y G
  have hJ := J1_le p.J
  have key : (1 + p.factors.sum) * c.W ≤ 2 ^ (p.J + Big + 4 * c.n + 1) := by
    have hp : 1 ≤ 2 ^ Big := Nat.one_le_two_pow
    calc (1 + p.factors.sum) * c.W ≤ (2 ^ p.J * 2 ^ Big) * 2 ^ (4 * c.n + 1) := by
          apply Nat.mul_le_mul _ hW
          nlinarith
      _ = _ := by rw [← pow_add, ← pow_add, ← Nat.add_assoc]
  unfold ctr
  calc _ ≤ (((1 + p.factors.sum) * c.W : ℕ) : ℤ) := h1
    _ ≤ _ := by exact_mod_cast key

theorem ctrL_le : ∀ x ∈ ctrL c p wt y, x ≤ 2 ^ E1 c p Big := by
  intro x hx
  simp only [ctrL, pairOf, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨r, j, hx⟩ := hx
  have h := ctr_abs c p wt y G (r, j)
  have hle : 2 ^ (p.J + Big + 4 * c.n + 1) ≤ 2 ^ E1 c p Big := Nat.pow_le_pow_right (by norm_num) (by unfold E1; omega)
  rcases hx with rfl | rfl
  · have : ((ctr c p wt y (r, j)).toNat : ℤ) ≤ (2 ^ (p.J + Big + 4 * c.n + 1) : ℕ) := by
      have := abs_le.mp h; omega
    have : (ctr c p wt y (r, j)).toNat ≤ 2 ^ (p.J + Big + 4 * c.n + 1) := by exact_mod_cast this
    omega
  · have : ((-ctr c p wt y (r, j)).toNat : ℤ) ≤ (2 ^ (p.J + Big + 4 * c.n + 1) : ℕ) := by
      have := abs_le.mp h; omega
    have : (-ctr c p wt y (r, j)).toNat ≤ 2 ^ (p.J + Big + 4 * c.n + 1) := by exact_mod_cast this
    omega

theorem tailL_le : ∀ x ∈ tailL p, x ≤ 2 ^ E1 c p Big := by
  intro x hx
  simp only [tailL, List.mem_map, List.mem_range] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact (tailProd_toNat_le G.bits j).trans (Nat.pow_le_pow_right (by norm_num) (by unfold E1; omega))

theorem kxL_le : ∀ x ∈ kxL c p wt y, x ≤ 2 ^ (4 * c.n + 1) := by
  intro x hx
  obtain ⟨w, hw⟩ := G.dec
  have hW := W_le_pow c p wt y G
  simp only [kxL, pairOf, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨r, hx⟩ := hx
  have h1 := stageForm_abs c p wt w hw (p.J - 1) r.val (by have := J_ge c p wt y G; omega) r.isLt
    (extend wt.I y (zeroPoint wt.I))
  have h2 := scoreForm_abs c r.val (extend wt.I y (zeroPoint wt.I))
  have hW' : (c.W : ℤ) ≤ (2 ^ (4 * c.n + 1) : ℕ) := by exact_mod_cast hW
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  rcases hx with (rfl | rfl) | (rfl | rfl)
  · have : ((stageForm c wt r.val (p.J - 1) (extend wt.I y (zeroPoint wt.I))).toNat : ℤ) ≤
        (2 ^ (4 * c.n + 1) : ℕ) := by omega
    exact_mod_cast this
  · have : ((-stageForm c wt r.val (p.J - 1) (extend wt.I y (zeroPoint wt.I))).toNat : ℤ) ≤
        (2 ^ (4 * c.n + 1) : ℕ) := by omega
    exact_mod_cast this
  · have : ((scoreForm c r.val (extend wt.I y (zeroPoint wt.I))).toNat : ℤ) ≤ (2 ^ (4 * c.n + 1) : ℕ) := by omega
    exact_mod_cast this
  · have : ((-scoreForm c r.val (extend wt.I y (zeroPoint wt.I))).toNat : ℤ) ≤ (2 ^ (4 * c.n + 1) : ℕ) := by omega
    exact_mod_cast this

/-- The exponent `E₁` against the width. -/
theorem wd_E1 : 2 * E1 c p Big + p.J + Big + 10 ≤ C.Wd := by
  have h := G.wd
  unfold E1
  nlinarith

theorem wWin_lt : wWin p < 2 ^ (Big + 1) := by
  have := hE_lt G.bits; unfold wWin; rw [pow_succ]; omega

/-- The digit radix power fits the width. -/
theorem pw_fit (nD : ℕ) (hnD : nD ≤ 2 * p.J) : wWin p ^ nD * (wWin p + 1) < 2 ^ C.Wd := by
  have hw := wWin_lt c p wt y G
  have h1 : wWin p ^ nD ≤ (2 ^ (Big + 1)) ^ nD := Nat.pow_le_pow_left hw.le nD
  have h2 : wWin p ^ nD * (wWin p + 1) ≤ (2 ^ (Big + 1)) ^ nD * 2 ^ (Big + 1) := Nat.mul_le_mul h1 hw
  rw [← pow_mul, ← pow_add] at h2
  refine lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) ?_)
  have h := G.wd
  nlinarith

end Glob

end B

end NearCubicGates.Close.Cells.SystemsPhase
