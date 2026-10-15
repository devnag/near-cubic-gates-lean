import Proof.Gates.Expand.PolyTabCls0

/-! # PolyTab cost classes: the head's atoms

The monomial count (`LCls 1`), the expansion's budget (`LCls 4`, from `E.cls` and the printing condition), the
widths (`LCls 0`), the request word and the terms word (`LCls 1`), the request's natural-number fields. -/

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine

variable (E : ExpandMachine)

theorem nbl_le_of_lt (x m : ℕ) (h : x < 2 ^ m) : natBitLength x ≤ m + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.log_lt_of_lt_pow (Nat.pos_iff_ne_zero.mp hx) h; omega

theorem sum_choose_le (V D : ℕ) : ∑ d ∈ Finset.range (D + 1), V.choose d ≤ (V + 1) ^ D := by
  rw [add_pow]
  refine Finset.sum_le_sum fun d hd => ?_
  have h1 : V.choose d ≤ V ^ d := Nat.choose_le_pow V d
  have h2 : 1 ≤ D.choose d := Nat.choose_pos (by simp at hd; omega)
  calc V.choose d ≤ V ^ d := h1
    _ ≤ V ^ d * 1 ^ (D - d) * D.choose d := by simp; exact Nat.le_mul_of_pos_right _ h2

theorem V_add_one_le_Xr (r : TabReq) : r.V + 1 ≤ Xr r := by
  unfold Xr
  have : 1 ≤ mTr r := by unfold mTr Tabulator.mT; omega
  nlinarith

theorem degree_zero {F : Formula 0} : F.degree = 0 := by
  induction F with
  | const _ => rfl
  | var v => exact v.elim0
  | add f g hf hg => simp [Formula.degree, hf, hg]
  | neg f hf => simp [Formula.degree, hf]
  | sub f g hf hg => simp [Formula.degree, hf, hg]
  | mul f g hf hg => simp [Formula.degree, hf, hg]
  | pow f e hf => simp [Formula.degree, hf]

theorem lc_P : LCls 1 (fun r => (E.expand ⟨r.V, r.F⟩).length) :=
  lc_mono lc_lam (fun r => by
    have h1 := Terms.length_le r.F.degree (E.expand ⟨r.V, r.F⟩) (E.ok ⟨r.V, r.F⟩).nodup (E.ok ⟨r.V, r.F⟩).degree
    have h2 := sum_choose_le r.V r.F.degree
    have h3 : (r.V + 1) ^ r.F.degree ≤ Xr r ^ r.F.degree := Nat.pow_le_pow_left (V_add_one_le_Xr r) _
    unfold Lam
    calc (E.expand ⟨r.V, r.F⟩).length ≤ Xr r ^ r.F.degree := h1.trans (h2.trans h3)
      _ ≤ 2 ^ r.k * Xr r ^ r.F.degree := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))

theorem lc_Xr : LCls 0 Xr := by
  have h := lc_add (lc_const 1) (lc_mul lc_V lc_mTr)
  exact lc_mono h (fun r => by unfold Xr; simp)
where lc_V : LCls 0 (fun r : TabReq => r.V) := lc_le_tabSz le_tabSz_V

theorem lc_budget : LCls 4 (fun r => E.budget ⟨r.V, r.F⟩) := by
  obtain ⟨C, e, hC⟩ := E.cls
  have hX := lc_pow lc_Xr 3
  obtain ⟨Cx, ex, hx⟩ := hX
  refine ⟨8 * C * Cx * 4 ^ e, ex + e, fun r => ?_⟩
  have hb := hC ⟨r.V, r.F⟩
  simp only at hb
  have hw : (formulaWord ⟨r.V, r.F⟩).length + r.F.size + r.F.weight + 1 ≤ 4 * tabSz r := by
    have := le_tabSz_fw r; have := le_tabSz_size r; have := le_tabSz_w r; have := tabSz_pos r; omega
  have hpow : (r.V + 2) ^ (2 * r.F.degree + 3) ≤ 8 * Lam r ^ 4 * Xr r ^ 3 := by
    rcases Nat.eq_zero_or_pos r.V with h0 | hV
    · have hD : r.F.degree = 0 := by
        have := @degree_zero
        revert h0
        cases r with
        | mk n k s G V gates layout H role F B hB hc =>
          intro h0; simp only at h0; subst h0; exact degree_zero
      have h8 : (r.V + 2) ^ (2 * r.F.degree + 3) = 8 := by rw [hD, h0]; norm_num
      rw [h8]
      have := Lam_pos r; have := Xr_pos r
      have : 1 ≤ Lam r ^ 4 * Xr r ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    · have hX2 : 2 ≤ Xr r := by have := V_add_one_le_Xr r; omega
      have h1 : r.V + 2 ≤ 2 * Xr r := by have := V_add_one_le_Xr r; omega
      have h2 : (r.V + 2) ^ (2 * r.F.degree + 3) ≤ (2 * Xr r) ^ (2 * r.F.degree + 3) := Nat.pow_le_pow_left h1 _
      have h3 : (2 * Xr r) ^ (2 * r.F.degree + 3) = 8 * (2 ^ r.F.degree) ^ 2 * (Xr r ^ r.F.degree) ^ 2 * Xr r ^ 3 := by
        ring
      have h4 : 2 ^ r.F.degree ≤ Xr r ^ r.F.degree := Nat.pow_le_pow_left hX2 _
      have h5 : Xr r ^ r.F.degree ≤ Lam r := by unfold Lam; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      have h6 : (2 ^ r.F.degree) ^ 2 * (Xr r ^ r.F.degree) ^ 2 ≤ Lam r ^ 4 := by
        calc (2 ^ r.F.degree) ^ 2 * (Xr r ^ r.F.degree) ^ 2 ≤ Lam r ^ 2 * Lam r ^ 2 := by
              gcongr
              · exact h4.trans h5
          _ = Lam r ^ 4 := by ring
      calc (r.V + 2) ^ (2 * r.F.degree + 3) ≤ 8 * (2 ^ r.F.degree) ^ 2 * (Xr r ^ r.F.degree) ^ 2 * Xr r ^ 3 := by
            rw [← h3]; exact h2
        _ = 8 * ((2 ^ r.F.degree) ^ 2 * (Xr r ^ r.F.degree) ^ 2) * Xr r ^ 3 := by ring
        _ ≤ 8 * Lam r ^ 4 * Xr r ^ 3 := by gcongr
  have hx3 := hx r
  simp only [Nat.zero_mul, pow_zero, mul_one] at hx3
  calc E.budget ⟨r.V, r.F⟩ ≤ C * (r.V + 2) ^ (2 * r.F.degree + 3) *
        ((formulaWord ⟨r.V, r.F⟩).length + r.F.size + r.F.weight + 1) ^ e := hb
    _ ≤ C * (8 * Lam r ^ 4 * (Cx * tabSz r ^ ex)) * (4 * tabSz r) ^ e := by
        gcongr
        calc (r.V + 2) ^ (2 * r.F.degree + 3) ≤ 8 * Lam r ^ 4 * Xr r ^ 3 := hpow
          _ ≤ 8 * Lam r ^ 4 * (Cx * tabSz r ^ ex) := by gcongr
    _ = 8 * C * Cx * 4 ^ e * Lam r ^ 4 * tabSz r ^ (ex + e) := by ring

end NearCubicGates.Close.Expand.PolyTab
