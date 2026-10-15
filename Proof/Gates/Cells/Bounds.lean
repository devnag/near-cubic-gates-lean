import Proof.Gates.Cells.Format

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicWires

section Bounds
variable (c : Call) (p : Params) (wt : Wit c.n)

/-- The decoded coefficients of a witness, stage `s < J`, role `r < roleCount`. -/
theorem coef_shape (w : List Bool) (h : decodeWitness c p w = some wt) (s r : ℕ) (hs : s < p.J)
    (hr : r < roleCount c.kind) :
    ∃ vs : List ℕ, wt.coef s r = ((circ c r).coeffs.zip vs).map (fun av => coefOf av.1 av.2) ∧
      ∀ av ∈ (circ c r).coeffs.zip vs, av.2 ≤ 2 * av.1.natAbs := by
  unfold decodeWitness at h
  simp only at h
  split_ifs at h with hok
  cases h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at hok
  exact ⟨_, rfl, hok.2 s hs r hr⟩

theorem coefOf_abs (a : ℤ) (v : ℕ) (hv : v ≤ 2 * a.natAbs) : (coefOf a v).natAbs ≤ a.natAbs := by
  unfold coefOf; omega

theorem sum_natAbs_coef (l : List ℤ) (vs : List ℕ) (hv : ∀ av ∈ l.zip vs, av.2 ≤ 2 * av.1.natAbs) :
    (((l.zip vs).map (fun av => coefOf av.1 av.2)).map Int.natAbs).sum ≤ (l.map Int.natAbs).sum := by
  induction l generalizing vs with
  | nil => simp
  | cons a l ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      have h1 := coefOf_abs a v (hv (a, v) (by simp))
      have h2 := ih vs (fun av hav => hv av (by simp [hav]))
      omega

theorem topWeight_le_W (r : ℕ) : (circ c r).topWeight ≤ c.W := by
  unfold circ Call.W; split_ifs <;> omega

/-- A stage form moves by at most `2W` within a cell. -/
theorem stageForm_diff (w : List Bool) (h : decodeWitness c p w = some wt) (s r : ℕ) (hs : s < p.J)
    (hr : r < roleCount c.kind) (z z' : BitInput c.n) :
    |stageForm c wt r s z - stageForm c wt r s z'| ≤ 2 * (c.W : ℤ) := by
  obtain ⟨vs, hvs, hb⟩ := coef_shape c p wt w h s r hs hr
  have hsum : ((wt.coef s r).map Int.natAbs).sum ≤ c.W := by
    rw [hvs]
    exact (sum_natAbs_coef _ vs hb).trans (by have := topWeight_le_W c r; unfold NCircuit.topWeight at this; omega)
  have h1 := linForm_abs_le (circ c r).gates (wt.coef s r) z
  have h2 := linForm_abs_le (circ c r).gates (wt.coef s r) z'
  unfold stageForm
  have hW : (((wt.coef s r).map Int.natAbs).sum : ℤ) ≤ c.W := by exact_mod_cast hsum
  calc |linForm (circ c r).gates (wt.coef s r) z - linForm (circ c r).gates (wt.coef s r) z'|
      ≤ |linForm (circ c r).gates (wt.coef s r) z| + |linForm (circ c r).gates (wt.coef s r) z'| :=
        abs_sub _ _
    _ ≤ 2 * (c.W : ℤ) := by linarith

theorem scoreForm_diff (r : ℕ) (z z' : BitInput c.n) :
    |scoreForm c r z - scoreForm c r z'| ≤ 2 * (c.W : ℤ) := by
  have h1 := score_abs_le (circ c r) z
  have h2 := score_abs_le (circ c r) z'
  have hW : ((circ c r).topWeight : ℤ) ≤ c.W := by exact_mod_cast topWeight_le_W c r
  unfold scoreForm
  calc |(circ c r).score z - (circ c r).score z'| ≤ |(circ c r).score z| + |(circ c r).score z'| := abs_sub _ _
    _ ≤ 2 * (c.W : ℤ) := by linarith

theorem rateOf_le (j : ℕ) : rateOf p j ≤ (p.factors.sum : ℤ) := by
  unfold rateOf
  have : p.factors.getD j 0 ≤ p.factors.sum := by
    rw [List.getD_eq_getElem?_getD]
    cases hget : p.factors[j]? with
    | none => simp
    | some x => simpa using List.le_sum_of_mem (List.mem_of_getElem? hget)
  exact_mod_cast this

theorem rateOf_nonneg (j : ℕ) : 0 ≤ rateOf p j := by unfold rateOf; positivity

/-- A digit moves by at most `deltaBound` within a cell. -/
theorem digit_diff (w : List Bool) (h : decodeWitness c p w = some wt) (r j : ℕ) (hj : j < p.J)
    (hr : r < roleCount c.kind) (z z' : BitInput c.n) :
    |digit c p wt r j z - digit c p wt r j z'| ≤ (deltaBound c p : ℤ) := by
  have hδn : 2 * (1 + p.factors.sum) * c.W ≤ deltaBound c p := by
    unfold deltaBound; exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  have hδ : (2 * (1 + p.factors.sum) * c.W : ℤ) ≤ deltaBound c p := by exact_mod_cast hδn
  unfold digit
  cases j with
  | zero =>
    simp only [CountingCore.proposedDigit]
    have := stageForm_diff c p wt w h 0 r (by omega) hr z z'
    nlinarith [Nat.zero_le p.factors.sum, Nat.zero_le c.W]
  | succ j =>
    simp only [CountingCore.proposedDigit]
    have h1 := stageForm_diff c p wt w h (j + 1) r hj hr z z'
    have h2 := stageForm_diff c p wt w h j r (by omega) hr z z'
    have ha := rateOf_le p j
    have ha0 := rateOf_nonneg p j
    have e : stageForm c wt r (j + 1) z - rateOf p j * stageForm c wt r j z -
        (stageForm c wt r (j + 1) z' - rateOf p j * stageForm c wt r j z') =
        (stageForm c wt r (j + 1) z - stageForm c wt r (j + 1) z') -
          rateOf p j * (stageForm c wt r j z - stageForm c wt r j z') := by ring
    rw [e]
    calc _ ≤ |stageForm c wt r (j + 1) z - stageForm c wt r (j + 1) z'| +
          |rateOf p j * (stageForm c wt r j z - stageForm c wt r j z')| := abs_sub _ _
      _ = |stageForm c wt r (j + 1) z - stageForm c wt r (j + 1) z'| +
          rateOf p j * |stageForm c wt r j z - stageForm c wt r j z'| := by
          rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ 2 * c.W + p.factors.sum * (2 * c.W) := by
          have := mul_le_mul ha h2 (abs_nonneg _) (by positivity)
          linarith
      _ ≤ _ := by nlinarith

/-- `Φ^r` moves by at most `deltaBound` within a cell. -/
theorem phi_diff (w : List Bool) (h : decodeWitness c p w = some wt) (r : ℕ) (hJ : 1 ≤ p.J)
    (hr : r < roleCount c.kind) (z z' : BitInput c.n) :
    |phi c p wt r z - phi c p wt r z'| ≤ (deltaBound c p : ℤ) := by
  have h1 := stageForm_diff c p wt w h (p.J - 1) r (by omega) hr z z'
  have h2 := scoreForm_diff c r z z'
  unfold phi
  have e : (p.M1 : ℤ) * stageForm c wt r (p.J - 1) z - p.A * scoreForm c r z -
      ((p.M1 : ℤ) * stageForm c wt r (p.J - 1) z' - p.A * scoreForm c r z') =
      p.M1 * (stageForm c wt r (p.J - 1) z - stageForm c wt r (p.J - 1) z') -
        p.A * (scoreForm c r z - scoreForm c r z') := by ring
  rw [e]
  have hδn : 2 * (p.M1 + p.A) * c.W ≤ deltaBound c p := by
    unfold deltaBound; exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  have hδ : (2 * (p.M1 + p.A) * c.W : ℤ) ≤ deltaBound c p := by exact_mod_cast hδn
  calc _ ≤ |(p.M1 : ℤ) * (stageForm c wt r (p.J - 1) z - stageForm c wt r (p.J - 1) z')| +
        |(p.A : ℤ) * (scoreForm c r z - scoreForm c r z')| := abs_sub _ _
    _ = p.M1 * |stageForm c wt r (p.J - 1) z - stageForm c wt r (p.J - 1) z'| +
        p.A * |scoreForm c r z - scoreForm c r z'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity : (0 : ℤ) ≤ p.A)]
    _ ≤ p.M1 * (2 * c.W) + p.A * (2 * c.W) := by
        have := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ p.M1 by positivity)
        have := mul_le_mul_of_nonneg_left h2 (show (0 : ℤ) ≤ p.A by positivity)
        linarith
    _ ≤ _ := by nlinarith

end Bounds

end NearCubicGates.Close.Cells
