import Proof.Gates.Succinct.VerifierRun
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# 𝒱_G, part 11: the time bound `T_G`

Paper: lem:succinct-verifier (app:multitape), item (i) and the end of its proof: "If `n = L_ν`, the total is
`O(n) + O(N L_ν^3) + c_𝒟 T_clk(N) ≤ c′ 2^{C_clk ν}` … Choose `c_G ≥ c′` so large that `c_G 2^{C_clk ν} ≥ (c″+1)(ν+1)^{G+2}`
for every `ν ≥ 1`; this is possible because `(ν+1)^{G+2} 2^{−C_clk ν}` is bounded." Here `C_clk = k + 2` and
`T_G(n) = c_G · 2^{(k+2)·rootOf G n}`. **`exists_cG`**: some `c_G ≥ 1` bounds the verifier's run
(`bodyCost + 1 + H.time N`) and `n` itself by `c_G · 2^{(k+2)·rootOf G n}`, for every `n`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires

/-- Polynomials are dominated by `2^ν` (paper: "`(ν+1)^{G+2} 2^{−C_clk ν}` is bounded"). -/
theorem poly_le_exp (a : ℕ) : ∃ C, ∀ ν, (ν + 3) ^ a ≤ C * 2 ^ ν := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt a (show (1 : ℝ) < 2 by norm_num)
  have hev := h.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨8 + (N0 + 3) ^ a, fun ν => ?_⟩
  by_cases hν : N0 ≤ ν + 3
  · have h1 := hN0 (ν + 3) hν
    have h1' : ((ν + 3 : ℕ) : ℝ) ^ a / (2 : ℝ) ^ (ν + 3) ≤ 1 := h1
    have h2 : ((ν + 3 : ℕ) : ℝ) ^ a ≤ (2 : ℝ) ^ (ν + 3) := by
      rwa [div_le_one (by positivity)] at h1'
    have h3 : (ν + 3) ^ a ≤ 2 ^ (ν + 3) := by exact_mod_cast h2
    have h4 : 2 ^ (ν + 3) = 8 * 2 ^ ν := by ring
    have h5 : 8 * 2 ^ ν ≤ (8 + (N0 + 3) ^ a) * 2 ^ ν := Nat.mul_le_mul_right _ (by omega)
    omega
  · have h1 : (ν + 3) ^ a ≤ (N0 + 3) ^ a := Nat.pow_le_pow_left (by omega) _
    have h2 : (N0 + 3) ^ a ≤ (N0 + 3) ^ a * 2 ^ ν := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos ν)
    have h3 : (N0 + 3) ^ a * 2 ^ ν ≤ (8 + (N0 + 3) ^ a) * 2 ^ ν := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## The evaluator's costs, bounded by one parameter -/

theorem fieldCost_le (L b M : ℕ) (hL : L ≤ M) (hb : b ≤ M) (hP : 2 ^ b ≤ M) : fieldCost L b ≤ 2000 * (M + 1) ^ 2 := by
  unfold fieldCost
  have : (L + b + 2) * (2 ^ b + 1) ≤ (2 * M + 2) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem nodeCost_le (dl lb lp J M : ℕ) (hd : dl ≤ M) (hb : lb + lp ≤ M) (hP : 2 ^ (lb + lp) ≤ M) (hJ : J ≤ M) :
    nodeCost dl lb lp J ≤ 9000 * (M + 1) ^ 2 := by
  unfold nodeCost
  have := fieldCost_le dl (lb + lp) M hd hb hP
  nlinarith

theorem evalCost_le (dl lb lp M : ℕ) (hd : dl ≤ M) (hb : lb + lp ≤ M) (hP : 2 ^ (lb + lp) ≤ M) :
    evalCost dl lb lp ≤ 10 ^ 6 * (M + 1) ^ 3 := by
  have hlb : 2 ^ lb ≤ M := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hP
  have hn := nodeCost_le dl lb lp (2 ^ lb) M hd hb hP hlb
  have hf := fieldCost_le dl lb M hd (by omega) hlb
  unfold evalCost
  have h1 : (2 ^ lb + 4) * (nodeCost dl lb lp (2 ^ lb) + 100) ≤ (M + 4) * (9000 * (M + 1) ^ 2 + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem pow_add_two_le (x e : ℕ) (he : 1 ≤ e) : (x + 1) ^ e + 2 ≤ (x + 3) ^ e := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have h1 : (x + 1) ^ d ≤ (x + 3) ^ d := Nat.pow_le_pow_left (by omega) _
  have h2 : 1 ≤ (x + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ, pow_succ]
  nlinarith

/-- The constant `c_G` of lem:succinct-verifier, from the constant `C` of `poly_le_exp ((G+2)(G+10))`. -/
def cGOf (G c k C : ℕ) : ℕ :=
  50 * C + 310 * (G + 3) * C + 140 * C + 36 * C + 250000178 * C + (100 * (c + 1) * (k + 3) * 3 ^ (k + 2) + 10) +
    (120 * c + 30) + (2 * c + 21)

theorem cost_le (G c k C n : ℕ) (hC : ∀ ν, (ν + 3) ^ ((G + 2) * (G + 10)) ≤ C * 2 ^ ν) :
    bodyCost G c k n + 1 + c * ((2 ^ rootOf G n) ^ (k + 2) + 1) ≤
      cGOf G c k C * 2 ^ ((k + 2) * rootOf G n) ∧ n ≤ cGOf G c k C * 2 ^ ((k + 2) * rootOf G n) := by
  have hνn : rootOf G n ≤ n := rootOf_le G n
  have hlt := lt_root_succ_pow G n
  obtain ⟨ν, hν⟩ : ∃ ν, rootOf G n = ν := ⟨_, rfl⟩
  rw [hν] at hνn hlt ⊢
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ ν = N := ⟨_, rfl⟩
  have hX : 2 ^ ((k + 2) * ν) = N ^ (k + 2) := by rw [← hN, ← pow_mul, Nat.mul_comm]
  rw [hX, hN]
  obtain ⟨X, hXd⟩ : ∃ X, N ^ (k + 2) = X := ⟨_, rfl⟩
  rw [hXd]
  have hN1 : 1 ≤ N := hN ▸ Nat.one_le_two_pow
  have hX1 : 1 ≤ X := hXd ▸ Nat.one_le_pow _ _ (by omega)
  have hNX : N * N ≤ X := by
    rw [← hXd, show N * N = N ^ 2 by ring]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hNX1 : N ≤ X := by nlinarith
  set m := n + 2 with hm
  -- `m^{G+10} ≤ C·N`
  have hm1 : m ≤ (ν + 3) ^ (G + 2) := by have := pow_add_two_le ν (G + 2) (by omega); omega
  have hmC : m ^ (G + 10) ≤ C * N := by
    have := hC ν
    rw [pow_mul, hN] at this
    exact (Nat.pow_le_pow_left hm1 _).trans this
  have hC1 : 1 ≤ C := by
    have := hC 0
    rw [pow_zero, mul_one] at this
    exact le_trans (Nat.one_le_pow _ _ (by omega)) this
  have hmG : m ≤ m ^ (G + 10) := Nat.le_self_pow (by omega) _
  have hmN : m ≤ C * N := hmG.trans hmC
  have hCX : C * N ≤ C * X := Nat.mul_le_mul_left _ hNX1
  have hCNN : C * (N * N) ≤ C * X := Nat.mul_le_mul_left _ hNX
  -- term bounds
  have e50 : 50 * C * X = 50 * (C * X) := by ring
  have t1 : 45 * n + 5 ≤ 50 * C * X := by rw [e50]; omega
  have t2 : (n + 2) * (stepCost G n + 10) ≤ 310 * (G + 3) * C * X := by
    unfold stepCost
    rw [← hm]
    have h1 : m ^ (G + 4) ≤ m ^ (G + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : m * m ^ (G + 3) = m ^ (G + 4) := by ring
    have h3 : m ≤ m ^ (G + 4) := Nat.le_self_pow (by omega) _
    have h4 : m ^ (G + 4) ≤ C * X := h1.trans (hmC.trans hCX)
    have h5 : (G + 3) * m ^ (G + 4) ≤ (G + 3) * (C * X) := Nat.mul_le_mul_left _ h4
    have : m * (300 * (G + 3) * m ^ (G + 3) + 10) ≤ 310 * ((G + 3) * m ^ (G + 4)) := by
      have : m * (300 * (G + 3) * m ^ (G + 3) + 10) = 300 * ((G + 3) * m ^ (G + 4)) + 10 * m := by ring
      rw [this]
      have : m ≤ (G + 3) * m ^ (G + 4) := h3.trans (Nat.le_mul_of_pos_left _ (by omega))
      omega
    calc m * (300 * (G + 3) * m ^ (G + 3) + 10) ≤ 310 * ((G + 3) * m ^ (G + 4)) := this
      _ ≤ 310 * ((G + 3) * (C * X)) := Nat.mul_le_mul_left _ h5
      _ = 310 * (G + 3) * C * X := by ring
  have t3 : 2 * (18 * n + 3 + 30 * n + 20 * n + 1) ≤ 140 * C * X := by
    rw [show 140 * C * X = 140 * (C * X) by ring]; omega
  have t4 : ν * (18 * N + 11) + 7 * ν + 7 ≤ 36 * C * X := by
    have h0 : ν * (18 * N + 11) ≤ m * (18 * N + 11) := Nat.mul_le_mul_right _ (by omega)
    have h0' : m * (18 * N + 11) = 18 * (m * N) + 11 * m := by ring
    have hmN1 : m ≤ m * N := Nat.le_mul_of_pos_right _ hN1
    have h1 : ν * (18 * N + 11) + 7 * ν + 7 ≤ 36 * (m * N) := by omega
    have h2 : m * N ≤ C * (N * N) := by
      calc m * N ≤ (C * N) * N := Nat.mul_le_mul_right _ hmN
        _ = C * (N * N) := by ring
    rw [show 36 * C * X = 36 * (C * X) by ring]; omega
  have hmm : m ≤ m ^ 2 := Nat.le_self_pow (by omega) _
  have hM1 : n ≤ 4 * m ^ 2 := by omega
  have hM2 : hc n + hc ν ≤ 4 * m ^ 2 := by have := hc_le n; have := hc_le ν; omega
  have hM3 : 2 ^ (hc n + hc ν) ≤ 4 * m ^ 2 := by
    rw [pow_add]
    have h1 := two_pow_hc_le n
    have h2 := two_pow_hc_le ν
    have : 2 ^ hc n * 2 ^ hc ν ≤ (2 * n + 1) * (2 * ν + 1) := Nat.mul_le_mul h1 h2
    have h3 : (2 * n + 1) * (2 * ν + 1) ≤ (2 * m) * (2 * m) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 * m) * (2 * m) = 4 * m ^ 2 := by ring
    omega
  have hev := evalCost_le n (hc n) (hc ν) (4 * m ^ 2) hM1 hM2 hM3
  have hev2 : evalCost n (hc n) (hc ν) ≤ 125000000 * (C * N) := by
    have h1 : (4 * m ^ 2 + 1) ^ 3 ≤ 125 * m ^ 6 := by
      have : 4 * m ^ 2 + 1 ≤ 5 * m ^ 2 := by nlinarith
      calc (4 * m ^ 2 + 1) ^ 3 ≤ (5 * m ^ 2) ^ 3 := Nat.pow_le_pow_left this _
        _ = 125 * m ^ 6 := by ring
    have h2 : m ^ 6 ≤ m ^ (G + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 10 ^ 6 * (4 * m ^ 2 + 1) ^ 3 ≤ 10 ^ 6 * (125 * m ^ 6) := Nat.mul_le_mul_left _ h1
    omega
  have t5 : (N + 1) * (pointCost n (hc n) (hc ν) N + 10) + 30 * N + 20 ≤ 250000178 * C * X := by
    unfold pointCost
    generalize evalCost n (hc n) (hc ν) = Ev at hev2 ⊢
    have hNC : N ≤ C * N := Nat.le_mul_of_pos_left _ hC1
    have h1 : Ev + 14 * N + 40 + 10 ≤ 125000064 * (C * N) := by omega
    have h2 : (N + 1) * (Ev + 14 * N + 40 + 10) ≤ (2 * N) * (125000064 * (C * N)) :=
      Nat.mul_le_mul (by omega) h1
    have h3 : (2 * N) * (125000064 * (C * N)) = 250000128 * (C * (N * N)) := by ring
    have hXC : X ≤ C * X := Nat.le_mul_of_pos_left _ hC1
    have h5 : 250000178 * C * X = 250000128 * (C * X) + 50 * (C * X) := by ring
    rw [h5]
    omega
  have t6 : 100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) + 10 ≤ (100 * (c + 1) * (k + 3) * 3 ^ (k + 2) + 10) * X := by
    have h1 : (N + 2) ^ (k + 2) ≤ 3 ^ (k + 2) * X := by
      rw [← hXd, ← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    have h2 : 100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) ≤ 100 * (c + 1) * (k + 3) * (3 ^ (k + 2) * X) :=
      Nat.mul_le_mul_left _ h1
    have e : (100 * (c + 1) * (k + 3) * 3 ^ (k + 2) + 10) * X =
        100 * (c + 1) * (k + 3) * (3 ^ (k + 2) * X) + 10 * X := by ring
    rw [e]; omega
  have hcX : c ≤ c * X := Nat.le_mul_of_pos_right _ hX1
  have t7 : 60 * htVal c k N + 30 ≤ (120 * c + 30) * X := by
    unfold htVal; rw [hXd]
    have e1 : 60 * (c * (X + 1)) = 60 * (c * X) + 60 * c := by ring
    have e2 : (120 * c + 30) * X = 120 * (c * X) + 30 * X := by ring
    rw [e1, e2]; omega
  have t8 : 20 + 1 + c * (X + 1) ≤ (2 * c + 21) * X := by
    have e1 : c * (X + 1) = c * X + c := by ring
    have e2 : (2 * c + 21) * X = 2 * (c * X) + 21 * X := by ring
    rw [e1, e2]; omega
  have hcost : bodyCost G c k n = (45 * n + 5) + (n + 2) * (stepCost G n + 10) +
      2 * (18 * n + 3 + 30 * n + 20 * n + 1) + (ν * (18 * N + 11) + 7 * ν + 7) +
      ((N + 1) * (pointCost n (hc n) (hc ν) N + 10) + 30 * N + 20) +
      (100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) + 10) + (60 * htVal c k N + 30) + 20 := by
    simp only [bodyCost, hν, hN]
  have hsum : cGOf G c k C * X = 50 * C * X + 310 * (G + 3) * C * X + 140 * C * X + 36 * C * X +
      250000178 * C * X + (100 * (c + 1) * (k + 3) * 3 ^ (k + 2) + 10) * X + (120 * c + 30) * X +
      (2 * c + 21) * X := by unfold cGOf; ring
  refine ⟨?_, ?_⟩
  · rw [hcost, hsum]; omega
  · rw [hsum]
    have : n ≤ 50 * C * X := by rw [e50]; omega
    omega

/-- **The constant `c_G`** (paper lem:succinct-verifier, proof of (i)–(ii)). -/
theorem exists_cG (G c k : ℕ) : ∃ cG, 1 ≤ cG ∧ ∀ n,
    bodyCost G c k n + 1 + c * ((2 ^ rootOf G n) ^ (k + 2) + 1) ≤ cG * 2 ^ ((k + 2) * rootOf G n) ∧
      n ≤ cG * 2 ^ ((k + 2) * rootOf G n) := by
  obtain ⟨C, hC⟩ := poly_le_exp ((G + 2) * (G + 10))
  exact ⟨cGOf G c k C, by unfold cGOf; omega, fun n => cost_le G c k C n hC⟩

end NearCubicGates.Close.Succinct
