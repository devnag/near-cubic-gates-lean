import Proof.Wire_3_5.SamplerFix
import Proof.Wire_3_5.Runtime
import Proof.Wire_3_5.CompilerTable

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared

/-- **The sample count** at error `η = n^{−D}`, `I` matrix indices, `N = 2^{kh}`:
`Q = 2^{⌈5kh/4⌉}·2^{13}·I·n^{2D}`. -/
def sampleCount (kh D n I : ℕ) : ℕ := 2 ^ ((5 * kh + 3) / 4) * (2 ^ 13 * I * n ^ (2 * D))

/-- **The count meets the direct `h = 4` rate**: `4⁸C₈·I·N⁵ ≤ Q⁴·η⁸` at `η = n^{−D}` (for `n, I ≥ 1`). -/
theorem sampleCount_rate (kh D n I : ℕ) (hn : 1 ≤ n) (hI : 1 ≤ I) :
    4 ^ 8 * C8 * (I : ℝ) * ((2 ^ kh : ℕ) : ℝ) ^ 5 ≤ (sampleCount kh D n I : ℝ) ^ 4 * ((1 : ℝ) / (n : ℝ) ^ D) ^ 8 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hIr : (1 : ℝ) ≤ I := by exact_mod_cast hI
  have hx : (0 : ℝ) < (n : ℝ) ^ D := pow_pos (by linarith) D
  set a : ℝ := (2 : ℝ) ^ ((5 * kh + 3) / 4)
  set b : ℝ := (2 : ℝ) ^ kh
  set x : ℝ := (n : ℝ) ^ D
  have hQ : (sampleCount kh D n I : ℝ) = a * (2 ^ 13 * (I : ℝ) * x ^ 2) := by
    unfold sampleCount; push_cast
    rw [show (n : ℝ) ^ (2 * D) = x ^ 2 by rw [← pow_mul, mul_comm]]
    norm_num [a]
  have hb : (((2 ^ kh : ℕ) : ℝ)) = b := by push_cast; rfl
  have h2 : b ^ 5 ≤ a ^ 4 := by
    rw [← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hI4 : (I : ℝ) ≤ (I : ℝ) ^ 4 := by
    calc (I : ℝ) = (I : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (I : ℝ) ^ 4 := pow_le_pow_right₀ hIr (by norm_num)
  have hR : (a * (2 ^ 13 * (I : ℝ) * x ^ 2)) ^ 4 * ((1 : ℝ) / x) ^ 8 = a ^ 4 * (2 ^ 52 * (I : ℝ) ^ 4) := by
    field_simp
  have hC : (4 : ℝ) ^ 8 * C8 ≤ 2 ^ 52 := by unfold C8; norm_num
  rw [hQ, hb, hR]
  have hb0 : (0 : ℝ) ≤ b ^ 5 := by positivity
  have hI0 : (0 : ℝ) ≤ (I : ℝ) := by linarith
  calc 4 ^ 8 * C8 * (I : ℝ) * b ^ 5 ≤ 2 ^ 52 * (I : ℝ) * b ^ 5 := by
        apply mul_le_mul_of_nonneg_right _ hb0
        exact mul_le_mul_of_nonneg_right hC hI0
    _ ≤ 2 ^ 52 * (I : ℝ) ^ 4 * a ^ 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hI4 (by norm_num)) h2 hb0 (by positivity)
    _ = a ^ 4 * (2 ^ 52 * (I : ℝ) ^ 4) := by ring

theorem N_le_sampleCount (kh D n I : ℕ) (hn : 1 ≤ n) (hI : 1 ≤ I) : 2 ^ kh ≤ sampleCount kh D n I := by
  unfold sampleCount
  calc 2 ^ kh ≤ 2 ^ ((5 * kh + 3) / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ ((5 * kh + 3) / 4) * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hI) (Nat.pow_pos hn))

theorem sampleCount_le (kh D n I C : ℕ) (hn : 2 ≤ n) (hI : I ≤ n ^ C) :
    sampleCount kh D n I ≤ 2 ^ ((3 * (2 * kh) + 3) / 4) * n ^ (13 + C + 2 * D) := by
  unfold sampleCount
  apply Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h13 : 2 ^ 13 ≤ n ^ 13 := Nat.pow_le_pow_left hn 13
  calc 2 ^ 13 * I * n ^ (2 * D) ≤ n ^ 13 * n ^ C * n ^ (2 * D) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul h13 hI)
    _ = n ^ (13 + C + 2 * D) := by rw [pow_add, pow_add]

def ellFor (kh Q : ℕ) : ℕ := max 1 (max (2 * kh) (Nat.clog 2 Q))

/-- The generator parameters for `N = 2^{kh}` and `Q` samples. -/
def seedParamsFor (kh Q : ℕ) : SeedParams where
  ell := ellFor kh Q
  kh := kh
  Q := Q
  one_le_ell := le_max_left _ _
  k_le := le_trans (le_max_left _ _) (le_max_right _ _)
  Q_le := (Nat.le_pow_clog (by norm_num) Q).trans
    (Nat.pow_le_pow_right (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem seedBits_le (kh Q : ℕ) : 8 * (seedParamsFor kh Q).ell ≤ 8 * (2 * kh + Nat.clog 2 Q + 1) := by
  show 8 * ellFor kh Q ≤ _
  unfold ellFor
  apply Nat.mul_le_mul_left
  apply max_le (by omega) (max_le (by omega) (by omega))

theorem samp_load (A m Q' P d k L c : ℕ) (hA : A ≤ 2 ^ (c * (k + L ^ 2))) (hm : m ≤ c * L)
    (hQ : Q' ≤ c * (k + L)) (hP : P + 1 ≤ 2 ^ (c * (k + L))) :
    A * 2 ^ m * (Q' * (P + 1) ^ (Q' * d)) ≤ 2 ^ ((3 * c + c ^ 2) * ((k + L) ^ 2 * d + k + L ^ 2)) := by
  have hQ2 : Q' ≤ 2 ^ (c * (k + L)) := hQ.trans (Nat.lt_two_pow_self).le
  have hmain := Compiler.occurrences_le_budget A m Q' P d (c * (k + L ^ 2)) (c * (k + L)) (c * (k + L))
    ((3 * c + c ^ 2) * ((k + L) ^ 2 * d + k + L ^ 2)) hA hQ2 hP (by
      have hL : L ≤ L ^ 2 := by
        rcases Nat.eq_zero_or_pos L with h | h
        · simp [h]
        · calc L = L * 1 := (mul_one L).symm
            _ ≤ L * L := Nat.mul_le_mul_left _ h
            _ = L ^ 2 := (sq L).symm
      have e1 : Q' * d * (c * (k + L)) ≤ c * (k + L) * d * (c * (k + L)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hQ)
      have e2 : c * (k + L) * d * (c * (k + L)) = c ^ 2 * ((k + L) ^ 2 * d) := by ring
      have hm' : m ≤ c * L ^ 2 := hm.trans (Nat.mul_le_mul_left _ hL)
      have h1 : c * (k + L) ≤ c * (k + L ^ 2) := Nat.mul_le_mul_left _ (by omega)
      have h2 : Q' * d * (c * (k + L)) ≤ c ^ 2 * ((k + L) ^ 2 * d) := e1.trans e2.le
      generalize (k + L) ^ 2 * d = X at h2 ⊢
      have hR : (3 * c + c ^ 2) * (X + k + L ^ 2) =
          3 * (c * X) + 3 * (c * k) + 3 * (c * L ^ 2) + c ^ 2 * X + c ^ 2 * k + c ^ 2 * L ^ 2 := by ring
      have hL2 : c * (k + L ^ 2) = c * k + c * L ^ 2 := by ring
      rw [hR]
      rw [hL2] at h1 ⊢
      omega)
  exact hmain

theorem final_pass_sampler (n kh D I C A c : ℕ) (hn : 2 ≤ n) (hI : I ≤ n ^ C) (hk : 2 * kh ≤ n) :
    2 ^ (n - 2 * kh) * (sampleCount kh D n I * (c * n ^ A)) ≤
      c * (2 ^ (n - 2 * kh / 4) * n ^ (A + (13 + C + 2 * D))) :=
  Cost.final_pass_count n (2 * kh) (sampleCount kh D n I) A (13 + C + 2 * D) c hk (sampleCount_le kh D n I C hn hI)

end NearCubicWires.WireExponent3_5.Sampler
