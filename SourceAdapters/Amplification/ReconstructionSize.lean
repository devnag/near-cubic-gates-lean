import SourceAdapters.Amplification.OracleSim
import SourceAdapters.Amplification.Layout

/-!
# A02, size: the reconstruction circuit has at most `A·(n/δ)^a·s'` nodes

`app:sources`, "Full-range amplification interface": "An `s'`-node circuit agreeing with the encoded function on more than a `1/2 + δ` fraction yields
an exact circuit for the original `n`-input function with at most `A(n/δ)^a s' + n + 2` nodes."

* `oracleSize`, `reconSize`: the node counts produced by `real_slot` and by `2(3n+3)` copies of `real_run` plus the
  majority count (`Reconstruction.lean`).
* `reconSize_le_W`: if every parameter is at most `W` (and `2^(b+τ) ≤ 2W`), the count is at most `10^5·W^5·s'`.
* `reconSize_bound`: with Theorem 29's constants `K`, `e` and the rounding constant `C`, every parameter is at most
  `W = (⌈K⌉+1)·(12·2^{size C}·X^{10})^{e+1}` for `X = n·2^(k+2) = n/δ`; hence the count is at most
  `A·X^a·s'` with `A = 10^5(⌈K⌉+1)^5(12·2^{size C})^{5(e+1)}`, `a = 50(e+1)` — absolute constants, fixed before
  `n`, `k` and the adversary.
-/

set_option autoImplicit false
namespace NearCubicGates.Adapters.Amplification

/-- The node count of the slot-oracle net (`real_slot`). -/
def oracleSize (t ℓ θ j0 Bs : ℕ) : ℕ :=
  2 ^ t * (ℓ + Bs) + 2 ^ t * ((θ + 1) + 2 ^ t * ((θ + 1) * (3 + 8 * 2 ^ 3))) +
    ((j0 + 2 + t) + 2 ^ t * ((j0 + 2 + t) * (4 + 8 * 2 ^ 4)))

/-- The node count of the reconstruction circuit: `2(3n+3)` runs of `T` steps and a majority. -/
def reconSize (n m t ℓ θ T Q τ j0 Bs : ℕ) : ℕ :=
  (2 * (3 * n + 3)) * (Fintype.card (CIdx τ (Nat.log 2 Q + 1) (T + m * t + 1)) +
      T * stepSize τ (Nat.log 2 Q + 1) (T + m * t + 1) (oracleSize t ℓ θ j0 Bs)) +
    ((3 * n + 4 + 1) + (2 * (3 * n + 3)) * ((3 * n + 4 + 1) * (3 + 8 * 2 ^ 3)))

/-- A monomial `W^i·Bs^j` with `i ≤ d`, `j ≤ 1` is at most `W^d·Bs`. -/
theorem monomial_le (W Bs i j d : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ Bs) (hi : i ≤ d) (hj : j ≤ 1) :
    W ^ i * Bs ^ j ≤ W ^ d * Bs := by
  apply Nat.mul_le_mul (Nat.pow_le_pow_right hW hi)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h <;> simp [h, hB]

/-- The count is a polynomial of degree five in parameters bounded by `W`, linear in `s'`. -/
theorem reconSize_le_W (n m t ℓ θ T Q τ j0 Bs W : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ Bs)
    (hN : 6 * n + 6 ≤ W) (hb : Nat.log 2 Q + 1 ≤ W) (hτ : τ ≤ W) (hbτ : 2 ^ (Nat.log 2 Q + 1 + τ) ≤ 2 * W)
    (hT : T ≤ W) (hmt : m * t ≤ W) (h2t : 2 ^ t ≤ W) (hℓ : ℓ ≤ W) (hθ : θ ≤ W) (hj : j0 ≤ W) (ht : t ≤ W) :
    reconSize n m t ℓ θ T Q τ j0 Bs ≤ 100000 * W ^ 5 * Bs := by
  have hP : T + m * t + 1 ≤ 3 * W := by omega
  have m1 := monomial_le W Bs 1 0 3 hW hB (by norm_num) (by norm_num)
  have m2 := monomial_le W Bs 2 0 3 hW hB (by norm_num) (by norm_num)
  have m3 := monomial_le W Bs 3 0 3 hW hB (by norm_num) (by norm_num)
  have m11 := monomial_le W Bs 1 1 3 hW hB (by norm_num) (by norm_num)
  have m21 := monomial_le W Bs 2 1 3 hW hB (by norm_num) (by norm_num)
  have m0 := monomial_le W Bs 0 0 3 hW hB (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at m0 m1 m2 m3 m11 m21
  have hsO : oracleSize t ℓ θ j0 Bs ≤ 1000 * W ^ 3 * Bs := by
    unfold oracleSize
    calc _ ≤ W * (W + Bs) + W * ((W + 1) + W * ((W + 1) * (3 + 8 * 2 ^ 3))) +
          ((W + 2 + W) + W * ((W + 2 + W) * (4 + 8 * 2 ^ 4))) := by gcongr
      _ ≤ _ := by ring_nf; ring_nf at m2 m21; linarith
  have hstep : stepSize τ (Nat.log 2 Q + 1) (T + m * t + 1) (oracleSize t ℓ θ j0 Bs) ≤ 40000 * W ^ 3 * Bs := by
    unfold stepSize
    calc _ ≤ W * (1 + 3 * W * (1 * ((2 + 1) + 8 * 2 ^ (2 + 1)))) + (W + (W * 4 + 2)) * ((W + W) + 8 * (2 * W)) +
          (W + (W * (3 * W) + W * (3 * W)) + 1) * (9 + 8 * 2 ^ 9) +
          (1000 * W ^ 3 * Bs + (W + (W * (3 * W) + W * (3 * W))) * (3 + 8 * 2 ^ 3)) := by gcongr
      _ ≤ _ := by ring_nf; ring_nf at m2 m21; linarith
  have n1 := monomial_le W Bs 1 0 5 hW hB (by norm_num) (by norm_num)
  have n2 := monomial_le W Bs 2 0 5 hW hB (by norm_num) (by norm_num)
  have n3 := monomial_le W Bs 3 0 5 hW hB (by norm_num) (by norm_num)
  have n0 := monomial_le W Bs 0 0 5 hW hB (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at n0 n1 n2 n3
  unfold reconSize
  rw [card_CIdx]
  calc _ ≤ W * ((W + (W * (3 * W) + W * (3 * W))) + W * (40000 * W ^ 3 * Bs)) +
        (W + W * (W * (3 + 8 * 2 ^ 3))) := by gcongr <;> omega
    _ ≤ _ := by ring_nf; ring_nf at n2 n3; linarith

/-- `2^{size n} ≤ 2n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hs : 1 ≤ Nat.size n := Nat.size_pos.mpr h
    have h1 : ¬ Nat.size n ≤ Nat.size n - 1 := by omega
    rw [Nat.size_le] at h1
    push Not at h1
    calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * n + 1 := by omega

/-- The basic parameters are polynomial in `X = n·2^(k+2)`. -/
theorem two_pow_tParam_le (C n k : ℕ) (hn : 1 ≤ n) :
    2 ^ tParam C n k ≤ 6 * 2 ^ Nat.size C * (n * 2 ^ (k + 2)) ^ 9 := by
  set X := n * 2 ^ (k + 2) with hX
  have hX1 : n ≤ X := Nat.le_mul_of_pos_right n (by positivity)
  have hX2 : 2 ^ (k + 2) ≤ X := Nat.le_mul_of_pos_left _ hn
  have h4 : 4 ≤ 2 ^ (k + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX4 : n * 4 ≤ X := Nat.mul_le_mul_left n h4
  have hm := mParam_le n k
  have hsn : 2 ^ Nat.size n ≤ 2 * X := by have := two_pow_size_le n; omega
  have hsm : 2 ^ Nat.size (mParam n k) ≤ 3 * X := by have := two_pow_size_le (mParam n k); omega
  have h6 : 2 ^ (6 * k + 12) ≤ X ^ 6 := by
    rw [show 6 * k + 12 = (k + 2) * 6 by ring, pow_mul]; exact Nat.pow_le_pow_left hX2 6
  unfold tParam hParam
  rw [show k + 2 + Nat.size n + 6 * k + 12 + Nat.size (mParam n k) + Nat.size C =
    (k + 2) + Nat.size n + (6 * k + 12) + Nat.size (mParam n k) + Nat.size C by ring]
  rw [pow_add, pow_add, pow_add, pow_add]
  calc 2 ^ (k + 2) * 2 ^ Nat.size n * 2 ^ (6 * k + 12) * 2 ^ Nat.size (mParam n k) * 2 ^ Nat.size C
      ≤ X * (2 * X) * X ^ 6 * (3 * X) * 2 ^ Nat.size C := by gcongr
    _ = 6 * 2 ^ Nat.size C * X ^ 9 := by ring

/-- The binary digits of `Q ≥ 1` number at most `Q`. -/
theorem log_succ_le (Q : ℕ) (hQ : 1 ≤ Q) : Nat.log 2 Q + 1 ≤ Q := by
  have h1 := Nat.pow_log_le_self 2 (show Q ≠ 0 by omega)
  have h2 : Nat.log 2 Q < 2 ^ Nat.log 2 Q := Nat.lt_two_pow_self
  omega

/-- **The size bound of A02**: the reconstruction circuit has at most `A·(n/δ)^a·|B|` nodes. -/
theorem reconSize_bound (C : ℕ) (K : ℝ) (e : ℕ) :
    ∃ A a : ℕ, ∀ n k T Q τ j0 Bs : ℕ, 1 ≤ n → 1 ≤ Q → 1 ≤ Bs →
      (T : ℝ) ≤ K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e →
      ((Q * 2 ^ τ : ℕ) : ℝ) ≤ K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e →
      j0 < ⌊1 / dyadicAcc k ^ 2⌋₊ →
      reconSize n (mParam n k) (tParam C n k) ((mParam n k + 1) * tParam C n k)
        (2 ^ (tParam C n k - 1) + 2 ^ (tParam C n k - (k + 3))) T Q τ j0 Bs ≤ A * (n * 2 ^ (k + 2)) ^ a * Bs := by
  set Kn := ⌈K⌉₊
  set Cs := 2 ^ Nat.size C
  refine ⟨100000 * (Kn + 1) ^ 5 * (12 * Cs) ^ (5 * (e + 1)), 50 * (e + 1), ?_⟩
  intro n k T Q τ j0 Bs hn hQ hB hT hD hj0
  set X := n * 2 ^ (k + 2) with hX
  set t := tParam C n k with ht
  set m := mParam n k with hm
  have hX1 : n ≤ X := Nat.le_mul_of_pos_right n (by positivity)
  have hX2 : 2 ^ (k + 2) ≤ X := Nat.le_mul_of_pos_left _ hn
  have hCs : 1 ≤ Cs := Nat.one_le_two_pow
  have hmn : m ≤ n := mParam_le n k
  set Y := 12 * Cs * X ^ 10 with hY
  set W := (Kn + 1) * Y ^ (e + 1) with hW
  have hXpos : 1 ≤ X := le_trans hn hX1
  have h4 : 4 ≤ 2 ^ (k + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX4 : n * 4 ≤ X := Nat.mul_le_mul_left n h4
  have hXY : 12 * X ≤ Y := by
    have h10 := Nat.le_self_pow (n := 10) (by norm_num) X
    rw [hY]
    calc 12 * X ≤ 12 * X ^ 10 := by omega
      _ ≤ 12 * Cs * X ^ 10 := Nat.mul_le_mul_right _ (by omega)
  have hY1 : 1 ≤ Y := by omega
  have hYW : Y ≤ W := by
    rw [hW]
    calc Y = 1 * Y ^ 1 := by ring
      _ ≤ (Kn + 1) * Y ^ (e + 1) := by gcongr <;> omega
  have h2t : 2 ^ t ≤ 6 * Cs * X ^ 9 := two_pow_tParam_le C n k hn
  have h2tY : 2 ^ t ≤ Y := by
    rw [hY]
    calc 2 ^ t ≤ 6 * Cs * X ^ 9 * 1 := by simpa using h2t
      _ ≤ 12 * Cs * X ^ 10 := by
          rw [pow_succ]
          calc 6 * Cs * X ^ 9 * 1 ≤ 6 * Cs * X ^ 9 * X := by gcongr
            _ ≤ 12 * Cs * (X ^ 9 * X) := by ring_nf; omega
  have htt : t < 2 ^ t := Nat.lt_two_pow_self
  have hℓ : (m + 1) * t ≤ Y := by
    rw [hY]
    calc (m + 1) * t ≤ (2 * X) * (6 * Cs * X ^ 9) := by gcongr <;> omega
      _ = 12 * Cs * X ^ 10 := by ring
  -- the real bound
  have hbase : (m : ℝ) + dParam n k + t + 1 / dyadicAcc k ^ 3 ≤ (Y : ℝ) := by
    have hd : dParam n k ≤ 2 * X ^ 3 := by
      unfold dParam
      have h2h : 2 ^ hParam n k ≤ 2 * X ^ 2 := by
        unfold hParam
        rw [pow_add]
        have := two_pow_size_le n
        calc 2 ^ (k + 2) * 2 ^ Nat.size n ≤ X * (2 * X) := by gcongr; omega
          _ = 2 * X ^ 2 := by ring
      calc m * (2 ^ hParam n k - 1) ≤ X * (2 * X ^ 2) := by gcongr <;> omega
        _ = 2 * X ^ 3 := by ring
    have hδ : 1 / dyadicAcc k ^ 3 = ((2 ^ (k + 2)) ^ 3 : ℕ) := by
      unfold dyadicAcc; push_cast; field_simp
    have hδX : (2 ^ (k + 2)) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hX2 3
    have hsum : m + dParam n k + t + (2 ^ (k + 2)) ^ 3 ≤ Y := by
      have hX3 : X ^ 3 ≤ X ^ 9 := Nat.pow_le_pow_right hXpos (by norm_num)
      have hX1' : X ≤ X ^ 9 := by
        calc X = X ^ 1 := by ring
          _ ≤ X ^ 9 := Nat.pow_le_pow_right hXpos (by norm_num)
      have h910 : X ^ 9 ≤ X ^ 10 := Nat.pow_le_pow_right hXpos (by norm_num)
      have : Cs * X ^ 9 ≤ Cs * X ^ 10 := Nat.mul_le_mul_left _ h910
      have : X ^ 9 ≤ Cs * X ^ 9 := Nat.le_mul_of_pos_left _ hCs
      rw [hY]; nlinarith
    rw [hδ]; exact_mod_cast hsum
  have hKY : K * ((m : ℝ) + dParam n k + t + 1 / dyadicAcc k ^ 3) ^ e ≤ ((Kn * Y ^ e : ℕ) : ℝ) := by
    have hb0 : (0 : ℝ) ≤ (m : ℝ) + dParam n k + t + 1 / dyadicAcc k ^ 3 := by
      have := dyadicAcc_pos k; positivity
    push_cast
    calc K * ((m : ℝ) + dParam n k + t + 1 / dyadicAcc k ^ 3) ^ e
        ≤ (Kn : ℝ) * ((m : ℝ) + dParam n k + t + 1 / dyadicAcc k ^ 3) ^ e :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
      _ ≤ (Kn : ℝ) * (Y : ℝ) ^ e := by gcongr
  have hKW : Kn * Y ^ e ≤ W := by
    rw [hW, pow_succ]
    calc Kn * Y ^ e ≤ (Kn + 1) * (Y ^ e * 1) := by rw [mul_one]; gcongr; omega
      _ ≤ (Kn + 1) * (Y ^ e * Y) := by gcongr
  have hTW : T ≤ W := le_trans (by exact_mod_cast hT.trans hKY) hKW
  have hDW : Q * 2 ^ τ ≤ W := le_trans (by exact_mod_cast hD.trans hKY) hKW
  have hτD : τ ≤ Q * 2 ^ τ := le_trans (Nat.lt_two_pow_self).le (Nat.le_mul_of_pos_left _ hQ)
  have hQD : Q ≤ Q * 2 ^ τ := Nat.le_mul_of_pos_right _ (by positivity)
  have hbτ : 2 ^ (Nat.log 2 Q + 1 + τ) ≤ 2 * W := by
    rw [pow_add, pow_succ]
    have := Nat.pow_log_le_self 2 (show Q ≠ 0 by omega)
    calc 2 ^ Nat.log 2 Q * 2 * 2 ^ τ ≤ Q * 2 * 2 ^ τ := by gcongr
      _ = 2 * (Q * 2 ^ τ) := by ring
      _ ≤ 2 * W := by omega
  have hj : j0 ≤ X ^ 2 := by
    have hfl : ⌊1 / dyadicAcc k ^ 2⌋₊ = (2 ^ (k + 2)) ^ 2 := by
      have : 1 / dyadicAcc k ^ 2 = (((2 ^ (k + 2)) ^ 2 : ℕ) : ℝ) := by unfold dyadicAcc; push_cast; field_simp
      rw [this, Nat.floor_natCast]
    rw [hfl] at hj0
    exact le_trans hj0.le (Nat.pow_le_pow_left hX2 2)
  have hjY : X ^ 2 ≤ Y := by
    rw [hY]
    calc X ^ 2 = 1 * 1 * X ^ 2 := by ring
      _ ≤ 12 * Cs * X ^ 10 := by gcongr <;> omega
  have hθ : 2 ^ (t - 1) + 2 ^ (t - (k + 3)) ≤ 2 ^ t := by
    have ht3 : k + 3 ≤ t := by rw [ht]; unfold tParam hParam; omega
    have h1 : 2 ^ (t - 1) ≤ 2 ^ (t - 1) := le_rfl
    have h2 : 2 ^ (t - (k + 3)) ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (t - 1) + 2 ^ (t - (k + 3)) ≤ 2 * 2 ^ (t - 1) := by omega
      _ = 2 ^ t := by rw [← pow_succ']; congr 1; omega
  have hmain := reconSize_le_W n m t ((m + 1) * t) (2 ^ (t - 1) + 2 ^ (t - (k + 3))) T Q τ j0 Bs W
    (by omega) hB (by omega) (by have := log_succ_le Q hQ; omega) (by omega) hbτ hTW
    (by have : m * t ≤ (m + 1) * t := Nat.mul_le_mul_right _ (by omega); omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  refine hmain.trans (le_of_eq ?_)
  rw [hW, hY]
  ring_nf

end NearCubicGates.Adapters.Amplification
