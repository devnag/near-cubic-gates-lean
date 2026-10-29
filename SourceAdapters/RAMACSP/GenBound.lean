import SourceAdapters.RAMACSP.GenMain

/-!
# Polynomial bounds of the generator's run

Paper: `lem:generator` ("in `poly(n, log t)` steps"; "Every loop runs over bit indices, code positions, registers,
coordinates, neighbors or patterns, never over the points of `H`"; "each field operation costs `poly(f)` steps") and
`lem:acsp-degree` (`m_H`, `f = log T + O(log log T)`).

Every quantity of the run is bounded by `A·Y^a` with `Y = |ClockRequest.word r| + 1` (`Bnd`). The numbers `f`,
`|x̄|`, `16C`, `τ`, `k` are linear in `Y` for fixed `V` (`lin_bound`); the run's constants
`K = N = 2·64^(c + size |word|)` dominate them once `64^c` dominates the constant (`boostC`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry

/-! ## Polynomial bounds in the request length -/

/-- The scale of a request: the length of its word, plus one. -/
def Yr (r : ClockRequest) : ℕ := (ClockRequest.word r).length + 1

/-- `g r ≤ A · Y^a` for every request. -/
def Bnd (g : ClockRequest → ℕ) : Prop := ∃ A a : ℕ, ∀ r, g r ≤ A * Yr r ^ a

theorem one_le_Yr (r : ClockRequest) : 1 ≤ Yr r := by simp [Yr]

namespace Bnd

theorem mono {g h : ClockRequest → ℕ} (hg : Bnd g) (hle : ∀ r, h r ≤ g r) : Bnd h := by
  obtain ⟨A, a, hA⟩ := hg
  exact ⟨A, a, fun r => (hle r).trans (hA r)⟩

theorem const (c : ℕ) : Bnd fun _ => c := ⟨c, 0, fun r => by simp⟩

theorem scale : Bnd Yr := ⟨1, 1, fun r => by simp⟩

theorem add {g h : ClockRequest → ℕ} (hg : Bnd g) (hh : Bnd h) : Bnd fun r => g r + h r := by
  obtain ⟨A, a, hA⟩ := hg
  obtain ⟨B, b, hB⟩ := hh
  refine ⟨A + B, a + b, fun r => ?_⟩
  show g r + h r ≤ _
  have p1 : Yr r ^ a ≤ Yr r ^ (a + b) := Nat.pow_le_pow_right (one_le_Yr r) (by omega)
  have p2 : Yr r ^ b ≤ Yr r ^ (a + b) := Nat.pow_le_pow_right (one_le_Yr r) (by omega)
  have := hA r
  have := hB r
  have := Nat.mul_le_mul_left A p1
  have := Nat.mul_le_mul_left B p2
  rw [Nat.add_mul]; omega

theorem mul {g h : ClockRequest → ℕ} (hg : Bnd g) (hh : Bnd h) : Bnd fun r => g r * h r := by
  obtain ⟨A, a, hA⟩ := hg
  obtain ⟨B, b, hB⟩ := hh
  refine ⟨A * B, a + b, fun r => ?_⟩
  calc g r * h r ≤ (A * Yr r ^ a) * (B * Yr r ^ b) := Nat.mul_le_mul (hA r) (hB r)
    _ = A * B * Yr r ^ (a + b) := by rw [pow_add]; ring

theorem pow {g : ClockRequest → ℕ} (hg : Bnd g) (e : ℕ) : Bnd fun r => g r ^ e := by
  obtain ⟨A, a, hA⟩ := hg
  refine ⟨A ^ e, a * e, fun r => ?_⟩
  calc g r ^ e ≤ (A * Yr r ^ a) ^ e := Nat.pow_le_pow_left (hA r) e
    _ = A ^ e * Yr r ^ (a * e) := by rw [mul_pow, ← pow_mul]

end Bnd

theorem word_len (r : ClockRequest) :
    (ClockRequest.word r).length = 2 * r.1.1 + 2 * r.2.bits.length + 2 := by
  simp only [ClockRequest.word, List.length_append, FL.frame_len, List.length_ofFn]; omega

theorem t_lt_bits (t : ℕ) : t < 2 ^ t.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self t

theorem bits_le_nbl (t : ℕ) : t.bits.length ≤ natBitLength t := by
  rw [Nat.size_eq_bits_len]; unfold natBitLength
  exact Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) t)

theorem pow_size_le' (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs := Nat.size_pos.2 hn
    have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
    have h2 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by rw [← pow_succ']; congr 1; omega
    omega

theorem Yr_le_input (r : ClockRequest) : Yr r ≤ 3 * (r.1.1 + natBitLength r.2 + 1) := by
  have := word_len r; have := bits_le_nbl r.2; simp only [Yr]; omega

theorem Yr_le_pow (r : ClockRequest) : Yr r ≤ 2 ^ Nat.size (ClockRequest.word r).length := by
  have := Nat.lt_size_self (ClockRequest.word r).length; simp only [Yr]; omega

theorem pow_size_scale (c : ℕ) (r : ClockRequest) :
    2 ^ (c * Nat.size (ClockRequest.word r).length) ≤ 2 ^ c * Yr r ^ c := by
  have h1 := pow_size_le' (ClockRequest.word r).length
  have h2 : 2 ^ Nat.size (ClockRequest.word r).length ≤ 2 * Yr r := by simp only [Yr]; omega
  calc 2 ^ (c * Nat.size (ClockRequest.word r).length) = (2 ^ Nat.size (ClockRequest.word r).length) ^ c := by
        rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * Yr r) ^ c := Nat.pow_le_pow_left h2 c
    _ = 2 ^ c * Yr r ^ c := by rw [mul_pow]

/-! ## The numbers are linear in `Y` -/

section Lin

variable (V : Verifier)

theorem w_le_bits (t : ℕ) : wordWidth (clockConst V) t ≤ 2 * (t.bits.length + clockConst V) := by
  have h1 := wordWidth_lt (clockConst V) t (by have := sixteen_le_clockConst V; omega)
  have h2 := clog_le_size t
  omega

theorem ctw_lt (t : ℕ) :
    clockConst V * (t + wordWidth (clockConst V) t) < 2 ^ (t.bits.length + 2 * clockConst V + 2) := by
  have h2 := w_le_bits V t
  have h1 := t_lt_bits t
  set c := clockConst V with hc
  set b := t.bits.length with hb
  have h3 : c < 2 ^ c := Nat.lt_two_pow_self
  have h4 : b + c < 2 ^ (b + c) := Nat.lt_two_pow_self
  have e1 : 2 ^ (b + c + 2) = 4 * 2 ^ (b + c) := by rw [pow_add]; ring
  have e2 : 2 ^ b ≤ 2 ^ (b + c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : t + wordWidth c t < 2 ^ (b + c + 2) := by omega
  calc c * (t + wordWidth c t) < 2 ^ c * 2 ^ (b + c + 2) := mul_lt_mul'' h3 h5 (Nat.zero_le _) (Nat.zero_le _)
    _ = 2 ^ (b + 2 * c + 2) := by rw [← pow_add]; congr 1; omega

theorem tau_le_bits (t : ℕ) : tau V t ≤ t.bits.length + 2 * clockConst V + 2 :=
  Nat.clog_le_of_le_pow (le_of_lt (ctw_lt V t))

/-- `f ≤ 40 (|bits t| + c + d + 4)`. -/
theorem fieldExp_le (t : ℕ) : fieldExp V t ≤ 40 * (t.bits.length + clockConst V + tagExp V + 4) := by
  have hτ := tau_le_bits V t
  have hω := wordExp_le_tau V t
  have hℓ : stageExp V t ≤ 2 * laneExp V t := by
    unfold stageExp
    exact le_trans (Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_two_pow_self (n := 2 * laneExp V t)))) le_rfl
  have hlf : Nat.clog 2 (4 * (domExp V t + 4)) ≤ 4 * (domExp V t + 4) :=
    Nat.clog_le_of_le_pow (le_of_lt Nat.lt_two_pow_self)
  unfold fieldExp domExp colExp laneExp at *
  omega

/-- `16·C = 16·2^d·w ≤ 64·2^d·(|bits t| + c)`. -/
theorem sixteenC_le (t : ℕ) : 16 * 2 ^ colExp V t ≤ 64 * 2 ^ tagExp V * (t.bits.length + clockConst V) := by
  have hw := w_le_bits V t
  have e : 2 ^ colExp V t = 2 ^ tagExp V * wordW V t := by unfold colExp; rw [pow_add]; rfl
  rw [e]
  have hw' : wordW V t ≤ 2 * (t.bits.length + clockConst V) := hw
  have : 2 ^ tagExp V * wordW V t ≤ 2 ^ tagExp V * (2 * (t.bits.length + clockConst V)) :=
    Nat.mul_le_mul_left _ hw'
  have e2 : 2 ^ tagExp V * (2 * (t.bits.length + clockConst V)) = 2 * (2 ^ tagExp V * (t.bits.length + clockConst V)) :=
    by ring
  have e3 : 64 * 2 ^ tagExp V * (t.bits.length + clockConst V) = 64 * (2 ^ tagExp V * (t.bits.length + clockConst V)) :=
    by ring
  omega

theorem xbar_le (r : ClockRequest) : 2 ^ inExp V r ≤ 2 * (r.1.1 + 1 + 2 * (r.2.bits.length + clockConst V)) := by
  have hw := w_le_bits V r.2
  rw [inExp_eq]
  have := two_pow_clog_lt (max (r.1.1 + 1) (wordW V r.2)) (by omega)
  have : max (r.1.1 + 1) (wordW V r.2) ≤ r.1.1 + 1 + wordW V r.2 := by omega
  have : wordW V r.2 = wordWidth (clockConst V) r.2 := rfl
  omega

/-- The linear constant: everything the run's `K` and `N` must exceed is at most `linConst V · Y`. -/
def linConst : ℕ := 1000 * (2 ^ tagExp V + 1) * (clockConst V + tagExp V + 10)

/-- **The numbers are linear in `Y`.** -/
theorem lin_bound (r : ClockRequest) :
    r.1.1 + r.2.bits.length + fieldExp V r.2 + 2 ^ inExp V r + 16 * 2 ^ colExp V r.2 + 2 * laneExp V r.2 +
      2 * tau V r.2 + clockConst V + tagExp V + 20 ≤ linConst V * Yr r := by
  have h1 := fieldExp_le V r.2
  have h2 := sixteenC_le V r.2
  have h3 := xbar_le V r
  have h4 := tau_le_bits V r.2
  have hY := word_len r
  have hk : laneExp V r.2 = tau V r.2 + 1 := rfl
  unfold linConst
  set c := clockConst V
  set d := tagExp V
  set D := 2 ^ tagExp V
  set b := r.2.bits.length
  set n := r.1.1
  have hYr : Yr r = 2 * n + 2 * b + 3 := by simp only [Yr]; omega
  rw [hYr]
  have hD : 1 ≤ D := Nat.one_le_two_pow
  set E := (D + 1) * (c + d + 10) with hE
  have hE1 : c + d + 10 ≤ E := by rw [hE]; nlinarith
  have hED : D ≤ E := by rw [hE]; nlinarith
  have hDc : D * c ≤ E := by rw [hE]; nlinarith
  have hDb : D * b ≤ E * b := Nat.mul_le_mul_right _ hED
  have hEn : n ≤ E * n := Nat.le_mul_of_pos_left _ (by omega)
  have hEb : b ≤ E * b := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : 64 * D * (b + c) = 64 * (D * b) + 64 * (D * c) := by ring
  have e2 : 1000 * (D + 1) * (c + d + 10) * (2 * n + 2 * b + 3) = 2000 * (E * n) + 2000 * (E * b) + 3000 * E := by
    rw [hE]; ring
  rw [e2]
  omega

end Lin

end NearCubicGates.Adapters.RAMACSP.Gen
