import Proof.Wire_3_5.LedgerBudget
import Proof.Wire_3_5.LedgerSparse

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule Filter

def addrWidth (dG q : ℕ) : ℕ := q + Nat.clog 2 ((q + 2) ^ dG) + 1

theorem le_addrWidth (dG q : ℕ) : q ≤ addrWidth dG q := by unfold addrWidth; omega

/-- `clog₂(x^d) ≤ d·clog₂ x`. -/
theorem clog_pow_le (x d : ℕ) : Nat.clog 2 (x ^ d) ≤ d * Nat.clog 2 x := by
  apply Nat.clog_le_of_le_pow
  calc x ^ d ≤ (2 ^ Nat.clog 2 x) ^ d := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) x) d
    _ = 2 ^ (d * Nat.clog 2 x) := by rw [← pow_mul, mul_comm]

/-- `clog₂(2^d·x) ≤ d + clog₂ x`. -/
theorem clog_two_pow_mul_le (d x : ℕ) : Nat.clog 2 (2 ^ d * x) ≤ d + Nat.clog 2 x := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by norm_num) x)

/-- The address width's excess is `O(log q)`: eventually `q_0 ≤ 2q`. -/
theorem eventually_addrWidth_le (dG : ℕ) : ∀ᶠ q : ℕ in atTop, addrWidth dG q ≤ 2 * q := by
  filter_upwards [eventually_mul_Lq_pow_le (dG + 1) 1] with q hq
  have h1 : Nat.clog 2 ((q + 2) ^ dG) ≤ dG * Lq q := clog_pow_le (q + 2) dG
  have hL := Lq_pos q
  unfold addrWidth
  rw [pow_one] at hq
  nlinarith

structure LengthSchedule where
  qs : ℕ → ℕ
  t : ℕ → ℕ
  dG : ℕ
  cw : ℕ
  J : ℕ
  qs_mono : Monotone qs
  qs_ge : ∀ a, a ≤ qs a
  qs_jump : ∀ a, qs (a + 1) ≤ qs a + cw
  t_pos : ∀ q, 1 ≤ t q
  t_jump : ∀ q q', cw ≤ q → q ≤ q' → q' ≤ q + cw → t q' ≤ t q + J
  t_tendsto : Tendsto t atTop atTop
  t_log : ∀ q, t q ≤ J * (Nat.log 2 (Lq q) + 1) + 1

namespace LengthSchedule
variable (S : LengthSchedule)

def coreLength (a : ℕ) : ℕ := S.t (S.qs a) * addrWidth S.dG (S.qs a)

def sourceIdx (n : ℕ) : ℕ := Nat.findGreatest (fun a => S.coreLength a ≤ n / 2) n

theorem le_coreLength (a : ℕ) : S.qs a ≤ S.coreLength a := by
  unfold coreLength
  calc S.qs a ≤ addrWidth S.dG (S.qs a) := le_addrWidth _ _
    _ = 1 * addrWidth S.dG (S.qs a) := (one_mul _).symm
    _ ≤ S.t (S.qs a) * addrWidth S.dG (S.qs a) := Nat.mul_le_mul_right _ (S.t_pos _)

theorem coreLength_sourceIdx (n : ℕ) (h : S.coreLength 0 ≤ n / 2) : S.coreLength (S.sourceIdx n) ≤ n / 2 :=
  Nat.findGreatest_spec (P := fun a => S.coreLength a ≤ n / 2) (Nat.zero_le n) h

theorem coreLength_succ_sourceIdx (n : ℕ) (hn : 1 ≤ n) : n / 2 < S.coreLength (S.sourceIdx n + 1) := by
  by_contra hc
  push Not at hc
  have hle : S.sourceIdx n + 1 ≤ n := by
    by_contra h2
    have h3 : S.sourceIdx n ≤ n := Nat.findGreatest_le n
    have h4 : S.sourceIdx n + 1 = n + 1 := by omega
    rw [h4] at hc
    have := (S.qs_ge (n + 1)).trans (S.le_coreLength (n + 1))
    omega
  have := Nat.le_findGreatest (P := fun a => S.coreLength a ≤ n / 2) hle hc
  unfold sourceIdx at this
  omega

/-- The selected index grows with `n`. -/
theorem tendsto_sourceIdx : Tendsto S.sourceIdx atTop atTop := by
  refine tendsto_atTop_atTop.2 fun A => ⟨A + 2 * S.coreLength A + 2, fun n hn => ?_⟩
  exact Nat.le_findGreatest (P := fun a => S.coreLength a ≤ n / 2) (by omega) (by omega)

theorem eventually_coreLength_succ_le : ∀ᶠ a : ℕ in atTop, 2 * S.coreLength (a + 1) ≤ 3 * S.coreLength a := by
  have hqs : Tendsto S.qs atTop atTop := tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => ha.trans (S.qs_ge a)⟩
  have ht : ∀ᶠ a : ℕ in atTop, 8 * S.J ≤ S.t (S.qs a) := (S.t_tendsto.comp hqs).eventually (eventually_ge_atTop _)
  filter_upwards [ht, eventually_ge_atTop (8 * (S.cw + S.dG) + S.cw)] with a hta ha
  set q := S.qs a
  set q' := S.qs (a + 1)
  have hq : a ≤ q := S.qs_ge a
  have hqq' : q ≤ q' := S.qs_mono (Nat.le_succ a)
  have hq'j : q' ≤ q + S.cw := S.qs_jump a
  have htj : S.t q' ≤ S.t q + S.J := S.t_jump q q' (by omega) hqq' hq'j
  -- q_0 jumps by at most cw + dG
  have hq0 : addrWidth S.dG q' ≤ addrWidth S.dG q + (S.cw + S.dG) := by
    unfold addrWidth
    have h1 : Nat.clog 2 ((q' + 2) ^ S.dG) ≤ S.dG + Nat.clog 2 ((q + 2) ^ S.dG) := by
      calc Nat.clog 2 ((q' + 2) ^ S.dG) ≤ Nat.clog 2 (2 ^ S.dG * (q + 2) ^ S.dG) := by
            apply Nat.clog_mono_right
            rw [← mul_pow]
            exact Nat.pow_le_pow_left (by omega) _
        _ ≤ S.dG + Nat.clog 2 ((q + 2) ^ S.dG) := clog_two_pow_mul_le _ _
    omega
  have hq0big : 8 * (S.cw + S.dG) ≤ addrWidth S.dG q := by have := le_addrWidth S.dG q; omega
  set t := S.t q
  set q0 := addrWidth S.dG q
  have h1 : 8 * (S.t q' ) ≤ 9 * t := by omega
  have h2 : 8 * addrWidth S.dG q' ≤ 9 * q0 := by omega
  have h3 : 64 * (S.t q' * addrWidth S.dG q') ≤ 81 * (t * q0) := by
    calc 64 * (S.t q' * addrWidth S.dG q') = (8 * S.t q') * (8 * addrWidth S.dG q') := by ring
      _ ≤ (9 * t) * (9 * q0) := Nat.mul_le_mul h1 h2
      _ = 81 * (t * q0) := by ring
  show 2 * (S.t q' * addrWidth S.dG q') ≤ 3 * (t * q0)
  omega

theorem eventually_lengths :
    ∀ᶠ n : ℕ in atTop, n / 3 ≤ S.coreLength (S.sourceIdx n) ∧ S.coreLength (S.sourceIdx n) ≤ n / 2 ∧
      S.qs (S.sourceIdx n) ≤ n ∧
      n ≤ (6 * (S.J + 1) + 2) * S.qs (S.sourceIdx n) * (Nat.log 2 (Lq (S.qs (S.sourceIdx n))) + 1) := by
  have hqs : Tendsto S.qs atTop atTop := tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => ha.trans (S.qs_ge a)⟩
  have hsucc := S.tendsto_sourceIdx.eventually S.eventually_coreLength_succ_le
  have haddr := (hqs.comp S.tendsto_sourceIdx).eventually (eventually_addrWidth_le S.dG)
  have hq1 := (hqs.comp S.tendsto_sourceIdx).eventually (eventually_ge_atTop 1)
  filter_upwards [hsucc, haddr, hq1, eventually_ge_atTop (2 * S.coreLength 0 + 2)] with n hs ha hq1 hn
  set a := S.sourceIdx n
  set q := S.qs a
  have hle : S.coreLength a ≤ n / 2 := S.coreLength_sourceIdx n (by omega)
  have hgt : n / 2 < S.coreLength (a + 1) := S.coreLength_succ_sourceIdx n (by omega)
  have hthird : n / 3 ≤ S.coreLength a := by omega
  refine ⟨hthird, hle, ?_, ?_⟩
  · have := S.le_coreLength a; omega
  · -- n ≤ 3 m_a + 2, m_a = t q_0 ≤ (J(log L + 1) + 1)(2q)
    have ht : S.t q ≤ (S.J + 1) * (Nat.log 2 (Lq q) + 1) := by
      have := S.t_log q
      nlinarith
    have hm : S.coreLength a ≤ (S.J + 1) * (Nat.log 2 (Lq q) + 1) * (2 * q) := by
      unfold coreLength
      exact Nat.mul_le_mul ht ha
    have hl1 : 1 ≤ q * (Nat.log 2 (Lq q) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e1 : (6 * (S.J + 1) + 2) * q * (Nat.log 2 (Lq q) + 1) =
        3 * ((S.J + 1) * (Nat.log 2 (Lq q) + 1) * (2 * q)) + 2 * (q * (Nat.log 2 (Lq q) + 1)) := by ring
    omega

end LengthSchedule

/-! ## The row-B instance -/

/-- `clog₂(x + c) ≤ clog₂ x + clog₂(c+1)` for `x ≥ 1`. -/
theorem clog_add_le (x c : ℕ) (hx : 1 ≤ x) : Nat.clog 2 (x + c) ≤ Nat.clog 2 x + Nat.clog 2 (c + 1) := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  calc x + c ≤ x * (c + 1) := by nlinarith
    _ ≤ 2 ^ Nat.clog 2 x * 2 ^ Nat.clog 2 (c + 1) :=
        Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) x) (Nat.le_pow_clog (by norm_num) (c + 1))

theorem nativeWidth_two_pow (kclk Apad a : ℕ) :
    nativeWidth kclk Apad (2 ^ a) = a * (kclk + 2) + Apad * Nat.clog 2 (a * (kclk + 2) + 2) + Apad := by
  unfold nativeWidth
  rw [← pow_mul, Nat.clog_pow 2 _ (by norm_num)]

theorem nativeWidth_two_pow_jump (kclk Apad a : ℕ) :
    nativeWidth kclk Apad (2 ^ (a + 1)) ≤
      nativeWidth kclk Apad (2 ^ a) + ((kclk + 2) + Apad * Nat.clog 2 (kclk + 2 + 1)) := by
  rw [nativeWidth_two_pow, nativeWidth_two_pow]
  have h := clog_add_le (a * (kclk + 2) + 2) (kclk + 2) (by omega)
  have e : (a + 1) * (kclk + 2) + 2 = a * (kclk + 2) + 2 + (kclk + 2) := by ring
  rw [e]
  have h2 := Nat.mul_le_mul_left Apad h
  have e2 : (a + 1) * (kclk + 2) = a * (kclk + 2) + (kclk + 2) := by ring
  rw [e2]
  nlinarith

/-- The row-B length schedule: `t = sched(L(q))` (the least `t` with `e_t ≤ L^{−3/16}`) on the paper's width `q(2^a)`. -/
noncomputable def rowBLengthSchedule {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (kclk Apad dG : ℕ) : LengthSchedule where
  qs := fun a => nativeWidth kclk Apad (2 ^ a)
  t := rowBt h0 h1
  dG := dG
  cw := (kclk + 2) + Apad * Nat.clog 2 (kclk + 2 + 1)
  J := Classical.choose (exists_block h0 h1)
  qs_mono := fun a b h => nativeWidth_mono kclk Apad (Nat.pow_le_pow_right (by norm_num) h)
  qs_ge := fun a => by
    rw [nativeWidth_two_pow]
    have : a ≤ a * (kclk + 2) := Nat.le_mul_of_pos_right a (by omega)
    omega
  qs_jump := fun a => nativeWidth_two_pow_jump kclk Apad a
  t_pos := fun q => (sched_spec h0 h1 (Lq q)).1
  t_jump := fun q q' hcw hqq' hq' => by
    have hL1 : Lq q' ≤ Lq q + 1 := by
      unfold Lq
      apply Nat.clog_le_of_le_pow
      rw [pow_succ]
      have := Nat.le_pow_clog (b := 2) (by norm_num) (q + 2)
      omega
    have hmono : sched ζ h0 h1 (Lq q') ≤ sched ζ h0 h1 (Lq q + 1) := sched_mono h0 h1 hL1
    exact hmono.trans (sched_jump h0 h1 (Classical.choose_spec (exists_block h0 h1)) (Lq q) (Lq_pos q))
  t_tendsto := by
    refine tendsto_atTop_atTop.2 fun T => ?_
    -- for `L` large, no `t < T` is good: `e_t ≥ e_T > 0`
    have hT : 0 < eps ζ (T + 1) := eps_pos h0 h1 _
    obtain ⟨Lb, hLb⟩ : ∃ Lb : ℕ, 1 < eps ζ (T + 1) ^ 16 * (Lb : ℚ) ^ 3 := by
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / eps ζ (T + 1) ^ 16)
      refine ⟨M + 1, ?_⟩
      have h16 : 0 < eps ζ (T + 1) ^ 16 := pow_pos hT 16
      have hM1 : (1 : ℚ) ≤ ((M + 1 : ℕ) : ℚ) := by push_cast; linarith [(Nat.cast_nonneg M : (0 : ℚ) ≤ M)]
      have hM2 : 1 / eps ζ (T + 1) ^ 16 < ((M + 1 : ℕ) : ℚ) := by push_cast; linarith
      have hM3 : ((M + 1 : ℕ) : ℚ) ≤ ((M + 1 : ℕ) : ℚ) ^ 3 := le_self_pow₀ hM1 (by norm_num)
      calc (1 : ℚ) = eps ζ (T + 1) ^ 16 * (1 / eps ζ (T + 1) ^ 16) := by field_simp
        _ < eps ζ (T + 1) ^ 16 * ((M + 1 : ℕ) : ℚ) := mul_lt_mul_of_pos_left hM2 h16
        _ ≤ eps ζ (T + 1) ^ 16 * ((M + 1 : ℕ) : ℚ) ^ 3 := mul_le_mul_of_nonneg_left hM3 h16.le
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 tendsto_Lq Lb
    refine ⟨N, fun q hq => ?_⟩
    by_contra hc
    push Not at hc
    have hgood := sched_spec h0 h1 (Lq q)
    set t := sched ζ h0 h1 (Lq q)
    have htT : t ≤ T + 1 := by simp only [rowBt] at hc; omega
    -- e_{T+1} ≤ e_t
    have he : eps ζ (T + 1) ≤ eps ζ t := by
      obtain ⟨j, hj⟩ : ∃ j, T + 1 = t + j := ⟨T + 1 - t, by omega⟩
      rw [hj, eps_add _ _ hgood.1]
      have : (1 - ζ) ^ j ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      nlinarith [eps_nonneg h0 h1 t]
    have hL : (Lb : ℚ) ≤ Lq q := by exact_mod_cast hN q hq
    have : eps ζ (T + 1) ^ 16 * (Lb : ℚ) ^ 3 ≤ eps ζ t ^ 16 * (Lq q : ℚ) ^ 3 := by
      apply mul_le_mul (pow_le_pow_left₀ hT.le he 16) (pow_le_pow_left₀ (Nat.cast_nonneg _) hL 3)
        (by positivity) (pow_nonneg (eps_nonneg h0 h1 _) _)
    linarith [hgood.2]
  t_log := fun q => sched_log h0 h1 (Classical.choose_spec (exists_block h0 h1)) (Lq q)

noncomputable def scheduleParams {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (cap : CapParams) (CD cr : ℕ) (hcr : 1 ≤ cr)
    (CΛ Cδ : ℕ) : RowBParams where
  cap := cap
  CD := CD
  cr := cr
  cr_pos := hcr
  Csp := Classical.choose (rowBSparse_pow8_le h0 h1 CΛ Cδ)
  sp := rowBSparse h0 h1 CΛ Cδ
  sp_le := Classical.choose_spec (rowBSparse_pow8_le h0 h1 CΛ Cδ)

end NearCubicWires.WireExponent3_5.Ledger
