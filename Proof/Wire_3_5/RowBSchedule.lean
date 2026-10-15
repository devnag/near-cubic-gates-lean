import StatementSupport

set_option autoImplicit false
set_option warningAsError true

namespace NearCubicWires.WireExponent3_5.Schedule

/-- `e_t = (1−ζ)^{t−1}(1/2−ζ)` over ℚ. -/
def eps (ζ : ℚ) (t : ℕ) : ℚ := (1 - ζ) ^ (t - 1) * (1 / 2 - ζ)

/-- The row-B condition at `L`: `t ≥ 1` and `e_t^16 · L^3 ≤ 1`, i.e. `e_t ≤ L^{−3/16}`. -/
def Good (ζ : ℚ) (L t : ℕ) : Prop := 1 ≤ t ∧ eps ζ t ^ 16 * (L : ℚ) ^ 3 ≤ 1

instance (ζ : ℚ) (L : ℕ) : DecidablePred (Good ζ L) := fun _ => by unfold Good; infer_instance

variable {ζ : ℚ}

theorem eps_nonneg (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (t : ℕ) : 0 ≤ eps ζ t := by
  unfold eps; exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)

theorem eps_pos (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (t : ℕ) : 0 < eps ζ t := by
  unfold eps; exact mul_pos (pow_pos (by linarith) _) (by linarith)

theorem eps_succ (t : ℕ) (ht : 1 ≤ t) : eps ζ (t + 1) = (1 - ζ) * eps ζ t := by
  unfold eps
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  simp [pow_succ]; ring

theorem eps_add (t j : ℕ) (ht : 1 ≤ t) : eps ζ (t + j) = (1 - ζ) ^ j * eps ζ t := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, eps_succ _ (by omega), ih, pow_succ]; ring

/-- A block length `J` with `((1−ζ)^16)^J ≤ 1/8`. -/
theorem exists_block (h0 : 0 < ζ) (h1 : ζ < 1 / 2) : ∃ J : ℕ, ((1 - ζ) ^ 16) ^ J ≤ 1 / 8 := by
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0 : ℚ) < 1 / 8 by norm_num)
    (show (1 - ζ) ^ 16 < 1 from pow_lt_one₀ (by linarith) (by linarith) (by norm_num))
  exact ⟨J, hJ.le⟩

/-- Some `t` is good: take `t = J·(log₂ L + 1) + 1`. This also gives `t = O(log L)`. -/
theorem good_at_log (h0 : 0 < ζ) (h1 : ζ < 1 / 2) {J : ℕ} (hJ : ((1 - ζ) ^ 16) ^ J ≤ 1 / 8) (L : ℕ) :
    Good ζ L (J * (Nat.log 2 L + 1) + 1) := by
  refine ⟨by omega, ?_⟩
  have hbase : (0 : ℚ) ≤ 1 - ζ := by linarith
  have he : eps ζ (J * (Nat.log 2 L + 1) + 1) = (1 - ζ) ^ (J * (Nat.log 2 L + 1)) * (1 / 2 - ζ) := by
    unfold eps; simp
  rw [he, mul_pow]
  have hL : (L : ℚ) < 2 ^ (Nat.log 2 L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) L
  have hL3 : (L : ℚ) ^ 3 ≤ 8 ^ (Nat.log 2 L + 1) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg L) hL.le 3
    calc (L : ℚ) ^ 3 ≤ (2 ^ (Nat.log 2 L + 1)) ^ 3 := h
      _ = 8 ^ (Nat.log 2 L + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpow : ((1 - ζ) ^ (J * (Nat.log 2 L + 1))) ^ 16 ≤ (1 / 8) ^ (Nat.log 2 L + 1) := by
    rw [← pow_mul, show J * (Nat.log 2 L + 1) * 16 = 16 * J * (Nat.log 2 L + 1) by ring, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (pow_nonneg hbase _) _) hJ _
  have hhalf : (1 / 2 - ζ) ^ 16 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have h8 : (1 / 8 : ℚ) ^ (Nat.log 2 L + 1) * 8 ^ (Nat.log 2 L + 1) = 1 := by
    rw [← mul_pow]; norm_num
  calc ((1 - ζ) ^ (J * (Nat.log 2 L + 1))) ^ 16 * (1 / 2 - ζ) ^ 16 * (L : ℚ) ^ 3
      ≤ (1 / 8) ^ (Nat.log 2 L + 1) * 1 * 8 ^ (Nat.log 2 L + 1) := by
        gcongr
    _ = 1 := by rw [mul_one, h8]

theorem exists_good (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (L : ℕ) : ∃ t, Good ζ L t := by
  obtain ⟨J, hJ⟩ := exists_block h0 h1
  exact ⟨_, good_at_log h0 h1 hJ L⟩

/-- **The row-B schedule**: the least `t ≥ 1` with `e_t^16 · L^3 ≤ 1`. -/
def sched (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (L : ℕ) : ℕ := Nat.find (exists_good h0 h1 L)

variable (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- Specification: `e_t^16 · L^3 ≤ 1`. -/
theorem sched_spec (L : ℕ) : Good ζ L (sched ζ h0 h1 L) := Nat.find_spec (exists_good h0 h1 L)

/-- Minimality gives the mass bound: either `t = 1`, or `e_t^16 · L^3 > (1−ζ)^16`, so `1/e_t = O(L^{3/16})`. -/
theorem sched_min (L : ℕ) :
    sched ζ h0 h1 L = 1 ∨ (1 - ζ) ^ 16 < eps ζ (sched ζ h0 h1 L) ^ 16 * (L : ℚ) ^ 3 := by
  by_cases h : sched ζ h0 h1 L = 1
  · exact Or.inl h
  right
  have hge : 1 ≤ sched ζ h0 h1 L := (sched_spec h0 h1 L).1
  obtain ⟨u, hu⟩ : ∃ u, sched ζ h0 h1 L = u + 1 := ⟨sched ζ h0 h1 L - 1, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have hnot : ¬ Good ζ L u := Nat.find_min (exists_good h0 h1 L) (by unfold sched at hu; omega)
  have hbad : 1 < eps ζ u ^ 16 * (L : ℚ) ^ 3 := by
    by_contra hc
    exact hnot ⟨hu1, not_lt.mp hc⟩
  rw [hu, eps_succ u hu1, mul_pow, mul_assoc]
  have hpos : (0 : ℚ) < (1 - ζ) ^ 16 := pow_pos (by linarith) _
  nlinarith

/-- Monotone in `L`. -/
theorem sched_mono {L L' : ℕ} (hL : L ≤ L') : sched ζ h0 h1 L ≤ sched ζ h0 h1 L' := by
  apply Nat.find_min'
  obtain ⟨ht, hg⟩ := sched_spec h0 h1 L'
  refine ⟨ht, le_trans ?_ hg⟩
  have : (L : ℚ) ^ 3 ≤ (L' : ℚ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hL) 3
  exact mul_le_mul_of_nonneg_left this (pow_nonneg (eps_nonneg h0 h1 _) _)

theorem sched_jump {J : ℕ} (hJ : ((1 - ζ) ^ 16) ^ J ≤ 1 / 8) (L : ℕ) (hL : 1 ≤ L) :
    sched ζ h0 h1 (L + 1) ≤ sched ζ h0 h1 L + J := by
  apply Nat.find_min'
  obtain ⟨ht, hg⟩ := sched_spec h0 h1 L
  refine ⟨by omega, ?_⟩
  rw [eps_add _ _ ht, mul_pow, ← pow_mul, mul_comm J 16, pow_mul]
  have hL' : ((L + 1 : ℕ) : ℚ) ^ 3 ≤ 8 * (L : ℚ) ^ 3 := by
    have : (1 : ℚ) ≤ L := by exact_mod_cast hL
    push_cast; nlinarith [sq_nonneg ((L : ℚ) - 1)]
  have hA : (0 : ℚ) ≤ ((1 - ζ) ^ 16) ^ J := pow_nonneg (pow_nonneg (by linarith) _) _
  have hB : (0 : ℚ) ≤ eps ζ (sched ζ h0 h1 L) ^ 16 := pow_nonneg (eps_nonneg h0 h1 _) _
  calc ((1 - ζ) ^ 16) ^ J * eps ζ (sched ζ h0 h1 L) ^ 16 * ((L + 1 : ℕ) : ℚ) ^ 3
      ≤ (1 / 8) * eps ζ (sched ζ h0 h1 L) ^ 16 * (8 * (L : ℚ) ^ 3) := by gcongr
    _ = eps ζ (sched ζ h0 h1 L) ^ 16 * (L : ℚ) ^ 3 := by ring
    _ ≤ 1 := hg

/-- `t = O(log L)`: `t(L) ≤ J·(log₂ L + 1) + 1`. -/
theorem sched_log {J : ℕ} (hJ : ((1 - ζ) ^ 16) ^ J ≤ 1 / 8) (L : ℕ) :
    sched ζ h0 h1 L ≤ J * (Nat.log 2 L + 1) + 1 :=
  Nat.find_min' _ (good_at_log h0 h1 hJ L)

/-- The advantage comparison in 16th powers: `e_t^16 · L(n)^2 < 1` once `L(n) ≤ 2 L(q)` and `L(q) > 4`. -/
theorem advantage16 {Lq Ln : ℕ} (hq : 4 < Lq) (hn : Ln ≤ 2 * Lq) :
    eps ζ (sched ζ h0 h1 Lq) ^ 16 * (Ln : ℚ) ^ 2 < 1 := by
  have hg := (sched_spec h0 h1 Lq).2
  set e := eps ζ (sched ζ h0 h1 Lq) ^ 16 with he
  have he0 : 0 ≤ e := pow_nonneg (eps_nonneg h0 h1 _) _
  have hq' : (4 : ℚ) < Lq := by exact_mod_cast hq
  have hn' : (Ln : ℚ) ≤ 2 * Lq := by exact_mod_cast hn
  have hLn2 : (Ln : ℚ) ^ 2 ≤ 4 * (Lq : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg Ln) hn' 2; nlinarith
  have hLq : 0 < (Lq : ℚ) := by linarith
  have key : e * (4 * (Lq : ℚ) ^ 2) * Lq ≤ 4 := by nlinarith
  have h4 : e * (4 * (Lq : ℚ) ^ 2) < 1 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  calc e * (Ln : ℚ) ^ 2 ≤ e * (4 * (Lq : ℚ) ^ 2) := mul_le_mul_of_nonneg_left hLn2 he0
    _ < 1 := h4

theorem advantage {Lq Ln : ℕ} (hq : 4 < Lq) (hn : Ln ≤ 2 * Lq) (hLn : 1 ≤ Ln) :
    (eps ζ (sched ζ h0 h1 Lq) : ℝ) < (Ln : ℝ) ^ (-((1 : ℝ) / 8)) := by
  have h16 := advantage16 h0 h1 hq hn
  set e : ℝ := (eps ζ (sched ζ h0 h1 Lq) : ℝ) with he
  have he0 : 0 ≤ e := by rw [he]; exact_mod_cast eps_nonneg h0 h1 _
  have hLn0 : (0 : ℝ) < Ln := by exact_mod_cast hLn
  have h16r : e ^ 16 < ((Ln : ℝ) ^ 2)⁻¹ := by
    have hlt : e ^ 16 * (Ln : ℝ) ^ 2 < 1 := by rw [he]; exact_mod_cast h16
    rw [← one_div]
    exact (lt_div_iff₀ (by positivity)).mpr hlt
  have hleft : (e ^ 16) ^ ((16 : ℕ)⁻¹ : ℝ) = e := Real.pow_rpow_inv_natCast he0 (by norm_num)
  have hright : (((Ln : ℝ) ^ 2)⁻¹) ^ ((16 : ℕ)⁻¹ : ℝ) = (Ln : ℝ) ^ (-((1 : ℝ) / 8)) := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hLn0.le,
      Real.rpow_neg hLn0.le]
    norm_num
  calc e = (e ^ 16) ^ ((16 : ℕ)⁻¹ : ℝ) := hleft.symm
    _ < (((Ln : ℝ) ^ 2)⁻¹) ^ ((16 : ℕ)⁻¹ : ℝ) :=
        Real.rpow_lt_rpow (by positivity) h16r (by norm_num)
    _ = (Ln : ℝ) ^ (-((1 : ℝ) / 8)) := hright

/-- `L(n) ≤ 2 L(q)` whenever `n + 2 ≤ (q+2)^2` (for instance `n ≤ q^2`): the ambient-length comparison. -/
theorem clog_sq_le {n q : ℕ} (h : n + 2 ≤ (q + 2) ^ 2) :
    Nat.clog 2 (n + 2) ≤ 2 * Nat.clog 2 (q + 2) := by
  apply Nat.clog_le_of_le_pow
  calc n + 2 ≤ (q + 2) ^ 2 := h
    _ ≤ (2 ^ Nat.clog 2 (q + 2)) ^ 2 := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) 2
    _ = 2 ^ (2 * Nat.clog 2 (q + 2)) := by rw [← pow_mul, mul_comm]

/-- Executable twin (ζ = 1/4): the schedule by linear search. -/
def schedExec (ζ : ℚ) (L : ℕ) : ℕ := ((List.range 400).find? fun t => decide (Good ζ L t)).getD 0

end NearCubicWires.WireExponent3_5.Schedule
