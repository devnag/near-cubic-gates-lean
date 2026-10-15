import Proof.Gates.Transfer.Schedule

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicGates.Target NearCubicGates.Close.Interfaces
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage

theorem lambda_ge_two {q : ℕ} (hq : 4 ≤ q) : 2 ≤ lambda q := by
  unfold lambda
  calc 2 = Nat.clog 2 4 := by decide
    _ ≤ Nat.clog 2 q := Nat.clog_mono_right 2 hq

theorem mu_ge_one {q : ℕ} (hq : 4 ≤ q) : 1 ≤ mu q := by
  unfold mu
  calc 1 = Nat.clog 2 2 := by decide
    _ ≤ Nat.clog 2 (lambda q) := Nat.clog_mono_right 2 (lambda_ge_two hq)

theorem lambda_mono {q m : ℕ} (h : q ≤ m) : lambda q ≤ lambda m := Nat.clog_mono_right 2 h

theorem mu_mono {q m : ℕ} (h : q ≤ m) : mu q ≤ mu m := Nat.clog_mono_right 2 (lambda_mono h)

/-- `MainBudget K m w` with `q ≤ m ≤ C q` and `C³ ≤ η K` gives `w ≤ η 𝒜₃(q)`. -/
theorem budget_of_mainBudget (C K q m w : ℕ) (η : ℝ) (hq : 4 ≤ q) (hqm : q ≤ m) (hm : m ≤ C * q)
    (hKpos : 0 < K) (hK : (C : ℝ) ^ 3 ≤ η * K) (hb : MainBudget K m w) : (w : ℝ) ≤ η * A3 q := by
  unfold MainBudget at hb
  have hl := lambda_ge_two hq
  have hmu := mu_ge_one hq
  set lq : ℝ := ((lambda q : ℕ) : ℝ) with hlq
  set mq : ℝ := ((mu q : ℕ) : ℝ) with hmq
  have hlq0 : (2 : ℝ) ≤ lq := by rw [hlq]; exact_mod_cast hl
  have hmq0 : (1 : ℝ) ≤ mq := by rw [hmq]; exact_mod_cast hmu
  -- monotone λ, μ and m ≤ C q in the integer budget
  have hint : (K * w * mu q ^ 7) ^ 4 * lambda q ^ 21 ≤ (C * q) ^ 12 := by
    calc (K * w * mu q ^ 7) ^ 4 * lambda q ^ 21
        ≤ (K * w * mu m ^ 7) ^ 4 * lambda m ^ 21 := by
          gcongr
          · exact mu_mono hqm
          · exact lambda_mono hqm
      _ ≤ m ^ 12 := hb
      _ ≤ (C * q) ^ 12 := Nat.pow_le_pow_left hm 12
  have hreal : ((K : ℝ) * w * mq ^ 7) ^ 4 * lq ^ 21 ≤ ((C : ℝ) * q) ^ 12 := by
    have := (Nat.cast_le (α := ℝ)).mpr hint
    push_cast at this
    simpa [hlq, hmq] using this
  set L : ℝ := lq ^ ((21 : ℝ) / 4) with hL
  have hLpos : 0 < L := Real.rpow_pos_of_pos (by linarith) _
  have hL4 : L ^ 4 = lq ^ 21 := by
    rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : ((K : ℝ) * w * mq ^ 7 * L) ^ 4 ≤ (((C : ℝ) * q) ^ 3) ^ 4 := by
    rw [mul_pow, hL4, ← pow_mul]
    exact hreal
  have hle : (K : ℝ) * w * mq ^ 7 * L ≤ ((C : ℝ) * q) ^ 3 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h4
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hden : 0 < L * mq ^ 7 := by positivity
  unfold A3
  rw [← hlq, ← hmq, ← hL]
  rw [mul_div_assoc', le_div_iff₀ hden]
  have hq3 : ((C : ℝ) * q) ^ 3 = (C : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring
  have : (K : ℝ) * ((w : ℝ) * (L * mq ^ 7)) ≤ (K : ℝ) * (η * (q : ℝ) ^ 3) := by
    calc (K : ℝ) * ((w : ℝ) * (L * mq ^ 7)) = (K : ℝ) * w * mq ^ 7 * L := by ring
      _ ≤ ((C : ℝ) * q) ^ 3 := hle
      _ = (C : ℝ) ^ 3 * (q : ℝ) ^ 3 := hq3
      _ ≤ η * K * (q : ℝ) ^ 3 := by gcongr
      _ = (K : ℝ) * (η * (q : ℝ) ^ 3) := by ring
  have := le_of_mul_le_mul_left this hKr
  linarith

open NearCubicWires.RepairSource.CloseoutLanguage in
/-- `m(q) ≤ K_amp (1 + 2 d_G + log₂ P) · q` for `q ≥ 1`. -/
theorem coreArity_le_linear (s : GateSources) (g : GateParams) (ν : ℕ) :
    g.coreArity s ν ≤ g.ampFactor * (1 + 2 * g.clauseDegree + g.positionLog) * g.width s ν := by
  have hq : 1 ≤ g.width s ν := by have := g.width_lower s ν; omega
  have hc := clause_linear g.clauseDegree (g.width s ν)
  unfold GateParams.coreArity GateParams.tableArity
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

variable {s : GateSources} {P : Gadget.ThreeQueryPCPP} {ε : ℝ}

theorem schedulePart (c : GateClosure s P ε) : SchedulePart c := by
  classical
  have hamp := c.ready.ampPos
  obtain ⟨η, hη, q0, hq0⟩ := c.ready.budgetLower
  set C : ℕ := c.g.ampFactor * (1 + 2 * c.g.clauseDegree + c.g.positionLog) with hC
  set K : ℕ := ⌈(C : ℝ) ^ 3 / η⌉₊ + 1 with hKdef
  have hKpos : 0 < K := Nat.succ_pos _
  have hK : (C : ℝ) ^ 3 ≤ η * K := by
    have h1 : (C : ℝ) ^ 3 / η ≤ ⌈(C : ℝ) ^ 3 / η⌉₊ := Nat.le_ceil _
    have h2 : (⌈(C : ℝ) ^ 3 / η⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have h3 : (C : ℝ) ^ 3 / η ≤ K := h1.trans h2
    rwa [div_le_iff₀ hη, mul_comm] at h3
  have hsel := selectionFacts c
  obtain ⟨oL, hL⟩ := lengthBound c
  obtain ⟨oS, hS⟩ := hsel.2
  obtain ⟨oB, hB⟩ := hsel.1 (max q0 4)
  refine ⟨hsel, K, hKpos, 5, by norm_num, max oL (max oS oB), fun n hn => hL n (le_trans (le_max_left _ _) hn), ?_⟩
  intro n hn w hw
  obtain ⟨-, -, hlen⟩ := hS n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hνbig := hB n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  set ν := c.g.selected s n
  set q := c.g.width s ν
  have hqν : ν + 1 ≤ q := c.g.width_lower s ν
  have hq4 : 4 ≤ q := by have := le_max_right q0 4; omega
  have hqq0 : q0 ≤ q := by have := le_max_left q0 4; omega
  have hqm : q ≤ c.g.nativeLength s n := by
    rw [hlen]
    unfold GateParams.coreArity GateParams.tableArity
    calc q ≤ q + clauseWidth c.g.clauseDegree q + c.g.positionLog := by omega
      _ ≤ c.g.ampFactor * _ := Nat.le_mul_of_pos_left _ hamp
  have hmC : c.g.nativeLength s n ≤ C * q := by rw [hlen]; exact coreArity_le_linear s c.g ν
  have hreal := budget_of_mainBudget C K q (c.g.nativeLength s n) w η hq4 hqm hmC hKpos hK hw
  have := hreal.trans (hq0 q hqq0)
  exact_mod_cast this

end NearCubicGates.Close.Transfer
