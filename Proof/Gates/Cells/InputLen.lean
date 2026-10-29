import Proof.Gates.Cells.Bounds
import Proof.Gates.Cells.Mac
import Proof.Gates.CounterMachine.CellNats

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN circN gateN intN ratN bitN srList cellN_word)

/-! ## Bit lengths and word lengths -/

theorem nbl_le_of_lt {v k : ℕ} (h : v < 2 ^ k) (hk : 1 ≤ k) : natBitLength v ≤ k := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem nbl_le_self (v : ℕ) : natBitLength v ≤ v + 1 :=
  nbl_le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))) (by omega)

theorem nbl_le_of_le {v w : ℕ} (h : v ≤ w) : natBitLength v ≤ w + 1 := (nbl_le_self v).trans (by omega)

theorem nbl_mul (v w : ℕ) : natBitLength (v * w) ≤ natBitLength v + natBitLength w := by
  apply nbl_le_of_lt _ (by have := natBitLength_pos v; omega)
  rw [pow_add]
  exact Nat.mul_lt_mul'' (lt_natBitLength v) (lt_natBitLength w)

theorem nbl_le_word (v : ℕ) : natBitLength v ≤ (natWord v).length := by rw [natWord_length]; omega

theorem flat_len_le (L : List ℕ) (Λ : ℕ) (h : ∀ x ∈ L, natBitLength x ≤ Λ) :
    (L.flatMap natWord).length ≤ L.length * (2 * Λ + 1) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.flatMap_cons, List.length_append, natWord_length, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    nlinarith

theorem flatMap_len_le {α β : Type} (l : List α) (f : α → List β) (m : ℕ) (h : ∀ a ∈ l, (f a).length ≤ m) :
    (l.flatMap f).length ≤ l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem length_le_sum_natAbs (l : List ℤ) (h : ∀ a ∈ l, a ≠ 0) : l.length ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 : a ≠ 0 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr h1
    omega

theorem natAbs_le_sum (l : List ℤ) (a : ℤ) (ha : a ∈ l) : a.natAbs ≤ (l.map Int.natAbs).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-! ## The radius -/

theorem ratWord_bits (q : ℚ) : natBitLength q.num.natAbs ≤ (ratWord q).length ∧
    natBitLength q.den ≤ (ratWord q).length := by
  have h1 := nbl_le_word q.num.natAbs
  have h2 := nbl_le_word q.den
  simp only [ratWord, Interfaces.intWord, List.length_append] at *
  omega

/-! ## The parameters (Spec, `sec:finite`) -/

theorem factorRat_mul_le (x : ℚ) (_hx : 0 < x) : (RationalRateChain.factorRat x : ℚ) * x ≤ 1 := by
  have hs' : 16 * ((RationalRateChain.factorRat x : ℕ) : ℚ) ^ 2 * x ≤ 1 := by
    unfold RationalRateChain.factorRat
    exact Nat.findGreatest_spec (P := fun a : ℕ => 16 * (a : ℚ) ^ 2 * x ≤ 1) (Nat.zero_le _) (by simp)
  rcases Nat.eq_zero_or_pos (RationalRateChain.factorRat x) with h0 | h0
  · rw [h0]; simp
  · have hf : (1 : ℚ) ≤ RationalRateChain.factorRat x := by exact_mod_cast h0
    nlinarith

section Params
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p)
include hadm hs

theorem beta_eq_radius : p.beta = c.radius := hs.beta_eq

theorem radius_pos : 0 < c.radius := hs.beta_pos

theorem inv_radius_le : 1 / c.radius ≤ (c.n : ℚ) ^ B1 := by
  have h1 := hadm.2.2.2.2.2.2.2.1
  have h0 := radius_pos c p hadm hs
  rw [div_le_iff₀ h0]; linarith

theorem T_pos : 1 ≤ p.T := by
  by_contra h0
  have hT : p.T = 0 := by omega
  have hp := hs.T_pass
  rw [hT] at hp
  unfold TPass at hp
  have h16 := hadm.2.2.2.2.2.2.2.2.1
  simp only [header] at hp
  have hJ : 1 ≤ Jmax c.n := by unfold Jmax; omega
  have h1 : (4 : ℚ) ≤ ((4 * Jmax c.n * 2 ^ p.k : ℕ) : ℚ) := by
    have : 4 ≤ 4 * Jmax c.n * 2 ^ p.k := by
      have := Nat.one_le_two_pow (n := p.k); nlinarith
    exact_mod_cast this
  simp at hp
  push_cast at h1
  linarith

theorem h_ge : 64 ≤ p.h := by have := T_pos c p hadm hs; have := hs.height; omega

theorem R0_pos : 1 ≤ p.R0 := by
  rw [hs.R0_eq]; exact Nat.le_sqrt.mpr (by omega)

theorem ell0_nonneg : 0 ≤ p.ell0 := by
  rw [hs.ell0_eq]
  have := radius_pos c p hadm hs
  have := R0_pos c p hadm hs
  simp only [header]
  positivity

theorem ell0_le : p.ell0 ≤ (c.W * p.k : ℕ) * (c.n : ℚ) ^ B1 := by
  rw [hs.ell0_eq]
  simp only [header]
  have hr := radius_pos c p hadm hs
  have hR : (1 : ℚ) ≤ p.R0 := by exact_mod_cast R0_pos c p hadm hs
  have hi := inv_radius_le c p hadm hs
  have hWk : (0 : ℚ) ≤ ((c.W * p.k : ℕ) : ℚ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℚ) ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.1
  have h2 : (1 : ℚ) ≤ c.radius * (c.n : ℚ) ^ B1 * p.R0 := by nlinarith
  calc ((c.W * p.k : ℕ) : ℚ) = ((c.W * p.k : ℕ) : ℚ) * 1 := by ring
    _ ≤ ((c.W * p.k : ℕ) : ℚ) * (c.radius * (c.n : ℚ) ^ B1 * p.R0) := mul_le_mul_of_nonneg_left h2 hWk
    _ = _ := by ring

theorem ellBar_ge : (p.h : ℚ) ^ 2 / (256 * p.T) ≤ ellBar p.ell0 p.h p.T := le_max_right _ _

theorem ellBar_pos : 0 < ellBar p.ell0 p.h p.T := by
  have hT : (1 : ℚ) ≤ p.T := by exact_mod_cast T_pos c p hadm hs
  have hh : (64 : ℚ) ≤ p.h := by exact_mod_cast h_ge c p hadm hs
  exact lt_of_lt_of_le (by positivity) (ellBar_ge c p hadm hs)

theorem M1_pos : 1 ≤ p.M1 := by
  rw [hs.M1_eq]; unfold firstDen
  have := ellBar_pos c p hadm hs
  have hh : (64 : ℚ) ≤ p.h := by exact_mod_cast h_ge c p hadm hs
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))

theorem M1_le : (p.M1 : ℚ) ≤ 4 * p.ell0 + p.h + 1 := by
  rw [hs.M1_eq]; unfold firstDen
  have he := ell0_nonneg c p hadm hs
  have hT : (1 : ℚ) ≤ p.T := by exact_mod_cast T_pos c p hadm hs
  have hh : (64 : ℚ) ≤ p.h := by exact_mod_cast h_ge c p hadm hs
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * ellBar p.ell0 p.h p.T / p.h by
    have := ellBar_pos c p hadm hs; positivity)
  have hb : ellBar p.ell0 p.h p.T ≤ p.ell0 + (p.h : ℚ) ^ 2 / 256 := by
    unfold ellBar
    have : (p.h : ℚ) ^ 2 / (256 * p.T) ≤ (p.h : ℚ) ^ 2 / 256 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have : (0 : ℚ) ≤ (p.h : ℚ) ^ 2 / 256 := by positivity
    exact max_le (by linarith) (by linarith)
  have hx : 4 * ellBar p.ell0 p.h p.T / p.h ≤ 4 * p.ell0 + p.h := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem piStar_le : piStar p.ell0 p.h p.T ≤ 32 := by
  unfold piStar
  have hT : (1 : ℚ) ≤ p.T := by exact_mod_cast T_pos c p hadm hs
  have hh : (64 : ℚ) ≤ p.h := by exact_mod_cast h_ge c p hadm hs
  have hb := ellBar_ge c p hadm hs
  have hp := ellBar_pos c p hadm hs
  rw [div_le_iff₀ (by positivity)]
  have : (p.h : ℚ) ^ 2 ≤ 256 * p.T * ellBar p.ell0 p.h p.T := by
    rw [div_le_iff₀ (by positivity)] at hb; linarith
  nlinarith

/-- `A·x₁ = x_{J−1}` (0-based): the chain factors telescope (lem:chain). -/
theorem prod_ratio (j : ℕ) (hj : j ≤ p.J - 1) :
    ((((List.range j).map fun i => RationalRateChain.factorRat
      (RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i)).prod : ℕ) : ℚ) * firstRatio p.ell0 p.h p.T =
      RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) j := by
  induction j with
  | zero => simp [RationalRateChain.ratio]
  | succ j ih =>
    have hact := active_ratio hs j (by omega)
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Nat.cast_mul]
    rw [show ∀ a b x : ℚ, a * b * x = b * (a * x) from fun a b x => by ring, ih (by omega)]
    simp only [RationalRateChain.ratio, if_pos hact.2]

theorem A_le : (p.A : ℚ) ≤ 32 * p.M1 := by
  have hM := M1_pos c p hadm hs
  have hx := firstRatio_pos hs
  have hA : (p.A : ℚ) = ((((List.range (p.J - 1)).map fun i => RationalRateChain.factorRat
      (RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i)).prod : ℕ) : ℚ) := by
    rw [hs.A_eq, hs.factors_eq]; rfl
  have hinv : 1 / firstRatio p.ell0 p.h p.T ≤ 32 * p.M1 := by
    unfold firstRatio
    have hM' : (1 : ℚ) ≤ p.M1 := by exact_mod_cast hM
    have hp := piStar_le c p hadm hs
    have hpp : 0 < piStar p.ell0 p.h p.T := by
      unfold piStar
      have := ellBar_pos c p hadm hs
      have hT : (1 : ℚ) ≤ p.T := by exact_mod_cast T_pos c p hadm hs
      have hh : (64 : ℚ) ≤ p.h := by exact_mod_cast h_ge c p hadm hs
      positivity
    have hM1 : ((firstDen p.ell0 p.h p.T : ℕ) : ℚ) = p.M1 := by rw [hs.M1_eq]
    have hM0 : (p.M1 : ℚ) ≠ 0 := by positivity
    have e : 1 / ((1 / (p.M1 : ℚ)) / piStar p.ell0 p.h p.T) = p.M1 * piStar p.ell0 p.h p.T := by
      field_simp
    rw [hM1, e]; nlinarith
  rcases Nat.lt_or_ge p.J 2 with hJ | hJ
  · have : p.J - 1 = 0 := by omega
    rw [hA, this]; simp; have : (1 : ℚ) ≤ p.M1 := by exact_mod_cast hM
    linarith
  · have h1 := prod_ratio c p hadm hs (p.J - 1) le_rfl
    have hr : RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) (p.J - 1) ≤ 1 := by
      obtain ⟨j, hj⟩ : ∃ j, p.J - 1 = j + 1 := ⟨p.J - 2, by omega⟩
      rw [hj]
      have hact := active_ratio hs j (by omega)
      simp only [RationalRateChain.ratio, if_pos hact.2]
      exact factorRat_mul_le _ hact.1
    rw [← hA] at h1
    have : (p.A : ℚ) ≤ 1 / firstRatio p.ell0 p.h p.T := by
      rw [le_div_iff₀ hx]; linarith
    linarith

theorem factor_le_A (f : ℕ) (hf : f ∈ p.factors) : f ≤ p.A := by
  have hA := A_pos hs
  rw [hs.A_eq] at hA ⊢
  exact Nat.le_of_dvd hA (List.dvd_prod hf)

/-- `T` is at most `3 + J_max + k + n·B₁` (the least `t` with `4J2^k ≤ 2^t β`, and `β ≥ n^{−B₁}`). -/
theorem T_le : p.T ≤ 3 + Jmax c.n + p.k + c.n * B1 := by
  rcases Nat.eq_zero_or_pos p.T with h0 | h0
  · omega
  have hl := hs.T_least (p.T - 1) (by omega)
  unfold TPass at hl
  simp only [header, not_le] at hl
  have hr := radius_pos c p hadm hs
  have hrn : (1 : ℚ) ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.1
  have h2 : (2 : ℚ) ^ (p.T - 1) < ((4 * Jmax c.n * 2 ^ p.k * c.n ^ B1 : ℕ) : ℚ) := by
    push_cast
    have hnn : (0 : ℚ) ≤ (c.n : ℚ) ^ B1 := by positivity
    have : (2 : ℚ) ^ (p.T - 1) * 1 ≤ 2 ^ (p.T - 1) * (c.radius * (c.n : ℚ) ^ B1) :=
      mul_le_mul_of_nonneg_left hrn (by positivity)
    push_cast at hl
    nlinarith
  have h3 : 2 ^ (p.T - 1) < 4 * Jmax c.n * 2 ^ p.k * c.n ^ B1 := by exact_mod_cast h2
  have h4 : 4 * Jmax c.n * 2 ^ p.k * c.n ^ B1 ≤ 2 ^ (2 + Jmax c.n + p.k + c.n * B1) := by
    have a1 : Jmax c.n ≤ 2 ^ Jmax c.n := Nat.lt_two_pow_self.le
    have a2 : c.n ^ B1 ≤ 2 ^ (c.n * B1) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le B1
    rw [pow_add, pow_add, pow_add]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [← this]
    calc 4 * Jmax c.n * 2 ^ p.k * c.n ^ B1 ≤ 4 * 2 ^ Jmax c.n * 2 ^ p.k * 2 ^ (c.n * B1) := by gcongr
      _ = _ := by ring
  have h5 := lt_of_lt_of_le h3 h4
  have h6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h5
  omega

theorem ell0_eq_divInt : p.ell0 = Rat.divInt ((c.W * p.k * c.radius.den : ℕ) : ℤ) (c.radius.num * p.R0) := by
  have hr := radius_pos c p hadm hs
  have hR : (1 : ℚ) ≤ p.R0 := by exact_mod_cast R0_pos c p hadm hs
  have hnum : (c.radius.num : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_pos.mpr hr).ne'
  have hden : (c.radius.den : ℚ) ≠ 0 := by positivity
  rw [hs.ell0_eq, Rat.divInt_eq_div]
  simp only [header]
  conv_lhs => rw [← Rat.num_div_den c.radius]
  push_cast
  field_simp

theorem ell0_num_bits : natBitLength p.ell0.num.natAbs ≤
    natBitLength c.W + natBitLength p.k + natBitLength c.radius.den := by
  have hr := radius_pos c p hadm hs
  have hb : c.radius.num * (p.R0 : ℤ) ≠ 0 := by
    have := Rat.num_pos.mpr hr
    have := R0_pos c p hadm hs
    positivity
  have hd := Rat.num_dvd ((c.W * p.k * c.radius.den : ℕ) : ℤ) hb
  rw [← ell0_eq_divInt c p hadm hs] at hd
  have h1 := natBitLength_pos c.W
  have h2 := natBitLength_pos p.k
  have h3 := natBitLength_pos c.radius.den
  rcases Nat.eq_zero_or_pos (c.W * p.k * c.radius.den) with h0 | h0
  · have he : p.ell0 = 0 := by rw [ell0_eq_divInt c p hadm hs, h0]; simp
    rw [he]; simp [natBitLength]; omega
  · have hle : p.ell0.num.natAbs ≤ c.W * p.k * c.radius.den :=
      Nat.le_of_dvd h0 (by have h := Int.natAbs_dvd_natAbs.mpr hd; rwa [Int.natAbs_natCast] at h)
    calc natBitLength p.ell0.num.natAbs ≤ natBitLength (c.W * p.k * c.radius.den) := by
          unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right hle) 1
      _ ≤ natBitLength (c.W * p.k) + natBitLength c.radius.den := nbl_mul _ _
      _ ≤ _ := by have := nbl_mul c.W p.k; omega

theorem ell0_den_bits : natBitLength p.ell0.den ≤ natBitLength c.radius.num.natAbs + natBitLength p.R0 := by
  have hr := radius_pos c p hadm hs
  have hd := Rat.den_dvd ((c.W * p.k * c.radius.den : ℕ) : ℤ) (c.radius.num * p.R0)
  rw [← ell0_eq_divInt c p hadm hs] at hd
  have hpos : 0 < c.radius.num.natAbs * p.R0 := by
    have := Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne'
    have := R0_pos c p hadm hs
    positivity
  have hle : p.ell0.den ≤ c.radius.num.natAbs * p.R0 := by
    apply Nat.le_of_dvd hpos
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa [Int.natAbs_mul] using this
  calc natBitLength p.ell0.den ≤ natBitLength (c.radius.num.natAbs * p.R0) := by
        unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right hle) 1
    _ ≤ _ := nbl_mul _ _

theorem Jmax_le : Jmax c.n ≤ c.n + 1 := by
  unfold Jmax Target.mu Target.lambda
  have h1 : Nat.clog 2 c.n ≤ c.n := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h2 : Nat.clog 2 (Nat.clog 2 c.n) ≤ Nat.clog 2 c.n := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  omega

theorem h_le : p.h ≤ 2 * c.n ^ 2 := by
  have h1 : p.h ≤ 2 * p.hE ^ 2 := by rw [hs.h_eq]; exact Nat.sqrt_le_self _
  have h2 : p.hE ≤ c.n := by rw [hs.hE_eq]; have := P_le_n c p hs; omega
  have : p.hE ^ 2 ≤ c.n ^ 2 := Nat.pow_le_pow_left h2 2
  omega

theorem M1_le_nat : p.M1 ≤ 4 * (c.W * p.k * c.n ^ B1) + 2 * c.n ^ 2 + 1 := by
  have h1 := M1_le c p hadm hs
  have h2 := ell0_le c p hadm hs
  have h3 : (p.h : ℚ) ≤ 2 * (c.n : ℚ) ^ 2 := by exact_mod_cast h_le c p hadm hs
  have : (p.M1 : ℚ) ≤ ((4 * (c.W * p.k * c.n ^ B1) + 2 * c.n ^ 2 + 1 : ℕ) : ℚ) := by
    push_cast at h2 ⊢; linarith
  exact_mod_cast this

theorem A_le_nat : p.A ≤ 32 * p.M1 := by
  have := A_le c p hadm hs; exact_mod_cast this

theorem Lambda_le : p.Lambda ≤ p.Lw * p.A + 1 := by
  rw [hs.Lambda_eq]
  have : (p.Lw - 1) * p.A ≤ p.Lw * p.A := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have := Nat.div_le_self ((p.Lw - 1) * p.A) 2
  omega

end Params

section Circ
variable {n : ℕ}

theorem mem_intN {z : ℤ} {x : ℕ} (h : x ∈ intN z) : x ≤ 1 ∨ x = z.natAbs := by
  simp only [intN, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · left; split_ifs <;> omega
  · right; rfl

theorem gateN_len (g : NormalizedThresholdGate n) : (gateN g).length ≤ 2 * n + 3 := by
  have h := flatMap_len_le (List.ofFn g.weight) intN 2 (fun _ _ => by simp [intN])
  simp only [List.length_ofFn] at h
  simp only [gateN, List.length_append, List.length_singleton]
  have : (intN g.threshold).length = 2 := by simp [intN]
  omega

theorem circ_len (C : NCircuit n) (hwf : C.WellFormed (Call.B0 n)) :
    (circN C).length ≤ 4 + C.topWeight * (2 * n + 7) := by
  obtain ⟨hlen, hnz, htab, _⟩ := hwf
  have hG : C.coeffs.length ≤ C.topWeight := length_le_sum_natAbs _ hnz
  have h1 := flatMap_len_le C.gates gateN (2 * n + 3) (fun g _ => gateN_len g)
  have h2 := flatMap_len_le C.coeffs intN 2 (fun a _ => by simp [intN])
  simp only [circN, List.length_append, List.length_singleton, List.length_map]
  rw [htab]
  rw [hlen] at h1
  have : C.coeffs.length * (2 * n + 3) ≤ C.topWeight * (2 * n + 3) := Nat.mul_le_mul_right _ hG
  nlinarith

theorem circ_bits (C : NCircuit n) (hwf : C.WellFormed (Call.B0 n)) :
    ∀ x ∈ circN C, natBitLength x ≤ Call.B0 n + 2 * C.topWeight + n + 3 := by
  obtain ⟨hlen, hnz, htab, hgw⟩ := hwf
  have hG : C.coeffs.length ≤ C.topWeight := length_le_sum_natAbs _ hnz
  have hbig : ∀ z : ℤ, z.natAbs < 2 ^ Call.B0 n → natBitLength z.natAbs ≤ Call.B0 n + 1 := fun z hz =>
    nbl_le_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega))) (by omega)
  intro x hx
  simp only [circN, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_map] at hx
  rcases hx with ((((hx | ⟨g, hg, hx⟩) | hx) | ⟨a, ha, hx⟩) | hx) | ⟨b, _, hx⟩
  · have := nbl_le_of_le (show x ≤ C.topWeight by omega); omega
  · have hgw' := hgw g hg
    simp only [gateN, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_ofFn] at hx
    rcases hx with (hx | ⟨w, ⟨i, rfl⟩, hx⟩) | hx
    · have := nbl_le_self x; omega
    · rcases mem_intN hx with h1 | h1
      · have := nbl_le_of_le h1; omega
      · subst h1; have := hbig _ (hgw'.1 i); omega
    · rcases mem_intN hx with h1 | h1
      · have := nbl_le_of_le h1; omega
      · subst h1; have := hbig _ hgw'.2; omega
  · have := nbl_le_of_le (show x ≤ C.topWeight by omega); omega
  · rcases mem_intN hx with h1 | h1
    · have := nbl_le_of_le h1; omega
    · subst h1; have := nbl_le_of_le (natAbs_le_sum C.coeffs a ha); unfold NCircuit.topWeight; omega
  · have := nbl_le_of_le (show x ≤ 2 * C.topWeight + 1 by omega); omega
  · subst hx; have := nbl_le_of_le (show bitN b ≤ 1 by unfold bitN; split_ifs <;> omega); omega

theorem B0_le (n : ℕ) : Call.B0 n ≤ 4 * n * (n + 1) := by
  unfold Call.B0
  exact Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)

end Circ

/-! ## Assembly -/

section Assembly
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (hadm : c.Admitted B1 B2) (hs : Spec cT (header c) p)

theorem pw_le {N a b : ℕ} (hN : 1 ≤ N) (h : a ≤ b) : N ^ a ≤ N ^ b := Nat.pow_le_pow_right hN h

include hadm in

theorem call_bits : ∀ x ∈ callN c, natBitLength x ≤
    4 * (c.n + 1) ^ 2 + 4 * (c.n + 1) ^ 4 + 2 * (c.n + 1) + 4 + (c.n + 1) ^ B2 := by
  obtain ⟨h4, hf, hsec, _, _, hpar, hW, _, _, hrad, hplen⟩ := hadm
  have hB0 := B0_le c.n
  have htw1 : c.first.topWeight ≤ 2 * c.n ^ 4 := by unfold Call.W at hW; omega
  have htw2 : c.second.topWeight ≤ 2 * c.n ^ 4 := by unfold Call.W at hW; omega
  have hn4 : c.n ^ 4 ≤ (c.n + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hn2 : 4 * c.n * (c.n + 1) ≤ 4 * (c.n + 1) ^ 2 := by nlinarith
  have hnB : c.n ^ B2 ≤ (c.n + 1) ^ B2 := Nat.pow_le_pow_left (by omega) B2
  have hr := ratWord_bits c.radius
  intro x hx
  simp only [callN, ratN, intN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (((((rfl | rfl) | hx) | hx) | rfl) | hx) | ((rfl | rfl) | rfl)
  · have := nbl_le_self c.n; omega
  · have := nbl_le_of_le (show kindTag c.kind ≤ 2 by cases c.kind <;> decide); omega
  · have := circ_bits c.first hf x hx; omega
  · have := circ_bits c.second hsec x hx; omega
  · have := nbl_le_of_le hplen; omega
  · have := nbl_le_of_le (hpar x hx).le; omega
  · have := nbl_le_of_le (show (if c.radius.num < 0 then 1 else 0) ≤ 1 by split_ifs <;> omega); omega
  · omega
  · omega

include hadm in
theorem call_len : (callN c).length ≤ 14 + (c.n + 1) + 4 * (c.n + 1) ^ 4 * (2 * (c.n + 1) + 7) := by
  obtain ⟨h4, hf, hsec, _, _, hpar, hW, _, _, hrad, hplen⟩ := hadm
  have h1 := circ_len c.first hf
  have h2 := circ_len c.second hsec
  have htw : c.first.topWeight + c.second.topWeight ≤ 2 * c.n ^ 4 := hW
  have hn4 : c.n ^ 4 ≤ (c.n + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  simp only [callN, ratN, intN, List.length_append, List.length_cons, List.length_nil]
  have : (c.first.topWeight + c.second.topWeight) * (2 * c.n + 7) ≤ 2 * (c.n + 1) ^ 4 * (2 * (c.n + 1) + 7) := by
    have := Nat.mul_le_mul htw (show 2 * c.n + 7 ≤ 2 * (c.n + 1) + 7 by omega)
    nlinarith
  nlinarith

include hadm hs in

theorem params_bits : ∀ x ∈ paramsN p, natBitLength x ≤ 2 ^ 10 * (c.n + 1) ^ (B1 + B2 + 8) := by
  set N := c.n + 1 with hN
  have hN5 : 5 ≤ N := by have := hadm.1; omega
  have hN1 : 1 ≤ N := by omega
  set Q := N ^ (B1 + B2 + 8) with hQ
  set Vb := 2 ^ 9 * N ^ (B1 + 7) with hVb
  have hVQ : Vb + 1 ≤ 2 ^ 10 * Q := by
    have := pw_le hN1 (show B1 + 7 ≤ B1 + B2 + 8 by omega)
    have : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
    omega
  have hval : ∀ x, x ≤ Vb → natBitLength x ≤ 2 ^ 10 * Q := fun x h => (nbl_le_of_le h).trans hVQ
  -- basic powers
  have q1 : N ≤ N ^ (B1 + 7) := by simpa using pw_le hN1 (show 1 ≤ B1 + 7 by omega)
  have q2 : N ^ 2 ≤ N ^ (B1 + 7) := pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ N ^ (B1 + 7) := pw_le hN1 (by omega)
  have hn : c.n ≤ N := by omega
  have hn2 : c.n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn 2
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hn 4
  have hW := hadm.2.2.2.2.2.2.1
  have hk := k_le_n c p hs
  have hP := P_le_n c p hs
  have hJ := Jmax_le c p hadm hs
  have hJJ := J_le_Jmax c p hs
  -- the big values
  have hWk : c.W * p.k * c.n ^ B1 ≤ 2 * N ^ (B1 + 5) := by
    have a1 : c.W ≤ 2 * N ^ 4 := by omega
    have a2 : p.k ≤ N := by omega
    have a3 : c.n ^ B1 ≤ N ^ B1 := Nat.pow_le_pow_left hn B1
    calc c.W * p.k * c.n ^ B1 ≤ (2 * N ^ 4) * N * N ^ B1 := by gcongr
      _ = 2 * N ^ (B1 + 5) := by ring
  have hM1 : p.M1 ≤ 11 * N ^ (B1 + 5) := by
    have := M1_le_nat c p hadm hs
    have : N ^ 2 ≤ N ^ (B1 + 5) := pw_le hN1 (by omega)
    have : 1 ≤ N ^ (B1 + 5) := Nat.one_le_pow _ _ (by omega)
    omega
  have hA : p.A ≤ 352 * N ^ (B1 + 5) := by have := A_le_nat c p hadm hs; omega
  have hLw : p.Lw ≤ N ^ 2 := by
    have := Lw_le c p hs
    have : p.P ^ 2 ≤ c.n ^ 2 := Nat.pow_le_pow_left hP 2
    nlinarith
  have hLam : p.Lambda ≤ Vb := by
    have h1 := Lambda_le c p hadm hs
    have h2 : p.Lw * p.A ≤ N ^ 2 * (352 * N ^ (B1 + 5)) := Nat.mul_le_mul hLw hA
    have h3 : N ^ 2 * (352 * N ^ (B1 + 5)) = 352 * N ^ (B1 + 7) := by ring
    omega
  have hAV : p.A ≤ Vb := by
    have : N ^ (B1 + 5) ≤ N ^ (B1 + 7) := pw_le hN1 (by omega)
    omega
  have hM1V : p.M1 ≤ Vb := by
    have : N ^ (B1 + 5) ≤ N ^ (B1 + 7) := pw_le hN1 (by omega)
    omega
  have hTV : p.T ≤ Vb := by
    have h1 := T_le c p hadm hs
    have h2 : B1 ≤ N ^ B1 := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) B1)
    have h3 : c.n * B1 ≤ N ^ (B1 + 7) := by
      calc c.n * B1 ≤ N * N ^ B1 := Nat.mul_le_mul hn h2
        _ = N ^ (B1 + 1) := by ring
        _ ≤ _ := pw_le hN1 (by omega)
    omega
  -- bits of the rationals
  have hB2 : c.n ^ B2 ≤ N ^ B2 := Nat.pow_le_pow_left hn B2
  have hQ2 : N ^ B2 ≤ Q := pw_le hN1 (by omega)
  have hQ4 : N ^ 4 ≤ Q := pw_le hN1 (by omega)
  have hQ1 : N ≤ Q := by simpa using pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have hrad := hadm.2.2.2.2.2.2.2.2.2.1
  have hrb := ratWord_bits c.radius
  have hbits : ∀ x, natBitLength x ≤ N ^ B2 + 2 * N ^ 4 + 2 * N + 4 → natBitLength x ≤ 2 ^ 10 * Q := by
    intro x h; omega
  have hbeta : p.beta = c.radius := hs.beta_eq
  have he0 := ell0_num_bits c p hadm hs
  have he1 := ell0_den_bits c p hadm hs
  have hR0 : p.R0 ≤ N := by rw [hs.R0_eq]; simp only [header]; have := Nat.sqrt_le_self (c.n - p.k + 1); omega
  have hWb : natBitLength c.W ≤ 2 * N ^ 4 + 1 := (nbl_le_self _).trans (by omega)
  have hkb : natBitLength p.k ≤ N := (nbl_le_self _).trans (by omega)
  have hRb : natBitLength p.R0 ≤ N + 1 := (nbl_le_self _).trans (by omega)
  intro x hx
  simp only [paramsN, ratN, intN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((((((((rfl | rfl | rfl) | ((rfl | rfl) | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | hx) |
    (rfl | rfl | rfl | rfl | rfl | rfl)) | ((rfl | rfl) | rfl)) | (rfl | rfl | rfl)) | hx) | (rfl | rfl)
  · apply hval; rw [hs.n_eq]; simp only [header]; omega
  · apply hval; unfold bitN; split_ifs <;> omega
  · apply hval; rw [hs.W_eq]; simp only [header]; omega
  · apply hval; split_ifs <;> omega
  · apply hbits; rw [hbeta]; omega
  · apply hbits; rw [hbeta]; omega
  · apply hval; omega
  · exact hval _ hTV
  · apply hval; rw [hs.m_eq]; simp only [header]; unfold outer; omega
  · apply hval; rw [hs.Dmax_eq]; unfold greatestDegree
    have := Nat.findGreatest_le (P := DegreePass (header c).n p.k p.m) p.m
    have hm : p.m ≤ c.n + 1 := by rw [hs.m_eq]; simp only [header]; unfold outer; omega
    omega
  · apply hval; omega
  · apply hval
    have := (leastUpTo_spec _ _ _ hs.e_eq).2.1; omega
  · apply hval; rw [Finset.length_sort]; have := primes_card_le c p hs; omega
  · apply hval; rw [Finset.mem_sort] at hx; have := primes_le hs x hx; omega
  · apply hval; have := window_le c p hs; have : p.P ^ 2 ≤ c.n ^ 2 := Nat.pow_le_pow_left hP 2; omega
  · apply hval; rw [hs.L2_eq]
    have := window_le c p hs; have : p.P ^ 2 ≤ c.n ^ 2 := Nat.pow_le_pow_left hP 2
    rcases NearCubicGates.Close.Counter.pairSide_le_window p.window with h | h <;> omega
  · apply hval; omega
  · apply hval; rw [hs.hE_eq]; omega
  · apply hval; have := h_le c p hadm hs; omega
  · apply hval; omega
  · apply hval; split_ifs <;> omega
  · apply hbits; omega
  · apply hbits
    have : natBitLength c.radius.num.natAbs ≤ N ^ B2 := by omega
    omega
  · exact hval _ hM1V
  · apply hval; omega
  · apply hval; rw [factors_length hs]; omega
  · apply hval; have := factor_le_A c p hadm hs x hx; omega
  · exact hval _ hAV
  · exact hval _ hLam

include hadm hs in
theorem params_len : (paramsN p).length ≤ 29 + 2 * (c.n + 1) := by
  have h1 := primes_card_le c p hs
  have h2 := P_le_n c p hs
  have h3 := factors_length hs
  have h4 := J_le_Jmax c p hs
  have h5 := Jmax_le c p hadm hs
  simp only [paramsN, ratN, intN, List.length_append, List.length_cons, List.length_nil, Finset.length_sort]
  omega

theorem circ_wf (hadm : c.Admitted B1 B2) (r : ℕ) : (circ c r).WellFormed (Call.B0 c.n) := by
  unfold circ; split_ifs
  · exact hadm.2.1
  · exact hadm.2.2.1

theorem coords_len {n : ℕ} (I : Finset (Fin n)) : (coordsOf I).length ≤ n := by
  unfold coordsOf; rw [List.length_map, Finset.length_sort]
  exact (Finset.card_le_univ I).trans (by simp)

theorem coords_lt {n : ℕ} (I : Finset (Fin n)) (x : ℕ) (hx : x ∈ coordsOf I) : x < n := by
  unfold coordsOf at hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact i.isLt

theorem mem_srList {sr : ℕ × ℕ} (h : sr ∈ srList c p) : sr.1 < p.J ∧ sr.2 < roleCount c.kind := by
  unfold srList at h
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨s, hs', r, hr, rfl⟩ := h
  exact ⟨hs', hr⟩

theorem srList_length : (srList c p).length ≤ p.J * 2 := by
  unfold srList
  have := flatMap_len_le (List.range p.J) (fun s => (List.range (roleCount c.kind)).map fun r => (s, r)) 2
    (fun _ _ => by simp; exact roleCount_le_two c)
  simpa using this

/-- The coefficient list of a valid stage and role: at most `W` entries, each of absolute value at most `W`. -/
theorem coef_bounds (hadm : c.Admitted B1 B2) (wt : Wit c.n) (w : List Bool) (hw : decodeWitness c p w = some wt)
    (s r : ℕ) (hs' : s < p.J) (hr : r < roleCount c.kind) :
    (wt.coef s r).length ≤ c.W ∧ ∀ a ∈ wt.coef s r, a.natAbs ≤ c.W := by
  obtain ⟨vs, hvs, hb⟩ := coef_shape c p wt w hw s r hs' hr
  obtain ⟨hlen, hnz, _, _⟩ := circ_wf c hadm r
  have htw := topWeight_le_W c r
  have hG : (circ c r).coeffs.length ≤ (circ c r).topWeight := length_le_sum_natAbs _ hnz
  rw [hvs]
  refine ⟨?_, ?_⟩
  · simp only [List.length_map, List.length_zip]; omega
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨av, hav, rfl⟩ := ha
    have h1 := coefOf_abs av.1 av.2 (hb av hav)
    have h2 := natAbs_le_sum (circ c r).coeffs av.1 (List.of_mem_zip hav).1
    unfold NCircuit.topWeight at htw
    omega

include hadm hs in
theorem wit_bits (wt : Wit c.n) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    ∀ x ∈ witN c p wt, natBitLength x ≤ c.n + c.W + 1 := by
  intro x hx
  simp only [witN, List.mem_append, List.mem_singleton, List.mem_flatMap] at hx
  rcases hx with (rfl | hx) | ⟨sr, hsr, hx | hx⟩
  · apply nbl_le_of_le; have := coords_len wt.I; omega
  · apply nbl_le_of_le; have := coords_lt wt.I x hx; omega
  · have hv := mem_srList c p hsr
    have hb := coef_bounds c p hadm wt w hw sr.1 sr.2 hv.1 hv.2
    subst hx
    exact nbl_le_of_le (by omega)
  · have hv := mem_srList c p hsr
    have hb := coef_bounds c p hadm wt w hw sr.1 sr.2 hv.1 hv.2
    obtain ⟨a, ha, hx⟩ := hx
    have h4 := hadm.1
    rcases mem_intN hx with h1 | h1
    · exact nbl_le_of_le (by omega)
    · subst h1; exact nbl_le_of_le (by have := hb.2 a ha; omega)

include hadm hs in
theorem wit_len (wt : Wit c.n) (w : List Bool) (hw : decodeWitness c p w = some wt) :
    (witN c p wt).length ≤ 1 + c.n + p.J * 2 * (1 + 2 * c.W) := by
  have h1 : (coordsOf wt.I).length ≤ c.n := coords_len wt.I
  have h2 := flatMap_len_le (srList c p) (fun sr => [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN)
    (1 + 2 * c.W) (fun sr hsr => by
      have hv := mem_srList c p hsr
      have hb := coef_bounds c p hadm wt w hw sr.1 sr.2 hv.1 hv.2
      have := flatMap_len_le (wt.coef sr.1 sr.2) intN 2 (fun _ _ => by simp [intN])
      simp only [List.length_append, List.length_singleton]; omega)
  have h3 := srList_length c p
  have h4 : (srList c p).length * (1 + 2 * c.W) ≤ p.J * 2 * (1 + 2 * c.W) := Nat.mul_le_mul_right _ h3
  simp only [witN, List.length_append, List.length_singleton]
  omega

end Assembly

/-- **The cell input has polynomial length** (`sec:algorithm`: "The entire encoding has polynomial length"). -/
theorem cellInput_length_le (B1 B2 cT : ℕ) :
    ∃ C e : ℕ, ∀ r : CellReq B1 B2 cT, (cellInput r).length ≤ C * (r.c.n + 1) ^ e := by
  refine ⟨2 ^ 19, B1 + B2 + 13, fun r => ?_⟩
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  set c := r.c
  set N := c.n + 1 with hN
  have hN5 : 5 ≤ N := by have := hadm.1; omega
  have hN1 : 1 ≤ N := by omega
  set Q := N ^ (B1 + B2 + 8) with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have q1 : N ≤ Q := by simpa using pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have q2 : N ^ 2 ≤ Q := pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ Q := pw_le hN1 (by omega)
  have qB : N ^ B2 ≤ Q := pw_le hN1 (by omega)
  have hW := hadm.2.2.2.2.2.2.1
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hbits : ∀ x ∈ cellN c r.p r.wt, natBitLength x ≤ 2 ^ 10 * Q := by
    intro x hx
    simp only [cellN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · have := call_bits c hadm x hx; rw [← hN] at this; omega
    · have := params_bits c r.p hadm hs x hx; rw [← hN] at this; omega
    · have := wit_bits c r.p hadm hs r.wt w hw x hx; omega
  have hlen : (cellN c r.p r.wt).length ≤ 70 * N ^ 5 := by
    have h1 := call_len c hadm
    have h2 := params_len c r.p hadm hs
    have h3 := wit_len c r.p hadm hs r.wt w hw
    have hJ := (J_le_Jmax c r.p hs).trans (Jmax_le c r.p hadm hs)
    have e1 : (2 * c.W) ≤ 4 * N ^ 4 := by omega
    have e2 : r.p.J * 2 * (1 + 2 * c.W) ≤ 2 * N * (1 + 4 * N ^ 4) := by
      have := Nat.mul_le_mul (show r.p.J * 2 ≤ 2 * N by omega) (show 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 by omega)
      exact this
    rw [← hN] at h1 h2
    have e3 : N ^ 5 = N * N ^ 4 := by ring
    have e4 : 5 * N ^ 4 ≤ N ^ 5 := by rw [e3]; exact Nat.mul_le_mul_right _ hN5
    have e5 : N ≤ N ^ 4 := by simpa using pw_le hN1 (show 1 ≤ 4 by omega)
    have e6 : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
    have e7 : 2 * N * (1 + 4 * N ^ 4) = 2 * N + 8 * N ^ 5 := by ring
    simp only [cellN, List.length_append]
    omega
  have hcell : cellInput r = (cellN c r.p r.wt).flatMap natWord := by
    rw [cellN_word]; rfl
  rw [hcell]
  have h := flat_len_le _ _ hbits
  have h5 : N ^ 5 * Q = N ^ (B1 + B2 + 13) := by rw [hQ, ← pow_add]; ring_nf
  calc _ ≤ (cellN c r.p r.wt).length * (2 * (2 ^ 10 * Q) + 1) := h
    _ ≤ 70 * N ^ 5 * (2 ^ 12 * Q) := Nat.mul_le_mul hlen (by omega)
    _ ≤ 2 ^ 19 * N ^ (B1 + B2 + 13) := by rw [← h5]; nlinarith

end NearCubicGates.Close.Cells
