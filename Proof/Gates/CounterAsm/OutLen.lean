import Proof.Gates.Counter.OutOK
import Proof.Gates.Interfaces.CounterFormats
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-! ## Dyadic rationals -/

theorem nbl_le_of_lt' {v k : ℕ} (h : v < 2 ^ k) (hk : 1 ≤ k) : natBitLength v ≤ k := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem natWord_len' (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 :=
  NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length v

theorem dyadic_num_den (a m : ℕ) :
    ((a : ℚ) / 2 ^ m).num.natAbs ≤ a ∧ ((a : ℚ) / 2 ^ m).den ≤ 2 ^ m := by
  have hb : ((2 ^ m : ℕ) : ℤ) ≠ 0 := by positivity
  have hq : ((a : ℚ) / 2 ^ m) = Rat.divInt (a : ℤ) ((2 ^ m : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]; push_cast; rfl
  rw [hq]
  constructor
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h := Rat.num_dvd (a : ℤ) hb
      have h2 := Int.natAbs_dvd_natAbs.mpr h
      simp only [Int.natAbs_natCast] at h2
      exact Nat.le_of_dvd ha h2
  · have h := Rat.den_dvd (a : ℤ) ((2 ^ m : ℕ) : ℤ)
    have h2 : (Rat.divInt (a : ℤ) ((2 ^ m : ℕ) : ℤ)).den ∣ 2 ^ m := by exact_mod_cast h
    exact Nat.le_of_dvd (by positivity) h2

/-- A dyadic `a / 2^m` with `a ≤ 2^m` prints in at most `4m + 9` cells. -/
theorem ratWord_len_le (a m : ℕ) (h : a ≤ 2 ^ m) : (ratWord ((a : ℚ) / 2 ^ m)).length ≤ 4 * m + 9 := by
  obtain ⟨hn, hd⟩ := dyadic_num_den a m
  have hpos : 0 < 2 ^ m := by positivity
  have hlt : ∀ v, v ≤ 2 ^ m → v < 2 ^ (m + 1) := fun v hv => by rw [pow_succ]; omega
  have b1 := nbl_le_of_lt' (hlt _ (hn.trans h)) (by omega)
  have b2 := nbl_le_of_lt' (hlt _ hd) (by omega)
  have b0 : ∀ z : ℤ, natBitLength (if z < 0 then 1 else 0) ≤ 1 := fun z =>
    nbl_le_of_lt' (k := 1) (by split_ifs <;> norm_num) le_rfl
  simp only [ratWord, Interfaces.intWord, List.length_append, natWord_len']
  have := b0 ((a : ℚ) / 2 ^ m).num
  omega

theorem half_eq : (1 / 2 : ℚ) = ((1 : ℕ) : ℚ) / 2 ^ 1 := by norm_num
theorem one_eq : (1 : ℚ) = ((1 : ℕ) : ℚ) / 2 ^ 0 := by norm_num
theorem zero_eq : (0 : ℚ) = ((0 : ℕ) : ℚ) / 2 ^ 0 := by norm_num

theorem len_half : (ratWord (1 / 2 : ℚ)).length ≤ 13 := by rw [half_eq]; exact ratWord_len_le 1 1 (by norm_num)
theorem len_one : (ratWord (1 : ℚ)).length ≤ 9 := by rw [one_eq]; exact ratWord_len_le 1 0 (by norm_num)
theorem len_zero : (ratWord (0 : ℚ)).length ≤ 9 := by rw [zero_eq]; exact ratWord_len_le 0 0 (by norm_num)

/-! ## eq:output's endpoints -/

open Classical in
/-- `Σ_certain N_y` is a natural `S`, and `S + 2^{k−1}·N_unc ≤ 2^k·#cells`. -/
theorem certainSum_nat (c : Call) (p : Params) (wt : Wit c.n) :
    ∃ S : ℕ, certainSum c p wt = S ∧
      S + 2 ^ (p.k - 1) * uncCount c p wt ≤ 2 ^ p.k * Fintype.card (Cells wt.I) := by
  set A := (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y) with hA
  refine ⟨∑ y ∈ A, (cellCount c p wt y).num.toNat, ?_, ?_⟩
  · unfold certainSum
    push_cast
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨_, _, hden, h0, _⟩ := (Finset.mem_filter.mp hy).2
    have hnn : (0 : ℤ) ≤ (cellCount c p wt y).num := Rat.num_nonneg.mpr h0
    have e1 : (((cellCount c p wt y).num.toNat : ℕ) : ℚ) = (((cellCount c p wt y).num.toNat : ℤ) : ℚ) := by
      push_cast; rfl
    rw [e1, Int.toNat_of_nonneg hnn]
    exact (Rat.coe_int_num_of_den_eq_one hden).symm
  · have hterm : ∀ y ∈ A, (cellCount c p wt y).num.toNat ≤ 2 ^ p.k := by
      intro y hy
      obtain ⟨_, _, hden, h0, hle⟩ := (Finset.mem_filter.mp hy).2
      have hq : ((cellCount c p wt y).num : ℚ) = cellCount c p wt y := Rat.coe_int_num_of_den_eq_one hden
      have hz : (cellCount c p wt y).num ≤ ((2 ^ p.k : ℕ) : ℤ) := by
        have : ((cellCount c p wt y).num : ℚ) ≤ (((2 ^ p.k : ℕ) : ℤ) : ℚ) := by rw [hq]; push_cast; exact hle
        exact_mod_cast this
      exact Int.toNat_le.mpr hz
    have hS : ∑ y ∈ A, (cellCount c p wt y).num.toNat ≤ A.card * 2 ^ p.k := by
      have := Finset.sum_le_card_nsmul A (fun y => (cellCount c p wt y).num.toNat) (2 ^ p.k) hterm
      simpa using this
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Cells wt.I)))
      (fun y => Certain c p wt y)
    have hU : 2 ^ (p.k - 1) * uncCount c p wt ≤ 2 ^ p.k * uncCount c p wt :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
    have hunc : uncCount c p wt = ((Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ Certain c p wt y).card :=
      rfl
    rw [Finset.card_univ] at hcard
    rw [← hA] at hcard
    calc ∑ y ∈ A, (cellCount c p wt y).num.toNat + 2 ^ (p.k - 1) * uncCount c p wt
        ≤ A.card * 2 ^ p.k + 2 ^ p.k * uncCount c p wt := Nat.add_le_add hS hU
      _ = 2 ^ p.k * (A.card + uncCount c p wt) := by ring
      _ = 2 ^ p.k * Fintype.card (Cells wt.I) := by rw [hunc, hcard]

/-- The cells of a `k`-subset number `2^{n−k}`. -/
theorem card_cells {n : ℕ} (I : Finset (Fin n)) : Fintype.card (Cells I) = 2 ^ (n - I.card) := by
  simp only [Cells, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe]

theorem outputOf_len (c : Call) (p : Params) (wt : Wit c.n) (hk : wt.I.card = p.k) (hkn : p.k ≤ c.n) :
    (outputWord (outputOf c p wt)).length ≤ 8 * c.n + 18 := by
  obtain ⟨S, hS, hle⟩ := certainSum_nat c p wt
  rw [card_cells, hk, ← pow_add, Nat.add_sub_cancel' hkn] at hle
  have e : outputOf c p wt = (((S + 2 ^ (p.k - 1) * uncCount c p wt : ℕ) : ℚ) / 2 ^ c.n,
      ((2 ^ (p.k - 1) * uncCount c p wt : ℕ) : ℚ) / 2 ^ c.n) := by
    rw [outputOf_eq, hS]; push_cast; rfl
  rw [e]
  simp only [outputWord, List.length_append]
  have h1 := ratWord_len_le (S + 2 ^ (p.k - 1) * uncCount c p wt) c.n hle
  have h2 := ratWord_len_le (2 ^ (p.k - 1) * uncCount c p wt) c.n (by omega)
  omega

theorem pair_len_le (o : ℚ × ℚ) (h1 : (ratWord o.1).length ≤ 13) (h2 : (ratWord o.2).length ≤ 13) :
    (outputWord o).length ≤ 26 := by
  simp only [outputWord, List.length_append]; omega

theorem zeroWeight_len (c : Call) : (outputWord (zeroWeightValue c)).length ≤ 26 := by
  have l1 : ∀ b : Bool, (ratWord (if b then (1 : ℚ) else 0)).length ≤ 13 := fun b => by
    cases b
    · simp only [Bool.false_eq_true, if_false]; have := len_zero; omega
    · simp only [if_true]; have := len_one; omega
  have l2 : (ratWord (0 : ℚ)).length ≤ 13 := by have := len_zero; omega
  unfold zeroWeightValue
  split
  · exact pair_len_le _ (l1 _) l2
  · exact pair_len_le _ (l1 _) l2
  · split
    · exact pair_len_le _ (l1 _) l2
    · exact pair_len_le _ len_half l2

/-- **The printed interval of `counterOnCall` has at most `8n + 30` cells.** -/
theorem counterOnCall_outLen (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    (outputWord (counterOnCall B1 B2 cT c w)).length ≤ 8 * c.n + 30 := by
  have hdef : (outputWord defaultValue).length ≤ 26 := pair_len_le _ len_half len_half
  unfold counterOnCall
  split_ifs with hadm hW
  · have := zeroWeight_len c; omega
  · split
    · omega
    · rename_i p hp
      split
      · omega
      · rename_i wt hw
        have hs := selectParams_spec cT (header c) p hp
        have hkn : p.k ≤ c.n := hs.k_lt.le
        have := outputOf_len c p wt (decodeWitness_card c p w wt hw) hkn
        omega
  · omega

theorem counterOfMachine_outOK
    (hR : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hB : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (hP : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 B2 cT : ℕ) (hB1 : 0 < B1) (hcT : 0 < cT)
    (budget : Call → List Bool → ℕ)
    (program : WordFunction (Call × List Bool) (fun r => RepairOrdinary.frame (callWord r.1) ++
      RepairOrdinary.frame r.2) (fun r => outputWord (counterOnCall B1 B2 cT r.1 r.2)) (fun r => budget r.1 r.2))
    (fast : ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 → ∀ w : List Bool,
      budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n)
    (rest : ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ c.Admitted B1 B2 →
      budget c w ≤ K * ((callWord c).length + 1) ^ e) :
    OutOK (counterOfMachine hR hB hP B1 B2 cT hB1 hcT budget program fast rest) :=
  ⟨30, 1, fun c w => by
    have := counterOnCall_outLen B1 B2 cT c w
    show (outputWord (counterOnCall B1 B2 cT c w)).length ≤ 30 * (c.n + 1) ^ 1
    rw [pow_one]; omega⟩

end NearCubicGates.Close.CounterAsm
