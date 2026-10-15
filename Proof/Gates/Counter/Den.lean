import Proof.Gates.Counter.Main

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires NearCubicWires.RepairOrdinary

/-- The counter's endpoints are integers over `2^{n+1}`. -/
def DenOK {B1 B2 : ℕ} (ctr : Counter B1 B2) : Prop :=
  ∀ (c : Call) (w : List Bool),
    ((ctr.value c w).1 * 2 ^ (c.n + 1)).den = 1 ∧ ((ctr.value c w).2 * 2 ^ (c.n + 1)).den = 1

theorem den_of_eq (q : ℚ) (m : ℕ) (z : ℤ) (h : q * 2 ^ m = z) : (q * 2 ^ m).den = 1 := by rw [h]; rfl

theorem half_den (n : ℕ) : ((1 / 2 : ℚ) * 2 ^ (n + 1)).den = 1 :=
  den_of_eq _ _ (2 ^ n) (by rw [pow_succ]; push_cast; ring)

theorem int_den (z : ℤ) (n : ℕ) : ((z : ℚ) * 2 ^ (n + 1)).den = 1 :=
  den_of_eq _ _ (z * 2 ^ (n + 1)) (by push_cast; ring)

open Classical in
theorem outputOf_den (c : Call) (p : Params) (wt : Wit c.n) :
    ((outputOf c p wt).1 * 2 ^ (c.n + 1)).den = 1 ∧ ((outputOf c p wt).2 * 2 ^ (c.n + 1)).den = 1 := by
  simp only [outputOf]
  have hint : ∃ z : ℤ, ∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
      cellCount c p wt y = z := by
    have hz : ∀ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
        (cellCount c p wt y : ℚ) = ((cellCount c p wt y).num : ℚ) := by
      intro y hy
      have hden := (Finset.mem_filter.mp hy).2.2.2.1
      exact (Rat.coe_int_num_of_den_eq_one hden).symm
    refine ⟨∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
      (cellCount c p wt y).num, ?_⟩
    rw [Finset.sum_congr rfl hz]
    push_cast
    rfl
  obtain ⟨z, hz⟩ := hint
  constructor
  · refine den_of_eq _ _ (2 * (z + 2 ^ (p.k - 1) *
      ((Finset.univ.filter fun y => ¬ Certain c p wt y).card : ℤ))) ?_
    rw [hz]
    push_cast
    rw [pow_succ]
    field_simp
  · refine den_of_eq _ _ (2 * (2 ^ (p.k - 1) * ((Finset.univ.filter fun y => ¬ Certain c p wt y).card : ℤ))) ?_
    push_cast
    rw [pow_succ]
    field_simp

theorem zeroWeightValue_den (c : Call) :
    ((zeroWeightValue c).1 * 2 ^ (c.n + 1)).den = 1 ∧ ((zeroWeightValue c).2 * 2 ^ (c.n + 1)).den = 1 := by
  have h0 : ((0 : ℚ) * 2 ^ (c.n + 1)).den = 1 := by simp
  have h1 : ((1 : ℚ) * 2 ^ (c.n + 1)).den = 1 := by simp
  unfold zeroWeightValue
  split
  · dsimp only; split <;> exact ⟨by assumption, h0⟩
  · dsimp only; split <;> exact ⟨by assumption, h0⟩
  · split
    · dsimp only; split <;> exact ⟨by assumption, h0⟩
    · exact ⟨half_den c.n, h0⟩

open Classical in
theorem counterOnCall_den (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    ((counterOnCall B1 B2 cT c w).1 * 2 ^ (c.n + 1)).den = 1 ∧
      ((counterOnCall B1 B2 cT c w).2 * 2 ^ (c.n + 1)).den = 1 := by
  have hdef : (defaultValue.1 * 2 ^ (c.n + 1)).den = 1 ∧ (defaultValue.2 * 2 ^ (c.n + 1)).den = 1 :=
    ⟨half_den c.n, half_den c.n⟩
  unfold counterOnCall
  split_ifs
  · exact zeroWeightValue_den c
  · split
    · exact hdef
    · split
      · exact hdef
      · exact outputOf_den c _ _
  · exact hdef

/-- Every counter built by `counterOfMachine` has `DenOK` (its `value` is `counterOnCall`). -/
theorem counterOfMachine_denOK
    (hR : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hB : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (hP : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 B2 cT : ℕ) (hB1 : 0 < B1) (hcT : 0 < cT)
    (budget : Call → List Bool → ℕ)
    (program : WordFunction (Call × List Bool) (fun r => frame (callWord r.1) ++ frame r.2)
      (fun r => outputWord (counterOnCall B1 B2 cT r.1 r.2)) (fun r => budget r.1 r.2))
    (fast : ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 → ∀ w : List Bool,
      budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n)
    (rest : ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ c.Admitted B1 B2 →
      budget c w ≤ K * ((callWord c).length + 1) ^ e) :
    DenOK (counterOfMachine hR hB hP B1 B2 cT hB1 hcT budget program fast rest) :=
  fun c w => counterOnCall_den B1 B2 cT c w

end NearCubicGates.Close.Counter
