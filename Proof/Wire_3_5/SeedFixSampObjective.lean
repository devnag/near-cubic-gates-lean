import Proof.Wire_3_5.SeedFixSampler
import Proof.Wire_3_5.SeedFixGreedy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Primitive Finset
open scoped Matrix

/-! ## Prefixes as seed numbers -/

/-- The number whose binary digits are a list (bit `i` is the list's entry `i`). -/
def listNum : List Bool → ℕ
  | [] => 0
  | b :: p => Nat.bit b (listNum p)

theorem listNum_lt : ∀ p : List Bool, listNum p < 2 ^ p.length
  | [] => by simp [listNum]
  | b :: p => by
    have := listNum_lt p
    rw [listNum, Nat.bit_val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem bitsNum_cons (m : ℕ) (b : Bool) (s : Fin m → Bool) :
    bitsNum (m + 1) (Fin.cons b s) = Nat.bit b (bitsNum m s) := by
  simp only [bitsNum, Fin.cons_zero, Fin.cons_succ]

theorem sum_range_two_mul_rat (f : ℕ → ℚ) : ∀ m : ℕ, ∑ r ∈ range (2 * m), f r =
    ∑ r ∈ range m, f (2 * r) + ∑ r ∈ range m, f (2 * r + 1)
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_two_mul_rat f n,
      sum_range_succ, sum_range_succ]
    ring

/-- The seed bits range over the seed numbers below `2^m`. -/
theorem sum_bitsNum : ∀ (m : ℕ) (F : ℕ → ℚ), ∑ s : Fin m → Bool, F (bitsNum m s) = ∑ r ∈ range (2 ^ m), F r
  | 0, F => by simp [bitsNum]
  | m + 1, F => by
    have e : ∀ (b : Bool) (y : Fin m → Bool), (Fin.consEquiv fun _ : Fin (m + 1) => Bool) (b, y) = Fin.cons b y :=
      fun _ _ => rfl
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [e, bitsNum_cons, Nat.bit_true_apply, Nat.bit_false_apply]
    rw [sum_bitsNum m (fun x => F (2 * x + 1)), sum_bitsNum m (fun x => F (2 * x)), pow_succ, mul_comm (2 ^ m) 2,
      sum_range_two_mul_rat, add_comm]

theorem condMean_bits : ∀ (p : List Bool) (m : ℕ) (F : ℕ → ℚ), p.length ≤ m →
    condMean m (fun s => F (bitsNum m s)) p =
      (∑ r ∈ range (2 ^ (m - p.length)), F (listNum p + 2 ^ p.length * r)) / 2 ^ (m - p.length)
  | [], m, F, _ => by
    rw [condMean_nil]
    unfold qMean
    rw [sum_bitsNum]
    simp [listNum]
  | _ :: _, 0, _, h => absurd h (by simp)
  | b :: p, m + 1, F, h => by
    rw [condMean_cons]
    have hp : p.length ≤ m := by simp at h; omega
    have e : (fun s : Fin m → Bool => F (bitsNum (m + 1) (Fin.cons b s))) =
        fun s => (fun x => F (Nat.bit b x)) (bitsNum m s) := funext fun s => by rw [bitsNum_cons]
    rw [e, condMean_bits p m (fun x => F (Nat.bit b x)) hp]
    simp only [List.length_cons, Nat.add_sub_add_right, listNum]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    congr 1
    rw [Nat.bit_val, Nat.bit_val, pow_succ]
    ring

/-! ## The elimination form of the printed column value -/

section Elim
variable (P : SeedParams) {T : Type} [Fintype T]

/-- A position as a number: `(U, V) ↦ V + N·U` (the inverse of `SeedParams.cellEquiv`'s digit reading). -/
def cellNumC {N : ℕ} (c : Cell N) : ℕ := c.2 + N * c.1

theorem cellNumC_eq (c : Cell P.N) : cellNumC c = cellNum P c := by
  have hlt : cellNumC c < 2 ^ (2 * P.kh) := by
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    have : cellNumC c < P.N * P.N := by
      unfold cellNumC
      nlinarith
    rw [two_mul, pow_add]
    exact this
  unfold cellNum
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofVec]
  by_cases hi : i < 2 * P.kh
  · have hv : ((P.cellEquiv.symm c ⟨i, hi⟩ : ZMod 2) : Fin 2).val = cellNumC c / 2 ^ i % 2 := by
      show ((finFunctionFinEquiv.symm ((finCongr _).symm (finProdFinEquiv.symm.symm c))) ⟨i, hi⟩).val = _
      rw [finFunctionFinEquiv_symm_apply_val]
      rfl
    have hne : (P.cellEquiv.symm c ⟨i, hi⟩ ≠ 0) ↔ (cellNumC c).testBit i := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
      constructor
      · intro h
        have h1 : ((P.cellEquiv.symm c ⟨i, hi⟩ : ZMod 2) : Fin 2).val ≠ 0 := fun h0 => h (Fin.ext h0)
        rw [hv] at h1
        omega
      · intro h h0
        have := congrArg (fun x : ZMod 2 => (x : Fin 2).val) h0
        rw [hv] at this
        change cellNumC c / 2 ^ i % 2 = 0 at this
        omega
    by_cases hb : (cellNumC c).testBit i
    · rw [hb]; exact (decide_eq_true ⟨hi, hne.mpr hb⟩).symm
    · rw [Bool.not_eq_true] at hb
      rw [hb]
      refine (decide_eq_false ?_).symm
      rintro ⟨_, h⟩
      have := hne.mp h
      rw [hb] at this
      exact Bool.false_ne_true this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_exists]
    intro h; omega

/-- The constraints of a subset `β` of the eight positions of a walk term, computably. -/
def consOfC (α : Fin 8 → Fin P.Q) (c : Fin 8 → Cell P.N) (β : Fin 8 → Bool) : List (ℕ × ℕ) :=
  (List.finRange 8).filterMap fun k => if β k then some ((α k : ℕ), cellNumC (c k)) else none

theorem consOfC_eq (α : Fin 8 → Fin P.Q) (c : Fin 8 → Cell P.N) (β : Fin 8 → Bool) :
    consOfC P α c β = consOf P α c β := by
  unfold consOfC consOf
  simp only [cellNumC_eq]

def coefW (plen pre : ℕ) (w : Fin 8 → Fin P.N) : ℤ :=
  ∑ α : Fin 8 → Fin P.Q, ∑ β : Fin 8 → Bool,
    (-(P.N : ℤ) ^ 2) ^ (Finset.univ.filter fun k => β k = true).card *
      ((JoinElimination.condProbGauss P.modulus P.ell 8 (2 * P.kh) plen pre
        (consOfC P α (fun k => cellOf (by norm_num) w k) β)).1 : ℤ)

def sampElim (Dz : T → Cell P.N → Bool) (plen pre : ℕ) : ℤ :=
  ∑ t, ∑ w : Fin 8 → Fin P.N, coefW P plen pre w * ∏ k, bitZ (Dz t (cellOf (by norm_num) w k))

theorem bitZ_cast (b : Bool) : ((bitZ b : ℤ) : ℝ) = bitR b := by cases b <;> simp [bitZ, bitR]

/-- **`V_p(z)` is the sum of the column potential over the completions** (`SamplerFix.condSum_eq`). -/
theorem sampElim_cast (Dz : T → Cell P.N → Bool) (plen pre : ℕ) (hplen : plen ≤ 8 * P.ell) :
    ((sampElim P Dz plen pre : ℤ) : ℝ) = condSum P (fun t c => bitR (Dz t c)) plen pre := by
  rw [condSum_eq P _ plen pre hplen]
  unfold sampElim coefW
  push_cast
  refine sum_congr rfl fun t _ => sum_congr rfl fun w _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun α _ => ?_
  rw [sum_mul, mul_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [consOfC_eq]
  simp only [bitZ_cast]
  ring

theorem sampElim_nonneg (Dz : T → Cell P.N → Bool) (plen pre : ℕ) (hplen : plen ≤ 8 * P.ell) :
    0 ≤ sampElim P Dz plen pre := by
  have h := condSum_nonneg P (fun t c => bitR (Dz t c)) plen pre
  rw [← sampElim_cast P Dz plen pre hplen] at h
  exact_mod_cast h

theorem sampElim_le (Dz : T → Cell P.N → Bool) (plen pre : ℕ) (hplen : plen ≤ 8 * P.ell) :
    sampElim P Dz plen pre ≤ 2 ^ (8 * P.ell - plen) * (Fintype.card T * (P.N ^ 8 * (P.Q * P.N ^ 2) ^ 8)) := by
  have hD : ∀ t c, |bitR (Dz t c)| ≤ 1 := fun t c => by cases Dz t c <;> simp [bitR]
  have h := condSum_le P (fun t c => bitR (Dz t c)) hD plen pre
  rw [← sampElim_cast P Dz plen pre hplen] at h
  exact_mod_cast h

end Elim

/-! ## The child sums are the scaled conditional objectives -/

section Sums
variable {Z T : Type} [Fintype Z] [Fintype T]

/-- The greedy objective as a function of the seed number: the exact potential of the positions. -/
theorem potQ_posC_cast (P : SeedParams) (D : Z → T → Cell P.N → Bool) (σ : ℕ) :
    ((potQ D (posC P σ) : ℚ) : ℝ) = ∑ z, colPot P (fun t c => bitR (D z t c)) σ := by
  rw [potQ_cast, posC_eq]
  rfl

def sampSum (P : SeedParams) (D : Z → T → Cell P.N → Bool) (p : List Bool) : ℤ :=
  ∑ z, sampElim P (D z) p.length (listNum p)

/-- **The child sums are `2^{8ℓ−|p|−1}` times the conditional objectives** of `greedyBitsQ`. -/
theorem sampSum_scaled (P : SeedParams) (D : Z → T → Cell P.N → Bool) :
    ScaledSums (8 * P.ell) (fun s => potQList D (List.ofFn (posC P (bitsNum _ s)))) (sampSum P D)
      (fun i => 2 ^ (8 * P.ell - i - 1)) := by
  refine ⟨fun i => by positivity, fun p b hp => ?_⟩
  have hq : (p ++ [b]).length ≤ 8 * P.ell := by simp; omega
  have hΦ : (fun s : Fin (8 * P.ell) → Bool => potQList D (List.ofFn (posC P (bitsNum _ s)))) =
      fun s => potQ D (posC P (bitsNum _ s)) := funext fun s => potQList_ofFn D _
  have hc := condMean_bits (p ++ [b]) (8 * P.ell) (fun σ => potQ D (posC P σ)) hq
  rw [hΦ, hc]
  have hexp : 8 * P.ell - p.length - 1 = 8 * P.ell - (p ++ [b]).length := by simp; omega
  beta_reduce
  rw [hexp, mul_div_cancel₀ _ (by positivity)]
  apply Rat.cast_injective (α := ℝ)
  unfold sampSum
  push_cast
  simp only [potQ_posC_cast]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sampElim_cast P (D z) _ _ hq]
  unfold condSum completion
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.mod_eq_of_lt (listNum_lt _), Nat.shiftLeft_eq, mul_comm]

theorem sampLoop_eq (P : SeedParams) (D : Z → T → Cell P.N → Bool) :
    greedyLoop (8 * P.ell) (sampSum P D) = List.ofFn (greedyBitsQ P D) :=
  greedyLoop_eq_greedyQ _ _ _ _ (sampSum_scaled P D)

end Sums

end NearCubicWires.WireExponent3_5.SeedFix
