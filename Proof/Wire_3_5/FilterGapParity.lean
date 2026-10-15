import Proof.Wire_3_5.FilterGapInclusion
import Proof.Wire_3_5.TraceBias

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierPipeline Finset
open NearCubicWires.WireExponent3_5.Shared

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The operations of a finite field with an `𝔽₂`-valued additive trace `Tr`. -/
def fieldOps (Tr : K →+ ZMod 2) : BiasOps K := ⟨(· * ·), 1, fun x => decide (Tr x = 1)⟩

omit [Fintype K] [DecidableEq K] in
theorem fieldOps_pow (Tr : K →+ ZMod 2) (v : K) (k : ℕ) : (fieldOps Tr).pow v k = v ^ k := by
  induction k with
  | zero => simp [BiasOps.pow, fieldOps]
  | succ k ih => rw [BiasOps.pow, ih, pow_succ]; rfl

omit [Fintype K] [DecidableEq K] in
theorem biasBit_fieldOps (Tr : K →+ ZMod 2) (u v : K) (i : ℕ) :
    biasBit (fieldOps Tr) u v i = decide (Tr (u * v ^ (i + 1)) = 1) := by
  simp only [biasBit, fieldOps_pow]; rfl

omit [Fintype K] [DecidableEq K] in
theorem psi_eq_ite (Tr : K →+ ZMod 2) (x : K) : psi Tr x = if Tr x = 1 then -1 else 1 := by
  unfold psi
  rcases zmod2_cases (Tr x) with h | h <;> simp [h]

omit [Fintype K] [DecidableEq K] in
/-- `(−1)^{Σ_{i∈S} Tr(f_i)} = ψ(Σ_{i∈S} f_i)`: the trace is additive. -/
theorem psi_sum (Tr : K →+ ZMod 2) (S : Finset ℕ) (f : ℕ → K) :
    psi Tr (∑ i ∈ S, f i) = (-1) ^ (S.filter fun i => Tr (f i) = 1).card := by
  have hprod : psi Tr (∑ i ∈ S, f i) = ∏ i ∈ S, psi Tr (f i) := by
    induction S using Finset.induction_on with
    | empty => simp [psi]
    | insert a S ha ih => rw [Finset.sum_insert ha, psi_add, ih, Finset.prod_insert ha]
  rw [hprod]
  simp only [psi_eq_ite]
  rw [Finset.prod_ite]
  simp

omit [Fintype K] [DecidableEq K] in
/-- The parity bit as a real: `[P = 1] = (1 − ψ(Σ_{i∈S} u v^{i+1}))/2`. -/
theorem bitAsReal_parity (Tr : K →+ ZMod 2) (S : Finset ℕ) (u v : K) :
    bitAsReal (decide (Odd (S.filter fun i => biasBit (fieldOps Tr) u v i = true).card)) =
      (1 - (psi Tr (∑ i ∈ S, u * v ^ (i + 1)) : ℝ)) / 2 := by
  rw [psi_sum]
  simp only [biasBit_fieldOps, decide_eq_true_eq]
  rcases Nat.even_or_odd (S.filter fun i => Tr (u * v ^ (i + 1)) = 1).card with he | ho
  · have : ¬ Odd (S.filter fun i => Tr (u * v ^ (i + 1)) = 1).card := Nat.not_odd_iff_even.mpr he
    simp [this, bitAsReal, he.neg_one_pow]
  · simp [ho, bitAsReal, ho.neg_one_pow]

/-- The shifted exponent set `J = S + 1` of `P_J(V) = Σ_{j∈J} V^j`. -/
def shiftUp (S : Finset ℕ) : Finset ℕ := S.map ⟨(· + 1), add_left_injective 1⟩

omit [Fintype K] [DecidableEq K] in
theorem sum_shiftUp (S : Finset ℕ) (f : ℕ → K) : ∑ j ∈ shiftUp S, f j = ∑ i ∈ S, f (i + 1) := by
  simp [shiftUp, Finset.sum_map]

theorem sum_parity_sandwich (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) (S : Finset ℕ) (hS : S.Nonempty)
    (M : ℕ) (hSM : ∀ i ∈ S, i + 1 ≤ M) :
    ((Fintype.card K : ℝ) ^ 2 - Fintype.card K * M) / 2 ≤
        ∑ u : K, ∑ v : K,
          bitAsReal (decide (Odd (S.filter fun i => biasBit (fieldOps Tr) u v i = true).card)) ∧
      (∑ u : K, ∑ v : K,
          bitAsReal (decide (Odd (S.filter fun i => biasBit (fieldOps Tr) u v i = true).card))) ≤
        (Fintype.card K : ℝ) ^ 2 / 2 := by
  have hJ : (shiftUp S).Nonempty := by simpa [shiftUp] using hS
  have hJM : ∀ j ∈ shiftUp S, j ≤ M := by
    intro j hj; simp only [shiftUp, Finset.mem_map, Function.Embedding.coeFn_mk] at hj
    obtain ⟨i, hi, rfl⟩ := hj; exact hSM i hi
  obtain ⟨heq, hle⟩ := parity_bias Tr hTr (shiftUp S) hJ M hJM
  simp only [sum_shiftUp] at heq
  simp only [bitAsReal_parity]
  have hsum : (∑ u : K, ∑ v : K, (1 - (psi Tr (∑ i ∈ S, u * v ^ (i + 1)) : ℝ)) / 2) =
      ((Fintype.card K : ℝ) ^ 2 - ((∑ u : K, ∑ v : K, psi Tr (∑ i ∈ S, u * v ^ (i + 1)) : ℤ) : ℝ)) / 2 := by
    push_cast
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum, heq]
  set Zc := (univ.filter fun v : K => (selectorPoly (shiftUp S)).eval v = 0).card
  have hZc : (Zc : ℝ) ≤ M := by exact_mod_cast hle
  have hK : (0 : ℝ) ≤ Fintype.card K := by positivity
  push_cast
  constructor
  · have : (Fintype.card K : ℝ) * Zc ≤ Fintype.card K * M := mul_le_mul_of_nonneg_left hZc hK
    linarith
  · have : (0 : ℝ) ≤ Fintype.card K * Zc := by positivity
    linarith

omit [DecidableEq K] in
/-- With the empty selected set, the parity is `0`. -/
theorem sum_parity_empty (Tr : K →+ ZMod 2) :
    (∑ u : K, ∑ v : K,
      bitAsReal (decide (Odd ((∅ : Finset ℕ).filter fun i => biasBit (fieldOps Tr) u v i = true).card))) = 0 := by
  simp [bitAsReal]

/-! ## The per-copy probability `q = Pr_{h,u,v}[P = 1]` -/

omit [DecidableEq K] in
/-- `Σ_{c}[P(c)=1]` as the Toeplitz sum of the `(u,v)` sums at `S = selectedActive h Z`. -/
theorem sum_copyParity (P : GapParams) (Tr : K →+ ZMod 2) (Z : List Bool) :
    (∑ c : CopySeed P K, bitAsReal (copyParity P (fieldOps Tr) c Z)) =
      ∑ h : ToeplitzSeed P.labelBits, ∑ u : K, ∑ v : K,
        bitAsReal (decide (Odd ((selectedActive P h Z).filter fun i =>
          biasBit (fieldOps Tr) u v i = true).card)) := by
  simp only [Fintype.sum_prod_type]; rfl

omit [Field K] [DecidableEq K] in
theorem card_copySeed (P : GapParams) :
    Fintype.card (CopySeed P K) = Fintype.card (ToeplitzSeed P.labelBits) * (Fintype.card K) ^ 2 := by
  simp [Fintype.card_prod, sq]

/-- `q ≤ (1/2)·Pr_h[S ≠ ∅]` and `q ≥ (15/32)·Pr_h[S ≠ ∅]`, for `|𝕂| ≥ 16M` and `Z` of at most `M` coordinates. -/
theorem copyParity_prob_bounds (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (Z : List Bool) (hZ : Z.length ≤ P.len) :
    (15 / 32 : ℝ) * booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) ≤
        booleanMean (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z) ∧
      booleanMean (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z) ≤
        (1 / 2 : ℝ) * booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) := by
  set k : ℝ := (Fintype.card K : ℝ)
  set NH : ℝ := (Fintype.card (ToeplitzSeed P.labelBits) : ℝ)
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  have hNH : 0 < NH := Nat.cast_pos.mpr Fintype.card_pos
  have hkM : 16 * (P.len : ℝ) ≤ k := by simp only [k]; exact_mod_cast hK
  -- per-`h` bounds
  have hper : ∀ h : ToeplitzSeed P.labelBits,
      (15 / 32 : ℝ) * k ^ 2 * bitAsReal (decide (selectedActive P h Z).Nonempty) ≤
          ∑ u : K, ∑ v : K, bitAsReal (decide (Odd ((selectedActive P h Z).filter fun i =>
            biasBit (fieldOps Tr) u v i = true).card)) ∧
        (∑ u : K, ∑ v : K, bitAsReal (decide (Odd ((selectedActive P h Z).filter fun i =>
            biasBit (fieldOps Tr) u v i = true).card))) ≤
          (1 / 2 : ℝ) * k ^ 2 * bitAsReal (decide (selectedActive P h Z).Nonempty) := by
    intro h
    by_cases hne : (selectedActive P h Z).Nonempty
    · have hSM : ∀ i ∈ selectedActive P h Z, i + 1 ≤ P.len := by
        intro i hi
        simp only [selectedActive, Finset.mem_filter, Finset.mem_range] at hi
        omega
      obtain ⟨h1, h2⟩ := sum_parity_sandwich Tr hTr _ hne P.len hSM
      rw [show bitAsReal (decide (selectedActive P h Z).Nonempty) = 1 by simp [hne, bitAsReal], mul_one]
      constructor
      · have : (15 / 32 : ℝ) * k ^ 2 ≤ (k ^ 2 - k * P.len) / 2 := by nlinarith
        linarith
      · linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, sum_parity_empty]
      simp [bitAsReal]
  unfold booleanMean
  rw [sum_copyParity, card_copySeed]
  push_cast
  constructor
  · rw [mul_div_assoc', div_le_div_iff₀ hNH (by positivity)]
    have := Finset.sum_le_sum fun h (_ : h ∈ (univ : Finset (ToeplitzSeed P.labelBits))) => (hper h).1
    rw [← Finset.mul_sum] at this
    nlinarith
  · rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hNH]
    have := Finset.sum_le_sum fun h (_ : h ∈ (univ : Finset (ToeplitzSeed P.labelBits))) => (hper h).2
    rw [← Finset.mul_sum] at this
    nlinarith

theorem copyParity_prob_le_low (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (Z : List Bool) (hZ : Z.length ≤ P.len) (hw : Z.count true ≤ P.cap) :
    booleanMean (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z) ≤ 1 / 64 := by
  have h1 := (copyParity_prob_bounds P Tr hTr hK Z hZ).2
  have h2 := nonempty_prob_le_low P Z hw
  linarith

theorem copyParity_prob_ge_high (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (hU : 1 ≤ P.cap) (Z : List Bool) (hZ : Z.length ≤ P.len)
    (hw : 4096 * P.cap ≤ Z.count true) :
    (6 / 13 : ℝ) ≤ booleanMean (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z) := by
  have h1 := (copyParity_prob_bounds P Tr hTr hK Z hZ).1
  have h2 := nonempty_prob_ge_high P hU Z (hZ.trans P.len_le_two_pow_labelBits) hw
  linarith

theorem copyParity_prob_le_half (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (Z : List Bool) (hZ : Z.length ≤ P.len) :
    booleanMean (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z) ≤ 1 / 2 := by
  have h1 := (copyParity_prob_bounds P Tr hTr hK Z hZ).2
  have h2 : booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) ≤ 1 := by
    unfold booleanMean
    rw [div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]
    calc (∑ h : ToeplitzSeed P.labelBits, bitAsReal (decide (selectedActive P h Z).Nonempty))
        ≤ ∑ _h : ToeplitzSeed P.labelBits, (1 : ℝ) :=
          Finset.sum_le_sum fun h _ => by cases decide (selectedActive P h Z).Nonempty <;> simp [bitAsReal]
      _ = _ := by simp
  linarith

end NearCubicWires.WireExponent3_5.Filters
