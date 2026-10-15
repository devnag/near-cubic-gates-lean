import Proof.Gates.CheckedPCPP.Composite
import Proof.Gates.CheckedPCPP.SubstitutedPoly
import Proof.Gates.WorkerArith.HotFuel

/-!
# SetupU half 2: the native width is logarithmic, so every polynomial in it is at most linear in `N`

Paper v2 line 2396: "All guesses have a fixed polynomial bound in `q` and hence are `o(N)`". The native width
`q = width s g N` satisfies `2^q ≤ A (N+1)^m` (the shared `HierarchyNormalizedBounds.proof_bound`; `A, m` depend on the
clock), hence `q ≤ A + m (⌊log₂ (N+1)⌋ + 1)` (`width_log`). With `(L+1)^d ≤ d!·2^d·2^L` (`pow_le_two_pow`):
* `qpoly`: for every `d`, `(q+1)^d ≤ C (N+1)` — exponent `1` in `N`, whatever `d` and the clock;
* `qpoly_le`: for every `d, c`, eventually `c (q+1)^d ≤ N`;
* `gadgets_lin`: the gadget count `M = 2^{cl}` is at most `C (N+1)`;
* `hierarchyWord_lin`: the hierarchy word has length at most `C (N+1)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicGates.Close.Worker (width gadgets)

/-- Polynomials are dominated by `2^L`: `(L+1)^d ≤ d!·2^d·2^L`. -/
theorem pow_le_two_pow (d L : ℕ) : (L + 1) ^ d ≤ d.factorial * 2 ^ d * 2 ^ L := by
  have h1 := Nat.pow_sub_le_descFactorial (L + d) d
  have e1 : L + d + 1 - d = L + 1 := by omega
  rw [e1] at h1
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 := Nat.choose_le_two_pow (L + d) d
  calc (L + 1) ^ d ≤ d.factorial * (L + d).choose d := h1
    _ ≤ d.factorial * 2 ^ (L + d) := Nat.mul_le_mul_left _ h2
    _ = d.factorial * 2 ^ d * 2 ^ L := by rw [pow_add]; ring

/-- `(⌊log₂ (N+1)⌋ + 1)^d ≤ d!·2^d·(N+1)`. -/
theorem log_pow_le (d N : ℕ) : (Nat.log 2 (N + 1) + 1) ^ d ≤ d.factorial * 2 ^ d * (N + 1) :=
  (pow_le_two_pow d _).trans (Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega)))

theorem logScale_le (T : ℕ) : logScale T ≤ T + 2 := by
  unfold logScale
  exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

variable (s : GateSources) (g : GateParams)

/-- `2^q ≤ A (N+1)^m` (paper v2 §11.4, `q(N)`'s formula: `2^q/T_clk(N) = q^{O(1)}`). -/
theorem width_pow : ∃ A m : ℕ, ∀ N, 2 ^ width s g N ≤ A * (N + 1) ^ m :=
  Outer.widthOf_pow g.k _

/-- **The native width is logarithmic**: `q ≤ A + m (⌊log₂ (N+1)⌋ + 1)`. -/
theorem width_log : ∃ A m : ℕ, ∀ N, width s g N ≤ A + m * (Nat.log 2 (N + 1) + 1) := by
  obtain ⟨A, m, h⟩ := width_pow s g
  refine ⟨A, m, fun N => ?_⟩
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hN : N + 1 < 2 ^ (Nat.log 2 (N + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hNm : (N + 1) ^ m ≤ 2 ^ (m * (Nat.log 2 (N + 1) + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left hN.le m
  have hlt : 2 ^ width s g N < 2 ^ (A + m * (Nat.log 2 (N + 1) + 1)) := by
    calc 2 ^ width s g N ≤ A * (N + 1) ^ m := h N
      _ < 2 ^ A * 2 ^ (m * (Nat.log 2 (N + 1) + 1)) :=
          Nat.mul_lt_mul_of_lt_of_le hA hNm (by positivity)
      _ = _ := by rw [pow_add]
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt).le

/-- **Every polynomial in the native width is at most linear in `N`.** -/
theorem qpoly (d : ℕ) : ∃ C : ℕ, ∀ N, (width s g N + 1) ^ d ≤ C * (N + 1) := by
  obtain ⟨A, m, h⟩ := width_log s g
  refine ⟨(A + m + 1) ^ d * (d.factorial * 2 ^ d), fun N => ?_⟩
  have h1 : width s g N + 1 ≤ (A + m + 1) * (Nat.log 2 (N + 1) + 1) := by
    have := h N; nlinarith
  calc (width s g N + 1) ^ d ≤ ((A + m + 1) * (Nat.log 2 (N + 1) + 1)) ^ d := Nat.pow_le_pow_left h1 d
    _ = (A + m + 1) ^ d * (Nat.log 2 (N + 1) + 1) ^ d := mul_pow _ _ _
    _ ≤ (A + m + 1) ^ d * (d.factorial * 2 ^ d * (N + 1)) := Nat.mul_le_mul_left _ (log_pow_le d N)
    _ = _ := by ring

/-- **Eventually `c (q+1)^d ≤ N`.** -/
theorem qpoly_le (d c : ℕ) : ∃ N1 : ℕ, ∀ N, N1 ≤ N → c * (width s g N + 1) ^ d ≤ N := by
  obtain ⟨C, hC⟩ := qpoly s g (2 * d)
  refine ⟨c ^ 2 * C + 1, fun N hN => ?_⟩
  by_contra hlt'
  have hlt : N < c * (width s g N + 1) ^ d := Nat.lt_of_not_le hlt'
  have hsq : (c * (width s g N + 1) ^ d) ^ 2 ≤ c ^ 2 * C * (N + 1) := by
    rw [mul_pow, ← pow_mul, mul_comm d 2, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (hC N)
  have h2 : N * N < (c * (width s g N + 1) ^ d) ^ 2 := by rw [sq]; exact Nat.mul_lt_mul'' hlt hlt
  have h3 : c ^ 2 * C * (N + 1) ≤ N * N := by nlinarith
  omega

/-- The gadget count is at most linear in `N`. -/
theorem gadgets_lin : ∃ C : ℕ, ∀ N, gadgets s g N ≤ C * (N + 1) := by
  obtain ⟨C, hC⟩ := qpoly s g g.clauseDegree
  refine ⟨2 ^ (g.clauseDegree + 1) * C, fun N => ?_⟩
  have h := WorkerArith.WorkerBounds.gadgets_le g.clauseDegree (width s g N)
  calc gadgets s g N ≤ 2 ^ (g.clauseDegree + 1) * (width s g N + 1) ^ g.clauseDegree := h
    _ ≤ 2 ^ (g.clauseDegree + 1) * (C * (N + 1)) := Nat.mul_le_mul_left _ (hC N)
    _ = _ := by ring

theorem natBitLength_time_leG (c m n : ℕ) (T : ℕ) (hT : T ≤ c * (n + 1) ^ m) :
    natBitLength T + 1 ≤ (c + m + 2) * (n + 1) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos T with rfl | hpos
  · simp only [Nat.log_zero_right]; nlinarith
  have hc : c < 2 ^ c := Nat.lt_two_pow_self
  have hn : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hpow : (n + 1) ^ m ≤ 2 ^ ((n + 1) * m) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hn.le m
  have hT2 : T < 2 ^ (c + (n + 1) * m) := by
    calc T ≤ c * (n + 1) ^ m := hT
      _ < 2 ^ c * 2 ^ ((n + 1) * m) := by
          have h1 : 0 < (n + 1) ^ m := by positivity
          calc c * (n + 1) ^ m < 2 ^ c * (n + 1) ^ m := Nat.mul_lt_mul_of_pos_right hc h1
            _ ≤ 2 ^ c * 2 ^ ((n + 1) * m) := Nat.mul_le_mul_left _ hpow
      _ = 2 ^ (c + (n + 1) * m) := by rw [pow_add]
  have hlog : Nat.log 2 T < c + (n + 1) * m := Nat.log_lt_of_lt_pow (by omega) hT2
  nlinarith

/-- The hierarchy word has length at most linear in `N`. -/
theorem hierarchyWord_lin : ∃ C : ℕ, ∀ N (x : BitInput N),
    (CheckedPCPP.hierarchyWord s g.k g.clock x).length ≤ C * (N + 1) := by
  let H := (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy
  refine ⟨2 * (2 * H.coefficient + 2 + (g.k + 2) + 2) + 4, fun N x => ?_⟩
  have hl : (CheckedPCPP.hierarchyWord s g.k g.clock x).length = 2 * N + 1 + (2 * (H.time N).bits.length + 1) := by
    simp only [CheckedPCPP.hierarchyWord, HierarchySourceInput.hierarchyInput, List.length_append,
      CheckedPCPP.SubstitutedPoly.frame_len']
    simp
    rfl
  have ht : H.time N ≤ (2 * H.coefficient + 2) * (N + 1) ^ (g.k + 2) := by
    have hn := Nat.one_le_pow (g.k + 2) (N + 1) (by omega)
    have hpower := Nat.pow_le_pow_left (Nat.le_succ N) (g.k + 2)
    change H.coefficient * (N ^ (g.k + 2) + 1) ≤ _
    nlinarith
  have hs := natBitLength_time_leG (2 * H.coefficient + 2) (g.k + 2) N (H.time N) ht
  have hb := CheckedPCPP.SubstitutedPoly.bitLen_le_bits (H.time N)
  have hb2 : (H.time N).bits.length ≤ natBitLength (H.time N) := by
    rcases Nat.eq_zero_or_pos (H.time N) with h0 | h0
    · rw [h0]; simp
    rw [Nat.size_eq_bits_len]
    unfold natBitLength
    rw [Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  rw [hl]
  nlinarith

end NearCubicGates.Close.Setup
