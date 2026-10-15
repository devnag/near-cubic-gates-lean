import Proof.Gates.CounterMachine.CellTablesCls5

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

theorem kGap (cT n : ℕ) : Counter.inner cT n - kLow cT (natBitLength n) ≤ 6 * natBitLength n + 2 + cT := by
  set L := natBitLength n with hL
  set s := Nat.size (L - 2) with hs
  have hnL : n < 2 ^ L := Cells.lt_natBitLength n
  have hlam : Target.lambda n ≤ L := Nat.clog_le_of_le_pow hnL.le
  have hs2 : L ≤ 2 ^ (s + 1) := by
    have h1 : L - 2 < 2 ^ s := Nat.lt_size_self _
    have h2 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have hmu : Target.mu n ≤ s + 1 := by
    unfold Target.mu
    exact (Nat.clog_mono_right 2 hlam).trans (Nat.clog_le_of_le_pow hs2)
  have hsL : s ≤ L := by
    have : L - 2 < 2 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self
    exact Nat.size_le.mpr this
  unfold Counter.inner kLow Jmax
  rw [← hs]
  have h1 : (2 * (Target.mu n + 1) + cT + Target.mu n) * Target.lambda n ≤ (3 * s + 5 + cT) * L :=
    Nat.mul_le_mul (by omega) hlam
  have hL1 : 1 ≤ L := Cells.natBitLength_pos n
  obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have h2 : (3 * s + 5 + cT) * L = (2 + cT + 3 * s) * (L - 1) + (3 * L + 3 * s + 2 + cT) := by
    rw [hM, Nat.add_sub_cancel]; ring
  omega

/-- The reserved call bound of `zK`: `2^{c₃L}·2^{n−kLow}·a₃ ≤ a₃·2^{e₀+8+c_T}·2^{n−k}·(n+1)^{e₀+6}`. -/
theorem Bk_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    (zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)).Bk (natBitLength r.c.n) ≤
      (C0 + 1) * 2 ^ (e0 + 8 + cT) * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (e0 + 6) := by
  have sz := sizes r
  have hs := cellReq_spec r
  set L := natBitLength r.c.n with hL
  set T := r.c.n + 1 with hT
  have hk : kLow cT L ≤ r.p.k := by rw [hs.k_eq]; exact kLow_le cT _
  have hgap : r.p.k - kLow cT L ≤ 6 * L + 2 + cT := by rw [hs.k_eq]; exact kGap cT r.c.n
  have hkn := sz.k
  have hsplit : r.c.n - kLow cT L = (r.c.n - r.p.k) + (r.p.k - kLow cT L) := by omega
  have h2L : 2 ^ L ≤ 2 * T := sz.L2
  have hgap2 : 2 ^ (r.p.k - kLow cT L) ≤ 2 ^ (8 + cT) * T ^ 6 := by
    calc 2 ^ (r.p.k - kLow cT L) ≤ 2 ^ (6 * L + 2 + cT) := Nat.pow_le_pow_right (by norm_num) hgap
      _ = (2 ^ L) ^ 6 * 2 ^ (2 + cT) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ (2 * T) ^ 6 * 2 ^ (2 + cT) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2L 6)
      _ = 2 ^ (8 + cT) * T ^ 6 := by rw [mul_pow, pow_add, pow_add]; ring
  have hc3 : 2 ^ (e0 * L) ≤ 2 ^ e0 * T ^ e0 := by
    calc 2 ^ (e0 * L) = (2 ^ L) ^ e0 := by rw [← pow_mul, mul_comm]
      _ ≤ (2 * T) ^ e0 := Nat.pow_le_pow_left h2L e0
      _ = 2 ^ e0 * T ^ e0 := mul_pow _ _ _
  show 2 ^ (e0 * L) * (2 ^ (r.c.n - kLow cT L) * (C0 + 1)) ≤ _
  rw [hsplit, pow_add]
  calc 2 ^ (e0 * L) * (2 ^ (r.c.n - r.p.k) * 2 ^ (r.p.k - kLow cT L) * (C0 + 1))
      ≤ (2 ^ e0 * T ^ e0) * (2 ^ (r.c.n - r.p.k) * (2 ^ (8 + cT) * T ^ 6) * (C0 + 1)) :=
        Nat.mul_le_mul hc3 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hgap2))
    _ = (C0 + 1) * 2 ^ (e0 + 8 + cT) * 2 ^ (r.c.n - r.p.k) * T ^ (e0 + 6) := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring

end NearCubicGates.Close.CounterMachine.CellTablesProg
