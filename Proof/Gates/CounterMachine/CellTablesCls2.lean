import Proof.Gates.CounterMachine.CellTablesCls1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {B1 B2 cT : ℕ}

/-- The size facts of a call. -/
structure Sizes (r : CellReq B1 B2 cT) : Prop where
  P : r.p.P ≤ r.c.n
  k : r.p.k ≤ r.c.n
  J : r.p.J ≤ Jmax r.c.n
  e : r.p.e ≤ 2 * r.p.k + 2
  rc : roleCount r.c.kind ≤ 2
  rc1 : 1 ≤ roleCount r.c.kind
  q : ∀ q ∈ r.p.primes, q ≤ r.p.P ∧ 2 ≤ q
  np : (r.p.primes.sort (· ≤ ·)).length ≤ r.c.n + 1
  X : (cellInput r).length ≤ 2 ^ 19 * (r.c.n + 1) ^ (B1 + B2 + 13)
  D : dOf r.c r.p ≤ 2 * (cellInput r).length + 2
  DJ : dOf r.c r.p ≤ 2 * Jmax r.c.n + 2
  L1 : r.c.n + 1 ≤ 2 ^ natBitLength r.c.n
  L2 : 2 ^ natBitLength r.c.n ≤ 2 * (r.c.n + 1)
  L3 : natBitLength r.c.n ≤ r.c.n + 1
  db : Nat.size (deltaBound r.c r.p) ≤ 3 * (cellInput r).length + 5
  JX : r.p.J ≤ 2 * (cellInput r).length + 2

theorem sizes (r : CellReq B1 B2 cT) : Sizes r := by
  have hs := cellReq_spec r
  set X := (cellInput r).length with hX
  have hP := P_le_n r.c r.p hs
  have he : r.p.e ≤ 2 * (r.p.k + 1) := (leastUpTo_spec _ _ _ hs.e_eq).2.1
  have hrc : roleCount r.c.kind ≤ 2 := by cases r.c.kind <;> decide
  have hrc1 := roleCount_pos r.c.kind
  have hJD : r.p.J ≤ dOf r.c r.p := by unfold dOf; nlinarith
  have hD := dOf_le r
  have hJ := J_le_Jmax r.c r.p hs
  have hL1 : r.c.n < 2 ^ natBitLength r.c.n := Cells.lt_natBitLength _
  have hmemN : ∀ v ∈ paramsN r.p, v < 2 ^ X := fun v hv => lt_of_lt_of_le (Cells.lt_natBitLength v)
    (Nat.pow_le_pow_right (by norm_num) (nbl_le_cellInput r v (by unfold cellN; simp [hv])))
  refine ⟨hP, le_of_lt hs.k_lt, hJ, by omega, hrc, hrc1, fun q hq => ?_, ?_, cellInput_le r, hD, ?_, by omega, ?_,
    ?_, ?_, by omega⟩
  · exact ⟨(prime_le_P r hq).1, (prime_le_P r hq).2.two_le⟩
  · rw [Finset.length_sort]
    calc r.p.primes.card ≤ (Finset.range (r.p.P + 1)).card :=
          Finset.card_le_card (fun q hq => Finset.mem_range.mpr (by have := (prime_le_P r hq).1; omega))
      _ = r.p.P + 1 := Finset.card_range _
      _ ≤ r.c.n + 1 := by omega
  · unfold dOf; nlinarith
  · unfold natBitLength
    rcases Nat.eq_zero_or_pos r.c.n with h0 | h0
    · rw [h0]; simp
    · have := Nat.pow_log_le_self 2 (by omega : r.c.n ≠ 0)
      rw [pow_succ]; omega
  · unfold natBitLength
    have := Nat.log_le_self 2 r.c.n
    omega
  · -- the delta bound
    have hM1 : r.p.M1 < 2 ^ X := hmemN _ (by unfold paramsN; simp)
    have hA : r.p.A < 2 ^ X := hmemN _ (by unfold paramsN; simp)
    have hWp : r.p.W < 2 ^ X := hmemN _ (by unfold paramsN; simp)
    have hF := factors_sum_lt r
    have hWc : r.p.W = r.c.W := hs.W_eq
    rw [Nat.size_le]
    unfold deltaBound
    rw [← hWc]
    have h2X : 2 ^ (2 * X) = 2 ^ X * 2 ^ X := by rw [← pow_add]; ring_nf
    have h34 : 2 ^ (3 * X + 5) = 32 * (2 ^ X * 2 ^ X * 2 ^ X) := by
      rw [show 3 * X + 5 = X + X + X + 5 by ring, pow_add, pow_add, pow_add]; ring
    rw [h34]
    have hpos : 1 ≤ 2 ^ X := Nat.one_le_two_pow
    have h1 : r.p.M1 + r.p.A + r.p.factors.sum + 1 ≤ 4 * (2 ^ X * 2 ^ X) := by rw [h2X] at hF; nlinarith
    have h2 : r.p.W + 1 ≤ 2 * 2 ^ X := by omega
    calc 2 * (r.p.M1 + r.p.A + r.p.factors.sum + 1) * (r.p.W + 1) ≤ 2 * (4 * (2 ^ X * 2 ^ X)) * (2 * 2 ^ X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ < 32 * (2 ^ X * 2 ^ X * 2 ^ X) := by nlinarith

end NearCubicGates.Close.CounterMachine.CellTablesProg
