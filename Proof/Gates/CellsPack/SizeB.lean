import Proof.Gates.CellsPack.Size

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.SystemsPhase

theorem flatMap_range_len {α : Type} (N B : ℕ) (f : ℕ → List α) (h : ∀ i < N, (f i).length ≤ B) :
    ((List.range N).flatMap f).length ≤ N * B := by
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul ((List.range N).map fun i => (f i).length) B (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact h i (List.mem_range.mp hi))
  simpa using this

theorem natWord_len_le (v k : ℕ) (h : v < 2 ^ k) (hk : 1 ≤ k) : (natWord v).length ≤ 2 * k + 1 := by
  rw [natWord_length]; have := nbl_lt h hk; omega

theorem intWord_len_le (z : ℤ) (k : ℕ) (h : z.natAbs < 2 ^ k) (hk : 1 ≤ k) : (Interfaces.intWord z).length ≤ 2 * k + 4 := by
  unfold Interfaces.intWord
  rw [List.length_append]
  have h1 := natWord_len_le z.natAbs k h hk
  have h2 : (natWord (if z < 0 then 1 else 0)).length ≤ 3 := by
    rw [natWord_length]
    have := nbl_small (if z < 0 then 1 else 0) (by split_ifs <;> omega) 1 le_rfl
    omega
  omega

section R
variable {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT)

theorem sysWord_len (y : Cells r.wt.I) (part : Option Bool) (κ : Role r.c × Fin r.p.J → ℤ) :
    (sysWord (sysOf r.c r.p r.wt y κ part)).length ≤ 2 ^ 12 * (r.c.n + 1) ^ 9 := by
  have hs := spec_r r
  have hW : r.c.W ≤ 2 * r.c.n ^ 4 := r.adm.2.2.2.2.2.2.1
  have h4 := n4p r.c.n
  have hrc := rc12 r.c
  set Y := r.c.n + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  rw [sysWord_eq]
  simp only [List.length_append, List.length_nil, Nat.add_zero]
  -- the point count
  have hN0 := lenR_le r.c r.p r.wt y κ 0
  have hN1 := lenR_le r.c r.p r.wt y κ 1
  have hPB : 2 * r.c.W + 1 ≤ 2 ^ (4 * r.c.n + 3) := by omega
  have hNN : lenR r.c r.p r.wt y κ 0 * lenR r.c r.p r.wt y κ 1 < 2 ^ (8 * r.c.n + 7) := by
    calc _ ≤ 2 ^ (4 * r.c.n + 3) * 2 ^ (4 * r.c.n + 3) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 ^ (8 * r.c.n + 6) := by rw [← pow_add]; ring_nf
      _ < 2 ^ (8 * r.c.n + 7) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have l1 := natWord_len_le _ _ hNN (by omega)
  -- the points
  have hpt : ∀ a < lenR r.c r.p r.wt y κ 0, ∀ b < lenR r.c r.p r.wt y κ 1,
      (ptWn (roleCount r.c.kind) (loR r.c r.p r.wt y κ 0).toNat (-loR r.c r.p r.wt y κ 0).toNat
        (loR r.c r.p r.wt y κ 1).toNat (-loR r.c r.p r.wt y κ 1).toNat a b).length ≤ 16 * r.c.n + 25 := by
    intro a ha b hb
    have hz : ∀ (q : ℕ) (hq : q < roleCount r.c.kind) (a' : ℕ), a' < lenR r.c r.p r.wt y κ q →
        (Interfaces.intWord (zOf ((loR r.c r.p r.wt y κ q).toNat + a') (-loR r.c r.p r.wt y κ q).toNat)).length ≤
          8 * r.c.n + 10 := by
      intro q hq a' ha'
      have h1 := coord_abs r.c r.p r.wt y κ q hq a' ha'
      have e : zOf ((loR r.c r.p r.wt y κ q).toNat + a') (-loR r.c r.p r.wt y κ q).toNat = loR r.c r.p r.wt y κ q + a' := by
        unfold zOf; omega
      rw [e]
      have := intWord_len_le (loR r.c r.p r.wt y κ q + a') (4 * r.c.n + 3) (by omega) (by omega)
      omega
    unfold ptWn
    have hd : (natWord (roleCount r.c.kind)).length ≤ 5 := by
      rw [natWord_length]; have := nbl_le_self (roleCount r.c.kind); have := roleCount_le_two r.c
      have : natBitLength (roleCount r.c.kind) ≤ 2 := by
        rcases hrc with h | h <;> rw [h] <;> decide
      omega
    have h0 := hz 0 (by omega) a ha
    simp only [List.length_append]
    split_ifs with h2
    · have h1' := hz 1 h2 b hb; omega
    · simp only [List.length_nil, Nat.add_zero]; omega
  have lP := flatMap_range_len (lenR r.c r.p r.wt y κ 0) (lenR r.c r.p r.wt y κ 1 * (16 * r.c.n + 25))
    (rowPts (roleCount r.c.kind) (loR r.c r.p r.wt y κ 0).toNat (-loR r.c r.p r.wt y κ 0).toNat
      (loR r.c r.p r.wt y κ 1).toNat (-loR r.c r.p r.wt y κ 1).toNat (lenR r.c r.p r.wt y κ 1))
    (fun a ha => flatMap_range_len _ _ _ (fun b hb => hpt a ha b hb))
  -- the rows
  have hqn : ∀ q ∈ r.p.primes.sort (· ≤ ·), q ≤ r.c.n := fun q hq =>
    (primes_le hs q ((Finset.mem_sort _).mp hq)).trans (P_le_n r.c r.p hs)
  have hrow : ∀ q ∈ r.p.primes.sort (· ≤ ·), (rowsS0W (roleCount r.c.kind) (Jf r.c r.p r.wt y κ part) q).length ≤
      q * qBn q (roleCount r.c.kind) * (10 * r.c.n + 15) := by
    intro q hq
    have hqn' := hqn q hq
    unfold rowsS0W
    rw [mul_assoc]
    refine flatMap_range_len _ _ _ (fun s0 hs0 => flatMap_range_len _ _ _ (fun s1 hs1 => ?_))
    have hs1q : s1 ≤ r.c.n := by unfold qBn at hs1; split_ifs at hs1 <;> omega
    have hJ := jointCount_le r.c r.p r.wt y q part κ (fun r' => ((([s0, s1].take (roleCount r.c.kind)).getD r'.val 0 : ℕ) : ℤ))
    have l2 : (natWord (Jf r.c r.p r.wt y κ part q s0 s1)).length ≤ 2 * (r.c.n + 1) + 1 :=
      natWord_len_le _ _ (lt_of_le_of_lt hJ (Nat.pow_lt_pow_right (by norm_num) (by omega))) (by omega)
    have nq : ∀ v, v ≤ r.c.n → (natWord v).length ≤ 2 * r.c.n + 3 := fun v hv => by
      rw [natWord_length]; have := nbl_le_self v; omega
    unfold rowWn
    simp only [List.length_append]
    have := nq q hqn'
    have := nq (roleCount r.c.kind) (by have := roleCount_le_two r.c; have := r.adm.1; omega)
    have := nq s0 (by omega)
    split_ifs
    · have := nq s1 hs1q; omega
    · simp only [List.length_nil, Nat.add_zero]; omega
  have lR : ((r.p.primes.sort (· ≤ ·)).flatMap (rowsS0W (roleCount r.c.kind) (Jf r.c r.p r.wt y κ part))).length ≤
      r.c.n ^ 3 * (10 * r.c.n + 15) := by
    rw [List.length_flatMap]
    calc _ ≤ ((r.p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount r.c.kind) * (10 * r.c.n + 15)).sum :=
          List.sum_le_sum (fun q hq => hrow q hq)
      _ = ((r.p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount r.c.kind)).sum * (10 * r.c.n + 15) := by
          rw [List.sum_map_mul_right]
      _ ≤ _ := Nat.mul_le_mul_right _ (qq_sum r.c r.p hs)
  have hcnt := qq_sum r.c r.p hs
  have l3 := natWord_len_le _ (3 * r.c.n + 1) (lt_of_le_of_lt hcnt (n3p r.c.n)) (by omega)
  -- the polynomial
  have p1 : lenR r.c r.p r.wt y κ 0 * (lenR r.c r.p r.wt y κ 1 * (16 * r.c.n + 25)) ≤ 625 * Y ^ 9 := by
    have q0 : lenR r.c r.p r.wt y κ 0 ≤ 5 * Y ^ 4 := by
      have : r.c.n ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY1; omega
    have q1 : lenR r.c r.p r.wt y κ 1 ≤ 5 * Y ^ 4 := by
      have : r.c.n ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY1; omega
    calc _ ≤ 5 * Y ^ 4 * (5 * Y ^ 4 * (25 * Y)) := Nat.mul_le_mul q0 (Nat.mul_le_mul q1 (by omega))
      _ = 625 * Y ^ 9 := by ring
  have p2 : r.c.n ^ 3 * (10 * r.c.n + 15) ≤ 15 * Y ^ 9 := by
    have : r.c.n ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc _ ≤ Y ^ 3 * (15 * Y) := Nat.mul_le_mul this (by omega)
      _ = 15 * Y ^ 4 := by ring
      _ ≤ 15 * Y ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by norm_num))
  have p3 : Y ≤ Y ^ 9 := by simpa using Nat.pow_le_pow_right hY1 (show 1 ≤ 9 by norm_num)
  omega

end R

end NearCubicGates.Close.CellsPack
