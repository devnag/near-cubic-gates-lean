import Proof.Gates.Succinct.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

theorem root_exists (G n : ℕ) : ∃ ν, n < (ν + 1) ^ (G + 2) :=
  ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_self_pow (by omega) _)⟩

/-- `⌊n^{1/(G+2)}⌋` (paper lem:succinct-verifier, stage (1)). -/
noncomputable def rootOf (G n : ℕ) : ℕ := Nat.find (root_exists G n)

theorem lt_root_succ_pow (G n : ℕ) : n < (rootOf G n + 1) ^ (G + 2) := Nat.find_spec (root_exists G n)

theorem pow_le_of_lt_root (G n ν : ℕ) (h : ν < rootOf G n) : (ν + 1) ^ (G + 2) ≤ n := by
  have := Nat.find_min (root_exists G n) h
  omega

theorem rootOf_pow (G ν : ℕ) : rootOf G (ν ^ (G + 2)) = ν := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.pow_lt_pow_left (Nat.lt_succ_self ν) (by omega))
  · by_contra h
    have hlt := Nat.lt_of_not_le h
    have h1 := lt_root_succ_pow G (ν ^ (G + 2))
    have h2 : (rootOf G (ν ^ (G + 2)) + 1) ^ (G + 2) ≤ ν ^ (G + 2) := Nat.pow_le_pow_left (by omega) _
    omega

theorem rootOf_le (G n : ℕ) : rootOf G n ≤ n :=
  Nat.find_min' _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_self_pow (by omega) _))

theorem rootOf_pow_le (G n : ℕ) (h : 1 ≤ rootOf G n) : rootOf G n ^ (G + 2) ≤ n := by
  have := pow_le_of_lt_root G n (rootOf G n - 1) (by omega)
  rwa [Nat.sub_add_cancel h] at this

theorem pow_le_iff_lt_root (G n k : ℕ) : (k + 1) ^ (G + 2) ≤ n ↔ k < rootOf G n := by
  constructor
  · intro h
    by_contra h'
    have h1 := lt_root_succ_pow G n
    have h2 : (rootOf G n + 1) ^ (G + 2) ≤ (k + 1) ^ (G + 2) := Nat.pow_le_pow_left (by omega) _
    omega
  · exact pow_le_of_lt_root G n k

end NearCubicGates.Close.Succinct
