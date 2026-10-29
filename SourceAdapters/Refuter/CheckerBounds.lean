import SourceAdapters.Refuter.CodeTable

/-!
# Size bounds on the code (input 7, F01 machine layer, part 7)

Every offset the checking machine computes stays inside `VerifierEncoding.code v`, and every
quantity it keeps in a register (`t`, `wd`, `2^t`, `2^wd`, a control, an entry index) is at most
`|code(M)|` (or twice it). These make the per-step cost `O(|code(M)|^2)`, the `b_M` of proof of `cor:framed-refuter`.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierEncoding

set_option autoImplicit false

variable (v : RepairOrdinary.Verifier)

theorem stateCount_pos : 0 < v.stateCount :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) v.machine.start.isLt

theorem block_length (j : Fin v.stateCount) :
    (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
      actionCode (cWd v) (v.machine.rule j (fun tape => mask.val.testBit tape.val))).flatten.length =
      cBs v := by
  rw [List.length_flatten, List.map_ofFn]
  have : (List.length ∘ fun mask : Fin (2 ^ v.tapeCount) =>
      actionCode (cWd v) (v.machine.rule j (fun tape => mask.val.testBit tape.val))) =
      fun _ => cEw v := by funext i; simp [actionCode_length, cEw]
  rw [this, List.sum_ofFn]
  simp [cBs]

theorem code_length : (VerifierEncoding.code v).length = cAt v + v.stateCount * cBs v := by
  rw [code_split, List.length_append, header_length, List.length_flatten, List.map_ofFn]
  have : (List.length ∘ fun i : Fin v.stateCount =>
      (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
        actionCode (cWd v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten) =
      fun _ => cBs v := by funext i; exact block_length v i
  rw [this, List.sum_ofFn]
  simp

theorem cEw_pos : 1 ≤ cEw v := by unfold cEw; omega

theorem entry_end_le (q : ℕ) (hq : q < v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount) :
    cAt v + q * cBs v + mk * cEw v + cEw v ≤ (VerifierEncoding.code v).length := by
  rw [code_length]
  have h1 : mk * cEw v + cEw v ≤ cBs v := by
    unfold cBs
    have : (mk + 1) * cEw v ≤ 2 ^ v.tapeCount * cEw v := Nat.mul_le_mul_right _ hmk
    nlinarith
  have h2 : (q + 1) * cBs v ≤ v.stateCount * cBs v := Nat.mul_le_mul_right _ hq
  nlinarith

theorem hb_le_at : cHb v ≤ cAt v := by unfold cAt; omega

theorem at_le_code : cAt v ≤ (VerifierEncoding.code v).length := by rw [code_length]; omega

theorem hb_le_code : cHb v ≤ (VerifierEncoding.code v).length :=
  (hb_le_at v).trans (at_le_code v)

theorem tapeCount_le_code : v.tapeCount ≤ (VerifierEncoding.code v).length :=
  le_trans (by unfold cHb; omega) (hb_le_code v)

theorem stateCount_le_code : v.stateCount ≤ (VerifierEncoding.code v).length :=
  le_trans (by unfold cHb; omega) (hb_le_code v)

theorem wd_le_code : cWd v ≤ (VerifierEncoding.code v).length :=
  le_trans (by unfold cHb; omega) (hb_le_code v)

theorem pow_t_le_code : 2 ^ v.tapeCount ≤ (VerifierEncoding.code v).length := by
  rw [code_length]
  have h1 : 2 ^ v.tapeCount ≤ cBs v := by
    unfold cBs; exact Nat.le_mul_of_pos_right _ (cEw_pos v)
  have h2 : cBs v ≤ v.stateCount * cBs v := Nat.le_mul_of_pos_left _ (stateCount_pos v)
  omega

theorem pow_wd_le : 2 ^ cWd v ≤ 2 * v.stateCount := by
  unfold cWd natBitLength
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp (stateCount_pos v))
  omega

theorem pow_wd_le_code : 2 ^ cWd v ≤ 2 * (VerifierEncoding.code v).length :=
  (pow_wd_le v).trans (by have := stateCount_le_code v; omega)

theorem ctl_lt_pow (q : Fin v.stateCount) : q.val < 2 ^ cWd v := by
  unfold cWd natBitLength
  exact lt_of_lt_of_le q.isLt (Nat.lt_pow_succ_log_self (by norm_num) _).le

end NearCubicGates.Adapters.Refuter
