import SourceAdapters.Compile.CNFMainB

/-!
# The printer, part C: sizes

proof of `lem:multitape-refuter`; proof of `cor:framed-refuter` (the construction time is a polynomial whose degree does not depend on the
machine): the request's generator data satisfy `GD.Ok` with `Λ = 4·measure²` (`reqGD_ok`), the round-template
cost is at most `1000·Λ⁶` (`tmplCost_le`), and the cell width `2^(c·natBitLength |word|)·a` is at least
`a·measure^c` (`width_ge`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.RepairOrdinary
  NearCubicWires.RepairSource.VerifierEncoding
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem counts_le_code (v : Verifier) : v.tapeCount + v.stateCount + 2 ≤ (code v).length := by
  rw [code_length]; unfold codeO3 codeO2 codeO1; omega

theorem natBitLength_pow_le (s : ℕ) (hs : 1 ≤ s) : 2 ^ natBitLength s ≤ 2 * s := by
  unfold natBitLength
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show s ≠ 0 by omega)
  omega

theorem reqGD_ok (r : CNFCompilationRequest) : (reqGD r).Ok (4 * r.measure ^ 2) := by
  set m := r.measure with hm
  have hmdef : m = (code r.verifier).length + r.input.length + r.witnessLength + r.fuel + natBitLength r.high + 1 :=
    rfl
  have hc := counts_le_code r.verifier
  have hpt := pow_tape_le_code r.verifier
  have hs1 : 1 ≤ r.verifier.stateCount := Nat.pos_of_ne_zero (fun h => by
    have := r.verifier.machine.start.isLt; omega)
  have hm1 : m ≤ m ^ 2 := by nlinarith
  have hw := natBitLength_pow_le _ hs1
  have hst := r.verifier.machine.start.isLt
  refine ⟨codeBits_length r.verifier, by simp [reqGD], by have := r.verifier.twoTapes; simp [reqGD]; omega,
    codeBits_le_one r.verifier, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reqGD, codeBits, List.length_map]; omega
  · simp only [reqGD, List.length_map]; omega
  · simp only [GD.W, reqGD, windowBits]
    have ht : r.verifier.tapeCount ≤ m := by omega
    have hf : r.fuel + 1 ≤ m := by omega
    have : r.verifier.tapeCount * (r.fuel + 1) ≤ m * m := Nat.mul_le_mul ht hf
    nlinarith
  · simp only [reqGD]; omega
  · simp only [reqGD, codeW]; omega
  · simp only [reqGD]; omega
  · simp only [reqGD]; omega

/-! ## The template cost -/

theorem tmplCost_le (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) : tmplCost D Λ ≤ 1000 * Λ ^ 6 := by
  have ht := D.t_le Λ hOk
  have hs := D.s_le Λ hOk
  have hw := D.width_le Λ hOk
  have hM := hOk.MΛ
  have hW := hOk.WΛ
  have h1 : 1 ≤ Λ := le_trans Nat.one_le_two_pow hM
  have p2 : Λ ≤ Λ ^ 2 := Nat.le_self_pow (by norm_num) Λ
  have p3 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have p4 : Λ ^ 3 ≤ Λ ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p5 : Λ ^ 4 ≤ Λ ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have p6 : Λ ^ 5 ≤ Λ ^ 6 := Nat.pow_le_pow_right h1 (by norm_num)
  have hf : fitsCost D Λ ≤ 150 * Λ ^ 3 := by
    unfold fitsCost
    calc D.t * ((D.width * ((14 * Λ + 80) + 4) + D.width * 5 + 12) + 4) + D.t * 5 + 12
        ≤ Λ * ((Λ * ((14 * Λ + 80) + 4) + Λ * 5 + 12) + 4) + Λ * 5 + 12 := by gcongr
      _ ≤ 150 * Λ ^ 3 := by ring_nf; nlinarith [h1, p2, p3]
  have hh : headCost D Λ ≤ 120 * Λ ^ 2 := by
    unfold headCost
    calc D.width * ((14 * Λ + 80) + 4) + D.width * 5 + 12 ≤ Λ * ((14 * Λ + 80) + 4) + Λ * 5 + 12 := by gcongr
      _ ≤ 120 * Λ ^ 2 := by ring_nf; nlinarith [h1, p2]
  have ha : actCost D Λ ≤ 330 * Λ ^ 2 := by unfold actCost; ring_nf; nlinarith [hh, h1, p2]
  have hv : valCost D Λ ≤ 560 * Λ ^ 3 := by unfold valCost; nlinarith [hf, ha, h1, p2, p3]
  have hb : bodyCost D Λ ≤ 720 * Λ ^ 3 := by unfold bodyCost; ring_nf; nlinarith [hv, h1, p2, p3]
  have htr : transCost D Λ ≤ 770 * Λ ^ 5 := by
    unfold transCost
    calc D.s * ((2 ^ D.t * (bodyCost D Λ + 4) + 2 ^ D.t * 5 + 12) + 4) + D.s * 5 + 12
        ≤ Λ * ((Λ * (720 * Λ ^ 3 + 4) + Λ * 5 + 12) + 4) + Λ * 5 + 12 := by gcongr
      _ ≤ 770 * Λ ^ 5 := by ring_nf; nlinarith [h1, p2, p3, p4, p5]
  unfold tmplCost
  calc D.W * ((transCost D Λ + 1 + 1) + 4) + 4 + 1 + 1 ≤ Λ * ((770 * Λ ^ 5 + 1 + 1) + 4) + 4 + 1 + 1 := by gcongr
    _ ≤ 1000 * Λ ^ 6 := by ring_nf; nlinarith [h1, p2, p3, p4, p5, p6]

/-! ## The width -/

theorem measure_le_word (r : CNFCompilationRequest) : r.measure ≤ r.word.length := by
  have hbits : natBitLength r.high ≤ r.high.bits.length + 1 := by
    rw [Nat.size_eq_bits_len]
    unfold natBitLength
    rcases Nat.eq_zero_or_pos r.high with h | h
    · simp [h]
    · have := Nat.lt_size_self r.high
      have := Nat.log_lt_of_lt_pow (b := 2) (by omega) this
      omega
  simp only [CNFCompilationRequest.word, List.length_append, frame_length, List.length_replicate,
    CNFCompilationRequest.measure]
  omega

theorem width_ge (a c : ℕ) (r : CNFCompilationRequest) :
    a * r.measure ^ c ≤ (ctxOf noCallee (cnfSz a c) (requestEntryWord r)).Wd := by
  show a * r.measure ^ c ≤ 2 ^ (c * leadOnes (requestEntryWord r)) * a
  rw [requestEntryWord, Proximity.LengthPrefix.wrapped_leadOnes, mul_comm _ a, pow_mul']
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have h1 := measure_le_word r
  have h2 : r.word.length < 2 ^ natBitLength r.word.length := by
    unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) _
  omega

end NearCubicGates.Adapters.Compile
