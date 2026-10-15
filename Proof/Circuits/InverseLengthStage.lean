import Proof.Circuits.InverseSourceIndexScan
import Proof.Circuits.SelectorDrivenLengthStage

/-!
# The inverse schedule's length program, executed

`InverseSourceIndexScan` proved the four-register additions-only scan computes
`RecoveryScheduleEnvelope.inverseSourceIndex` (`scanIter_eq_inverseSourceIndex`).
This module transcribes that scan into an `NPOracleProgram` (§2), then mirrors
`SelectorDrivenLengthStage`'s fixed pipeline with the extra scan stage (§3) to
discharge `SourceDrivenNumeralBank.InverseScheduledLengthRuns` and close the
inverse selector-driven bank with no hypothesis.

The scan program is one padded loop so every trajectory through it costs exactly
eighteen instructions per iteration — the uniform fuel `18·i + 4` the run lemma
charges.  Its register ABI is `r2=i`, `r3=j`, `r4=c`, `r5=q`, `r6=prod`,
`r7=arg`, `r8=K=k+2`, `r9=code`, with `r10..r15` scratch.
-/

namespace NearCubicWires.InverseLengthStage

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSourceIndexScan
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Reachable-value bound -/

/-- Every register value the scan holds is below this bound. -/
def scanBound (k : ℕ) : ℕ := 4 * (k + 4)

private theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

private theorem two_pow_clog_lt (m : ℕ) (hm : 1 ≤ m) :
    2 ^ Nat.clog 2 m < 2 * m := by
  have h1 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst m; decide
  · have hclogpos : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    have hpred : 2 ^ (Nat.clog 2 m - 1) < m :=
      Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    calc 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
            rw [← pow_succ']; congr 1; omega
      _ < 2 * m := by omega

private theorem pair_le_pair_left {a a' b : ℕ} (h : a ≤ a') :
    Nat.pair a b ≤ Nat.pair a' b := by
  unfold Nat.pair; split_ifs <;> nlinarith

/-- The tight register bounds a reachable scan state guarantees. -/
private theorem scanState_bounds {k : ℕ} {s : ScanState}
    (hvalid : ScanValid s) (hjk : s.j ≤ k + 1) :
    s.c ≤ k + 4 ∧ s.q ≤ 2 * (k + 4) ∧ s.arg ≤ k + 4 ∧ s.arg ≤ s.q := by
  obtain ⟨hc, hq, _, harg⟩ := hvalid
  have hcle : s.c ≤ s.j + 3 := by rw [hc]; exact clog_le_self _
  have hqlt : s.q < 2 * (s.j + 3) := by
    rw [hq, hc]; exact two_pow_clog_lt _ (by omega)
  have hargq : s.arg ≤ s.q := by rw [hq, hc, harg]; exact Nat.le_pow_clog (by norm_num) _
  exact ⟨by omega, by omega, by omega, hargq⟩

/-- The functional scan is the iterate of `scanStep`. -/
theorem scanIter_eq_iterate (K n : ℕ) (s : ScanState) :
    scanIter K n s = (scanStep K)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ m ih => rw [scanIter, ih]; exact (Function.iterate_succ_apply' _ _ _).symm

/-! ## 2. The scan program -/

/-- **The inverse source-index scan.**  One padded loop; ABI in the header. -/
def inverseSourceIndexProgram : NPOracleProgram :=
  [ .unpairRight 0 9 1        -- 0  r9 := code
  , .unpairLeft 0 8 2         -- 1  r8 := k
  , .copy 8 2 3               -- 2  r2 := k
  , .increment 2 4            -- 3  r2 := k+1 = i
  , .increment 8 5            -- 4  r8 := k+1
  , .increment 8 6            -- 5  r8 := k+2 = K
  , .set 3 0 7                -- 6  j := 0
  , .set 4 2 8                -- 7  c := 2
  , .set 5 4 9                -- 8  q := 4
  , .set 6 2 10               -- 9  prod := 2
  , .set 7 3 11               -- 10 arg := 3
  , .branchZero 2 41 12       -- 11 LOOP
  , .decrement 2 13           -- 12 i--
  , .subtract 5 7 10 14       -- 13 t1 := q - arg
  , .branchZero 10 22 15      -- 14 cross->22, nocross->15
  , .copy 4 12 16             -- 15 NOCROSS cNext := c
  , .copy 5 13 17             -- 16 qNext := q
  , .add 6 4 11 18            -- 17 prodNext := prod + c
  , .set 15 0 19              -- 18 pad
  , .set 15 0 20              -- 19 pad
  , .set 15 0 21              -- 20 pad
  , .set 15 0 29              -- 21 pad -> DECIDE
  , .copy 4 12 23             -- 22 CROSS cNext := c
  , .increment 12 24          -- 23 cNext := c+1
  , .add 5 5 13 25            -- 24 qNext := q+q
  , .copy 7 14 26             -- 25 r14 := arg
  , .decrement 14 27          -- 26 r14 := arg-1
  , .add 6 4 11 28            -- 27 r11 := prod + c
  , .add 11 14 11 29          -- 28 prodNext -> DECIDE
  , .subtract 11 8 14 30      -- 29 DECIDE t2 := prodNext - K
  , .branchZero 14 31 36      -- 30 commit->31, freeze->36
  , .copy 11 6 32             -- 31 COMMIT prod := prodNext
  , .copy 12 4 33             -- 32 c := cNext
  , .copy 13 5 34             -- 33 q := qNext
  , .increment 3 35           -- 34 j := j+1
  , .increment 7 11           -- 35 arg := arg+1 -> LOOP
  , .set 15 0 37              -- 36 FREEZE pad
  , .set 15 0 38              -- 37 pad
  , .set 15 0 39              -- 38 pad
  , .set 15 0 40              -- 39 pad
  , .set 15 0 11              -- 40 pad -> LOOP
  , .increment 3 42           -- 41 EXIT j := j+1
  , .pair 3 9 0 43            -- 42 r0 := pair (j+1) code
  , .halt 0                   -- 43
  ]

@[simp] theorem inverseSourceIndexProgram_oracleFree :
    OracleFree inverseSourceIndexProgram := by rfl

set_option maxHeartbeats 1600000 in
-- The loop threads eighteen instructions across four paths per iteration; the
-- register write-chains push the default heartbeat budget.
/-- **The scan loop, executed.**  From a register-encoded reachable state at the
loop head, the padded loop returns the fully-scanned candidate plus one, beside
the retained code, after the uniform fuel `18·i + 4`. -/
theorem run_scanLoop (k code maximumBits : ℕ)
    (hbv : ∀ v, v ≤ scanBound k → natBitLength v ≤ maximumBits)
    (hbo : ∀ v, v ≤ k + 2 → natBitLength (Nat.pair v code) ≤ maximumBits) :
    ∀ (i : ℕ) (s : ScanState) (state : NPOracleState),
      state.pc = 11 → state.registers 2 = i → state.registers 3 = s.j →
      state.registers 4 = s.c → state.registers 5 = s.q →
      state.registers 6 = s.prod → state.registers 7 = s.arg →
      state.registers 8 = k + 2 → state.registers 9 = code →
      ScanValid s → s.prod ≤ k + 2 → s.j + i ≤ k + 1 →
      runNPOracleProgram inverseSourceIndexProgram maximumBits (18 * i + 4)
          state =
        some (Nat.pair (((scanStep (k + 2))^[i] s).j + 1) code) := by
  have hb0 : natBitLength 0 ≤ maximumBits := hbv 0 (Nat.zero_le _)
  intro i
  induction i with
  | zero =>
      intro s state hpc h2 h3 h4 h5 h6 h7 h8 h9 _hvalid _hprod hji
      have hjout : s.j + 1 ≤ k + 2 := by omega
      have hjb : s.j + 1 ≤ scanBound k := by simp only [scanBound]; omega
      rw [show 18 * 0 + 4 = 3 + 1 by omega]
      rw [run_branchZero_instruction (program := inverseSourceIndexProgram)
        (register := 2) (zeroTarget := 41) (nonzeroTarget := 12) (by rfl) hpc]
      have hpc41 : (state.jump (if state.registers 2 = 0 then 41 else 12)).pc = 41 := by
        simp [NPOracleState.jump, h2]
      rw [show 3 = 2 + 1 by omega]
      rw [run_increment_instruction (register := 3) (value := s.j + 1)
        (by rfl) hpc41 (by simp [NPOracleState.jump, h3]) (hbv _ hjb)]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (left := 3) (right := 9)
        (value := Nat.pair (s.j + 1) code) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, h9]) (hbo _ hjout)]
      simp only [Function.iterate_zero, id_eq]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) (hbo _ hjout)
  | succ i' ih =>
      intro s state hpc h2 h3 h4 h5 h6 h7 h8 h9 hvalid hprod hji
      obtain ⟨hcT, hqT, hargT, hargq⟩ := scanState_bounds (k := k) hvalid (by omega)
      have hcE : s.c = Nat.clog 2 (s.j + 3) := hvalid.1
      have hqE : s.q = 2 ^ s.c := hvalid.2.1
      have hprodE : s.prod = (s.j + 1) * s.c := hvalid.2.2.1
      have hargE : s.arg = s.j + 3 := hvalid.2.2.2
      have hcrossStep := Function.iterate_succ_apply (scanStep (k + 2)) i' s
      -- Expand the uniform per-iteration fuel and thread the shared head.
      rw [show 18 * (i' + 1) + 4 =
        18 * i' + 4 + 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 by ring]
      rw [run_branchZero_instruction (program := inverseSourceIndexProgram)
        (register := 2) (pc := 11) (zeroTarget := 41) (nonzeroTarget := 12)
        (by rfl) hpc]
      rw [run_decrement_instruction (register := 2) (pc := 12) (value := i')
        (by rfl) (by simp [NPOracleState.jump, h2]) (by simp [NPOracleState.jump, h2])
        (by apply hbv; simp only [scanBound]; omega)]
      rw [run_subtract_instruction (left := 5) (right := 7) (pc := 13)
        (value := s.q - s.arg) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, h5, h7])
        (by apply hbv; simp only [scanBound]; omega)]
      by_cases hcross : s.q = s.arg
      · -- CROSS: t1 = q - arg = 0 -> 22
        have ht1 : s.q - s.arg = 0 := by omega
        have hprodNext :
            s.prod + s.c + (s.arg - 1) = inverseSourceMeasure (s.j + 1) := by
          have hbnd : s.j + 3 = 2 ^ Nat.clog 2 (s.j + 3) := by
            rw [← hcE, ← hargE, ← hqE, hcross]
          have hclog : Nat.clog 2 (s.j + 4) = Nat.clog 2 (s.j + 3) + 1 :=
            clog_succ_of_eq_pow rfl hbnd
          rw [inverseSourceMeasure_eq, show s.j + 1 + 3 = s.j + 4 from rfl,
            hprodE, hcE, hargE, hclog, show s.j + 3 - 1 = s.j + 2 from by omega]
          ring
        rw [run_branchZero_instruction (register := 10) (pc := 14)
          (zeroTarget := 22) (nonzeroTarget := 15) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [run_copy_instruction (source := 4) (destination := 12) (pc := 22)
          (value := s.c) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump, ht1])
          (by simp [NPOracleState.write, NPOracleState.jump, h4])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_increment_instruction (register := 12) (pc := 23) (value := s.c + 1)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_add_instruction (left := 5) (right := 5) (destination := 13) (pc := 24)
          (value := s.q + s.q) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h5])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_copy_instruction (source := 7) (destination := 14) (pc := 25)
          (value := s.arg) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h7])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_decrement_instruction (register := 14) (pc := 26) (value := s.arg - 1)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_add_instruction (left := 6) (right := 4) (destination := 11) (pc := 27)
          (value := s.prod + s.c) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h6, h4])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_add_instruction (left := 11) (right := 14) (destination := 11) (pc := 28)
          (value := s.prod + s.c + (s.arg - 1)) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_subtract_instruction (left := 11) (right := 8) (destination := 14)
          (pc := 29) (value := (s.prod + s.c + (s.arg - 1)) - (k + 2)) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h8])
          (by apply hbv; simp only [scanBound]; omega)]
        by_cases hadv : s.prod + s.c + (s.arg - 1) ≤ k + 2
        · -- COMMIT
          have ht2 : (s.prod + s.c + (s.arg - 1)) - (k + 2) = 0 := by omega
          have hmeasure : inverseSourceMeasure (s.j + 1) ≤ k + 2 := by
            rw [← hprodNext]; exact hadv
          have hvn := ((scanStep_run (K := k + 2) hvalid).1 hmeasure).1
          have hstepEq : scanStep (k + 2) s =
              ⟨s.j + 1, s.c + 1, s.q + s.q, s.prod + s.c + (s.arg - 1),
                s.arg + 1⟩ := by rw [scanStep_cross hcross, if_pos hadv]
          rw [hstepEq] at hvn
          rw [run_branchZero_instruction (register := 14) (pc := 30)
            (zeroTarget := 31) (nonzeroTarget := 36) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [run_copy_instruction (source := 11) (destination := 6) (pc := 31)
            (value := s.prod + s.c + (s.arg - 1)) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump, ht2])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_copy_instruction (source := 12) (destination := 4) (pc := 32)
            (value := s.c + 1) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_copy_instruction (source := 13) (destination := 5) (pc := 33)
            (value := s.q + s.q) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_increment_instruction (register := 3) (pc := 34) (value := s.j + 1)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump, h3])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_increment_instruction (register := 7) (pc := 35) (value := s.arg + 1)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump, h7])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [hcrossStep, hstepEq]
          refine ih ⟨s.j + 1, s.c + 1, s.q + s.q, s.prod + s.c + (s.arg - 1),
            s.arg + 1⟩ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvn ?_ ?_
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, h8]
          · simp [NPOracleState.write, NPOracleState.jump, h9]
          · change s.prod + s.c + (s.arg - 1) ≤ k + 2; exact hadv
          · change s.j + 1 + i' ≤ k + 1; omega
        · -- FREEZE
          have ht2 : ¬ (s.prod + s.c + (s.arg - 1)) - (k + 2) = 0 := by omega
          have hstepEq : scanStep (k + 2) s = s := by
            rw [scanStep_cross hcross, if_neg hadv]
          rw [run_branchZero_instruction (register := 14) (pc := 30)
            (zeroTarget := 31) (nonzeroTarget := 36) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [run_set_instruction (register := 15) (pc := 36) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump, ht2]) hb0]
          rw [run_set_instruction (register := 15) (pc := 37) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 38) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 39) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 40) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [hcrossStep, hstepEq]
          refine ih s _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvalid hprod (by omega)
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, h2]
          · simp [NPOracleState.write, NPOracleState.jump, h3]
          · simp [NPOracleState.write, NPOracleState.jump, h4]
          · simp [NPOracleState.write, NPOracleState.jump, h5]
          · simp [NPOracleState.write, NPOracleState.jump, h6]
          · simp [NPOracleState.write, NPOracleState.jump, h7]
          · simp [NPOracleState.write, NPOracleState.jump, h8]
          · simp [NPOracleState.write, NPOracleState.jump, h9]
      · -- NOCROSS: t1 = q - arg ≠ 0 -> 15
        have hlt : s.arg < s.q := lt_of_le_of_ne hargq (fun h => hcross h.symm)
        have ht1 : ¬ s.q - s.arg = 0 := by omega
        have hprodNext : s.prod + s.c = inverseSourceMeasure (s.j + 1) := by
          have hclog : Nat.clog 2 (s.j + 4) = Nat.clog 2 (s.j + 3) :=
            clog_succ_of_lt_pow (by rw [← hcE, ← hqE]; omega) rfl
          rw [inverseSourceMeasure_eq, show s.j + 1 + 3 = s.j + 4 from rfl,
            hprodE, hcE, hclog]; ring
        rw [run_branchZero_instruction (register := 10) (pc := 14)
          (zeroTarget := 22) (nonzeroTarget := 15) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [run_copy_instruction (source := 4) (destination := 12) (pc := 15)
          (value := s.c) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump, ht1])
          (by simp [NPOracleState.write, NPOracleState.jump, h4])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_copy_instruction (source := 5) (destination := 13) (pc := 16)
          (value := s.q) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h5])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_add_instruction (left := 6) (right := 4) (destination := 11) (pc := 17)
          (value := s.prod + s.c) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h6, h4])
          (by apply hbv; simp only [scanBound]; omega)]
        rw [run_set_instruction (register := 15) (pc := 18) (value := 0)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
        rw [run_set_instruction (register := 15) (pc := 19) (value := 0)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
        rw [run_set_instruction (register := 15) (pc := 20) (value := 0)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
        rw [run_set_instruction (register := 15) (pc := 21) (value := 0)
          (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
        rw [run_subtract_instruction (left := 11) (right := 8) (destination := 14)
          (pc := 29) (value := (s.prod + s.c) - (k + 2)) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump, h8])
          (by apply hbv; simp only [scanBound]; omega)]
        by_cases hadv : s.prod + s.c ≤ k + 2
        · -- COMMIT
          have ht2 : (s.prod + s.c) - (k + 2) = 0 := by omega
          have hmeasure : inverseSourceMeasure (s.j + 1) ≤ k + 2 := by
            rw [← hprodNext]; exact hadv
          have hvn := ((scanStep_run (K := k + 2) hvalid).1 hmeasure).1
          have hstepEq : scanStep (k + 2) s =
              ⟨s.j + 1, s.c, s.q, s.prod + s.c, s.arg + 1⟩ := by
            rw [scanStep_nocross hcross, if_pos hadv]
          rw [hstepEq] at hvn
          rw [run_branchZero_instruction (register := 14) (pc := 30)
            (zeroTarget := 31) (nonzeroTarget := 36) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [run_copy_instruction (source := 11) (destination := 6) (pc := 31)
            (value := s.prod + s.c) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump, ht2])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_copy_instruction (source := 12) (destination := 4) (pc := 32)
            (value := s.c) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_copy_instruction (source := 13) (destination := 5) (pc := 33)
            (value := s.q) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_increment_instruction (register := 3) (pc := 34) (value := s.j + 1)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump, h3])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [run_increment_instruction (register := 7) (pc := 35) (value := s.arg + 1)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
            (by simp [NPOracleState.write, NPOracleState.jump, h7])
            (by apply hbv; simp only [scanBound]; omega)]
          rw [hcrossStep, hstepEq]
          refine ih ⟨s.j + 1, s.c, s.q, s.prod + s.c, s.arg + 1⟩ _
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvn ?_ ?_
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, h8]
          · simp [NPOracleState.write, NPOracleState.jump, h9]
          · change s.prod + s.c ≤ k + 2; exact hadv
          · change s.j + 1 + i' ≤ k + 1; omega
        · -- FREEZE
          have ht2 : ¬ (s.prod + s.c) - (k + 2) = 0 := by omega
          have hstepEq : scanStep (k + 2) s = s := by
            rw [scanStep_nocross hcross, if_neg hadv]
          rw [run_branchZero_instruction (register := 14) (pc := 30)
            (zeroTarget := 31) (nonzeroTarget := 36) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [run_set_instruction (register := 15) (pc := 36) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump, ht2]) hb0]
          rw [run_set_instruction (register := 15) (pc := 37) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 38) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 39) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [run_set_instruction (register := 15) (pc := 40) (value := 0)
            (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
          rw [hcrossStep, hstepEq]
          refine ih s _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvalid hprod (by omega)
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, h2]
          · simp [NPOracleState.write, NPOracleState.jump, h3]
          · simp [NPOracleState.write, NPOracleState.jump, h4]
          · simp [NPOracleState.write, NPOracleState.jump, h5]
          · simp [NPOracleState.write, NPOracleState.jump, h6]
          · simp [NPOracleState.write, NPOracleState.jump, h7]
          · simp [NPOracleState.write, NPOracleState.jump, h8]
          · simp [NPOracleState.write, NPOracleState.jump, h9]

/-- The scan program's fuel. -/
def inverseSourceIndexFuel (k : ℕ) : ℕ := 11 + (18 * (k + 1) + 4)

set_option maxHeartbeats 800000 in
-- The eleven setup instructions seed `initialScanState` before the loop head.
/-- **The scan program, executed.**  From `Nat.pair k code` the program emits
`Nat.pair (inverseSourceIndex k + 1) code`. -/
theorem run_inverseSourceIndexProgram (k code maximumBits inputLength : ℕ)
    (hbv : ∀ v, v ≤ scanBound k → natBitLength v ≤ maximumBits)
    (hbc : natBitLength code ≤ maximumBits)
    (hbo : ∀ v, v ≤ k + 2 → natBitLength (Nat.pair v code) ≤ maximumBits) :
    runNPOracleProgram inverseSourceIndexProgram maximumBits
        (inverseSourceIndexFuel k)
        (initialNPOracleState inputLength (Nat.pair k code)) =
      some (Nat.pair (inverseSourceIndex k + 1) code) := by
  have hb0 : natBitLength 0 ≤ maximumBits := hbv 0 (Nat.zero_le _)
  have hloop := run_scanLoop k code maximumBits hbv hbo (k + 1) initialScanState
  rw [inverseSourceIndexFuel,
    show 11 + (18 * (k + 1) + 4) =
      18 * (k + 1) + 4 + 1+1+1+1+1+1+1+1+1+1+1 by ring]
  rw [run_unpairRight_instruction (source := 0) (destination := 9) (pc := 0)
    (value := code) (by rfl) rfl
    (by simp [initialNPOracleState, Nat.unpair_pair]) hbc]
  rw [run_unpairLeft_instruction (source := 0) (destination := 8) (pc := 1)
    (value := k) (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      Nat.unpair_pair]) (hbv _ (by simp only [scanBound]; omega))]
  rw [run_copy_instruction (source := 8) (destination := 2) (pc := 2)
    (value := k) (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_increment_instruction (register := 2) (pc := 3) (value := k + 1)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_increment_instruction (register := 8) (pc := 4) (value := k + 1)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_increment_instruction (register := 8) (pc := 5) (value := k + 2)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_set_instruction (register := 3) (pc := 6) (value := 0)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump]) hb0]
  rw [run_set_instruction (register := 4) (pc := 7) (value := 2)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_set_instruction (register := 5) (pc := 8) (value := 4)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_set_instruction (register := 6) (pc := 9) (value := 2)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [run_set_instruction (register := 7) (pc := 10) (value := 3)
    (by rfl) (by simp [NPOracleState.write, NPOracleState.jump])
    (hbv _ (by simp only [scanBound]; omega))]
  rw [show
    ((scanStep (k + 2))^[k + 1] initialScanState).j = inverseSourceIndex k by
    rw [← scanIter_eq_iterate]; exact scanIter_eq_inverseSourceIndex k] at hloop
  refine hloop _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ initialScanState_valid ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, initialScanState]
  · simp [NPOracleState.write, NPOracleState.jump, initialScanState]
  · simp [NPOracleState.write, NPOracleState.jump, initialScanState]
  · simp [NPOracleState.write, NPOracleState.jump, initialScanState]
  · simp [NPOracleState.write, NPOracleState.jump, initialScanState]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact Nat.le_add_left 2 k
  · simp only [initialScanState]; omega

/-- A self-contained register-width bound for the scan at one frame. -/
def scanMaxBits (k code : ℕ) : ℕ :=
  natBitLength (Nat.pair (scanBound k) (Nat.pair (k + 2) code))

/-- **The scan program at a concrete frame.**  Specialises
`run_inverseSourceIndexProgram` with the width envelope discharged. -/
theorem run_inverseSourceIndexProgram_at (source code inputLength : ℕ) :
    runNPOracleProgram inverseSourceIndexProgram (scanMaxBits source code)
        (inverseSourceIndexFuel source)
        (initialNPOracleState inputLength (Nat.pair source code)) =
      some (Nat.pair (inverseSourceIndex source + 1) code) := by
  have hbig : natBitLength (Nat.pair (scanBound source)
      (Nat.pair (source + 2) code)) ≤ scanMaxBits source code := le_refl _
  refine run_inverseSourceIndexProgram source code (scanMaxBits source code)
    inputLength ?_ ?_ ?_
  · intro v hv
    exact (natBitLength_mono (le_trans hv (Nat.left_le_pair _ _))).trans hbig
  · exact (natBitLength_mono ((Nat.right_le_pair _ _).trans
      (Nat.right_le_pair _ _))).trans hbig
  · intro v hv
    exact (natBitLength_mono ((pair_le_pair_left hv).trans
      (Nat.right_le_pair _ _))).trans hbig

/-! ## 3. The inverse schedule's length program, assembled -/

/-- Extract the selected source from the selector code, retaining the request
code: `pair (pair source rest) code ↦ pair source code`. -/
def sourceExtractProgram : NPOracleProgram :=
  [ .unpairLeft 0 3 1
  , .unpairRight 0 4 2
  , .unpairLeft 3 3 3
  , .pair 3 4 0 4
  , .halt 0
  ]

@[simp] theorem sourceExtractProgram_oracleFree :
    OracleFree sourceExtractProgram := by rfl

def sourceExtractBits (source rest code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (Nat.pair source rest) code) (Nat.pair source code))

/-- **The source extractor, executed.** -/
theorem run_sourceExtractProgram (inputLength source rest code : ℕ) :
    runNPOracleProgram sourceExtractProgram (sourceExtractBits source rest code) 5
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair source rest) code)) =
      some (Nat.pair source code) := by
  have hframeBits :
      natBitLength (Nat.pair (Nat.pair source rest) code) ≤
        sourceExtractBits source rest code :=
    natBitLength_mono (le_max_left _ _)
  have houtBits : natBitLength (Nat.pair source code) ≤
      sourceExtractBits source rest code :=
    natBitLength_mono (le_max_right _ _)
  have hselBits : natBitLength (Nat.pair source rest) ≤
      sourceExtractBits source rest code :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hframeBits
  have hcodeBits : natBitLength code ≤ sourceExtractBits source rest code :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hframeBits
  have hsourceBits : natBitLength source ≤ sourceExtractBits source rest code :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hselBits
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (source := 0) (destination := 3)
    (value := Nat.pair source rest) (by rfl) rfl
    (by simp [initialNPOracleState]) hselBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (source := 0) (destination := 4)
    (value := code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcodeBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (source := 3) (destination := 3)
    (value := source) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsourceBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (left := 3) (right := 4)
    (value := Nat.pair source code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtBits

/-- The inverse schedule's executable selector at the published outer PCP. -/
noncomputable def inverseLengthSelectorProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ) :
    NPOracleProgram :=
  (inverseSchedule contracts (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseCoreAdvantagePower advantageExponent)).selector.program

/-- **The inverse schedule's length program.**  Build the selector's unary
request, run the selector, extract the selected source, apply the
`inverseSourceIndex` scan, raise two to its successor. -/
noncomputable def inverseLengthProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ) :
    NPOracleProgram :=
  linkPrograms unaryBuildProgram
    (linkPrograms
      (preserveRightProgram
        (inverseLengthSelectorProgram contracts clockDepth advantageExponent))
      (linkPrograms sourceExtractProgram
        (linkPrograms inverseSourceIndexProgram
          (preserveRightProgram binaryTwoPowProgram))))

/-- The selected source at one target. -/
noncomputable def inverseLengthSource
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  inverseSelectedSource contracts
    (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseCoreAdvantagePower advantageExponent) target

noncomputable def inverseLengthFuel
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (inverseLengthSelectorProgram contracts clockDepth advantageExponent))
      (linkPrograms sourceExtractProgram
        (linkPrograms inverseSourceIndexProgram
          (preserveRightProgram binaryTwoPowProgram))))
    (unaryBuildFuel (LanguageEvaluationRequest.length request))
    (linkFuel
      (linkPrograms sourceExtractProgram
        (linkPrograms inverseSourceIndexProgram
          (preserveRightProgram binaryTwoPowProgram)))
      (preserveRightFuel
        ((inverseSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent)).selector.budget
          (LanguageEvaluationRequest.length request)))
      (linkFuel
        (linkPrograms inverseSourceIndexProgram
          (preserveRightProgram binaryTwoPowProgram))
        5
        (linkFuel (preserveRightProgram binaryTwoPowProgram)
          (inverseSourceIndexFuel
            (inverseLengthSource contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request)))
          (preserveRightFuel
            (binaryTwoPowFuel
              (inverseSourceIndex
                (inverseLengthSource contracts clockDepth advantageExponent
                  (LanguageEvaluationRequest.length request)) + 1))))))

noncomputable def inverseLengthBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (unaryBuildBits (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        ((inverseSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent)).selector.budget
          (LanguageEvaluationRequest.length request))
        (encodeUnary (LanguageEvaluationRequest.length request))
        (LanguageEvaluationRequest.code request)
        ((inverseSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent)).output
          (LanguageEvaluationRequest.length request)).code)
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (sourceExtractBits
          (inverseLengthSource contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))
          (Nat.pair
            ((inverseSchedule contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent)).output
              (LanguageEvaluationRequest.length request)).nextSource
            (Nat.pair
              ((inverseSchedule contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent)).output
                (LanguageEvaluationRequest.length request)).core
              ((inverseSchedule contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent)).output
                (LanguageEvaluationRequest.length request)).nextCore))
          (LanguageEvaluationRequest.code request))
        (occurrenceStageBits (LanguageEvaluationRequest.length request)
          (scanMaxBits
            (inverseLengthSource contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request))
            (LanguageEvaluationRequest.code request))
          (preserveRightBits
            (binaryTwoPowBits
              (inverseSourceIndex
                (inverseLengthSource contracts clockDepth advantageExponent
                  (LanguageEvaluationRequest.length request)) + 1))
            (inverseSourceIndex
              (inverseLengthSource contracts clockDepth advantageExponent
                (LanguageEvaluationRequest.length request)) + 1)
            (LanguageEvaluationRequest.code request)
            (2 ^
              (inverseSourceIndex
                (inverseLengthSource contracts clockDepth advantageExponent
                  (LanguageEvaluationRequest.length request)) + 1))))))

set_option maxHeartbeats 800000 in
-- The five-stage linked pipeline elaborates one deeply nested link term.
/-- **The inverse schedule's length program, executed.** -/
theorem run_inverseLengthProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) (input : BitInput target) :
    runNPOracleProgram
        (inverseLengthProgram contracts clockDepth advantageExponent)
        (inverseLengthBits contracts clockDepth advantageExponent ⟨target, input⟩)
        (inverseLengthFuel contracts clockDepth advantageExponent ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (Nat.pair
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (encodeBitInput input)) := by
  set schedule := inverseSchedule contracts
    (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseCoreAdvantagePower advantageExponent) with hschedule
  set code := encodeBitInput input with hcode
  set source := (schedule.output target).source with hsource
  set idx := inverseSourceIndex source with hidx
  have hlength :
      (2 : ℕ) ^ (idx + 1) =
        inverseScheduleLength contracts clockDepth advantageExponent target :=
    rfl
  refine Eq.trans ?_ (congrArg (fun value => some (Nat.pair value code)) hlength)
  exact run_occurrenceStage
    (run_unaryBuildProgram target code)
    (run_occurrenceStage
      (run_preserveRightProgram
        (inverseLengthSelectorProgram contracts clockDepth advantageExponent)
        target (schedule.selector.budget target) (schedule.selector.budget target)
        (encodeUnary target) code (schedule.output target).code
        (schedule.run_selector target))
      (run_occurrenceStage
        (run_sourceExtractProgram target source
          (Nat.pair (schedule.output target).nextSource
            (Nat.pair (schedule.output target).core
              (schedule.output target).nextCore))
          code)
        (run_occurrenceStage
          (run_inverseSourceIndexProgram_at source code target)
          (run_preserveRightProgram binaryTwoPowProgram target
            (binaryTwoPowBits (idx + 1)) (binaryTwoPowFuel (idx + 1))
            (idx + 1) code (2 ^ (idx + 1))
            (run_binaryTwoPowProgram target (idx + 1)
              (binaryTwoPowBits (idx + 1)) (le_refl _))))))

/-! ## 4. `InverseScheduledLengthRuns`, discharged -/

/-- **The inverse schedule's residual is a theorem.**  With `run_inverseLengthProgram`
the obligation `SourceDrivenNumeralBank` left is met with no `hdiagonal`. -/
theorem inverse_scheduledLengthRuns
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ) :
    InverseScheduledLengthRuns contracts clockDepth advantageExponent
      (inverseLengthProgram contracts clockDepth advantageExponent)
      (inverseLengthBits contracts clockDepth advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent) :=
  fun target input =>
    run_inverseLengthProgram contracts clockDepth advantageExponent target input

/-- **The inverse schedule's selector-driven bank, closed.**  Composing the
length supplier with `run_inverseSelectorDrivenBankProgram` emits the inverse
chain's own frame at every request with no hypothesis — the twin of
`SelectorDrivenLengthStage.run_fixedSelectorBank_closed`, and the last piece of
the diagonal repair on the inverse side. -/
theorem run_inverseSelectorBank_closed
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) (input : BitInput target) :
    runNPOracleProgram
        (publishedSourceDrivenBankProgram
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
          (inverseLengthProgram contracts clockDepth advantageExponent))
        (publishedSourceDrivenBankBits
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
          target
          (inverseLengthBits contracts clockDepth advantageExponent ⟨target, input⟩)
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (encodeBitInput input))
        (publishedSourceDrivenBankFuel
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
          (inverseLengthFuel contracts clockDepth advantageExponent ⟨target, input⟩)
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (selectorDrivenBankFrame
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))
          (encodeBitInput input)) :=
  run_inverseSelectorDrivenBankProgram contracts clockDepth advantageExponent
    (inverseLengthProgram contracts clockDepth advantageExponent)
    (inverseLengthBits contracts clockDepth advantageExponent)
    (inverseLengthFuel contracts clockDepth advantageExponent)
    (inverse_scheduledLengthRuns contracts clockDepth advantageExponent) target
    input

end NearCubicWires.InverseLengthStage
