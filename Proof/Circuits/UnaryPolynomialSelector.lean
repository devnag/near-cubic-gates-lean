import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.ScheduledRecovery

/-!
# Fixed unary selector for the recovery envelope

The recovery schedule is not an existential search oracle.  This module gives
one fixed, oracle-free register program which scans the canonical polynomial
envelope and returns its least half-crossing.  The coefficient, degree, and
source onset are constants embedded in the program; the only runtime input is
the canonical unary encoding of the target length.

The implementation deliberately keeps both numeric and unary copies of each
loop accumulator.  Numeric copies form the published output, while unary
copies are the structural loop controls supported by the small register
machine.  No decoded crossing, local proof, or caller-selected schedule enters
the machine state.
-/

namespace NearCubicWires.UnaryPolynomialSelector

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialSchedule
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.ScheduledRecovery
open NearCubicWires.VerifiedLinker

/-! ## Fixed register ABI -/

private abbrev oneRegister : ℕ := 2
private abbrev sourceRegister : ℕ := 3
private abbrev sourceUnaryRegister : ℕ := 4
private abbrev resultRegister : ℕ := 5
private abbrev resultUnaryRegister : ℕ := 6
private abbrev degreeCursorRegister : ℕ := 7
private abbrev outerCursorRegister : ℕ := 8
private abbrev productRegister : ℕ := 9
private abbrev productUnaryRegister : ℕ := 10
private abbrev innerCursorRegister : ℕ := 11
private abbrev zeroRegister : ℕ := 12
private abbrev targetCursorRegister : ℕ := 13
private abbrev coreCursorRegister : ℕ := 14
private abbrev previousSourceRegister : ℕ := 15
private abbrev previousCoreRegister : ℕ := 16
private abbrev temporaryRegister : ℕ := 17

private abbrev candidatePc : ℕ := 3
private abbrev degreePc : ℕ := 6
private abbrev outerPc : ℕ := 11
private abbrev innerPc : ℕ := 14
private abbrev comparePc : ℕ := 24
private abbrev advancePc : ℕ := 31
private abbrev emitPc : ℕ := 36

/-- The program has no SAT instruction.  It uses structural unary loops for
multiplication and for the exact comparison `target < 2 * core`. -/
def selectorProgram (coefficient degree sourceOnset : ℕ) :
    NPOracleProgram :=
  [ .set oneRegister 1 1
  , .set sourceRegister sourceOnset 2
  , .set sourceUnaryRegister (encodeUnary (sourceOnset + 1)) candidatePc
  -- Recompute `coefficient * (source + 1)^degree`.
  , .set resultRegister coefficient 4
  , .set resultUnaryRegister (encodeUnary coefficient) 5
  , .set degreeCursorRegister (encodeUnary degree) degreePc
  , .branchZero degreeCursorRegister 22 7
  , .unpairRight degreeCursorRegister degreeCursorRegister 8
  , .copy resultUnaryRegister outerCursorRegister 9
  , .set productRegister 0 10
  , .set productUnaryRegister 0 outerPc
  , .branchZero outerCursorRegister 19 12
  , .unpairRight outerCursorRegister outerCursorRegister 13
  , .copy sourceUnaryRegister innerCursorRegister innerPc
  , .branchZero innerCursorRegister outerPc 15
  , .unpairRight innerCursorRegister innerCursorRegister 16
  , .increment productRegister 17
  , .pair oneRegister productUnaryRegister productUnaryRegister 18
  , .branchZero zeroRegister innerPc innerPc
  , .copy productRegister resultRegister 20
  , .copy productUnaryRegister resultUnaryRegister 21
  , .branchZero zeroRegister degreePc degreePc
  -- Compare by consuming two target cells for every core cell.
  , .copy 0 targetCursorRegister 23
  , .copy resultUnaryRegister coreCursorRegister comparePc
  , .branchZero coreCursorRegister advancePc 25
  , .unpairRight coreCursorRegister coreCursorRegister 26
  , .branchZero targetCursorRegister emitPc 27
  , .unpairRight targetCursorRegister targetCursorRegister 28
  , .branchZero targetCursorRegister emitPc 29
  , .unpairRight targetCursorRegister targetCursorRegister 30
  , .branchZero zeroRegister comparePc comparePc
  -- The current core is still below half: retain it and advance one source.
  , .copy sourceRegister previousSourceRegister 32
  , .copy resultRegister previousCoreRegister 33
  , .increment sourceRegister 34
  , .pair oneRegister sourceUnaryRegister sourceUnaryRegister 35
  , .branchZero zeroRegister candidatePc candidatePc
  -- Emit `(previousSource, source, previousCore, core)`.
  , .pair previousCoreRegister resultRegister temporaryRegister 37
  , .pair sourceRegister temporaryRegister temporaryRegister 38
  , .pair previousSourceRegister temporaryRegister 0 39
  , .halt 0
  ]

@[simp] theorem selectorProgram_oracleFree
    (coefficient degree sourceOnset : ℕ) :
    OracleFree (selectorProgram coefficient degree sourceOnset) := by
  rfl

@[simp] theorem selectorProgram_length
    (coefficient degree sourceOnset : ℕ) :
    (selectorProgram coefficient degree sourceOnset).length = 40 := by
  rfl

/-! ## Pure bounded scan -/

/-- A total semantic scan.  The fallback is used only outside the proved
search horizon; the public theorem supplies a crossing within that horizon. -/
def scanOffset (coefficient degree sourceOnset target : ℕ) :
    ℕ → ℕ → ℕ
  | 0, offset => offset
  | fuel + 1, offset =>
      if target <
          2 * polynomialCore coefficient degree (sourceOnset + offset) then
        offset
      else
        scanOffset coefficient degree sourceOnset target fuel (offset + 1)

theorem scanOffset_eq_of_first
    {coefficient degree sourceOnset target offset fuel start : ℕ}
    (hcross :
      target <
        2 * polynomialCore coefficient degree (sourceOnset + offset))
    (hminimal : ∀ candidate, start ≤ candidate → candidate < offset →
      ¬target <
        2 * polynomialCore coefficient degree (sourceOnset + candidate))
    (hstart : start ≤ offset)
    (hoffset : offset - start < fuel) :
    scanOffset coefficient degree sourceOnset target fuel start = offset := by
  induction fuel generalizing start with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases hequal : start = offset
      · subst start
        simp [scanOffset, hcross]
      · have hbefore : start < offset := by omega
        have hnotCross := hminimal start (le_refl _) hbefore
        simp only [scanOffset, if_neg hnotCross]
        exact ih
          (fun candidate hcand hlt =>
            hminimal candidate (by omega) hlt)
          (by omega) (by omega)

theorem scanOffset_firstCrossing
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    scanOffset coefficient degree (polynomialSourceOnset degree) target
        (target + 1) 0 =
      (polynomialFirstCrossingData coefficient degree target
        hcoefficient hdegree htarget).nextOffset := by
  let data :=
    polynomialFirstCrossingData coefficient degree target
      hcoefficient hdegree htarget
  apply scanOffset_eq_of_first
  · exact data.crossesAtNextOffset
  · intro candidate _ hcandidate
    exact Nat.find_min data.crossingExists hcandidate
  · exact Nat.zero_le _
  · have hbound :=
      polynomialFirstCrossingData_nextOffset_le_target
        coefficient degree target hcoefficient hdegree htarget
    omega

/-! ## Unary encoding bounds -/

theorem encodeUnary_add_one_le_doublePow (count : ℕ) :
    encodeUnary count + 1 ≤ 2 ^ (2 ^ count) := by
  induction count with
  | zero => norm_num [encodeUnary]
  | succ count ih =>
      cases count with
      | zero => norm_num [encodeUnary, Nat.pair]
      | succ count =>
          have hunaryPositive :
              1 ≤ encodeUnary (count + 1) :=
            Nat.left_le_pair 1 (encodeUnary count)
          have hstep :
              encodeUnary ((count + 1) + 1) + 1 ≤
                (encodeUnary (count + 1) + 1) ^ 2 := by
            rw [show encodeUnary ((count + 1) + 1) =
              Nat.pair 1 (encodeUnary (count + 1)) by rfl]
            exact Nat.succ_le_iff.mpr <| by
              simpa [max_eq_right hunaryPositive] using
                Nat.pair_lt_max_add_one_sq 1
                  (encodeUnary (count + 1))
          calc
            encodeUnary ((count + 1) + 1) + 1 ≤
                (encodeUnary (count + 1) + 1) ^ 2 := hstep
            _ ≤ (2 ^ (2 ^ (count + 1))) ^ 2 :=
              Nat.pow_le_pow_left ih 2
            _ = 2 ^ (2 ^ ((count + 1) + 1)) := by
              rw [← pow_mul]
              congr 1

/-- Unary syntax has exponential bit length, not exponential numeric value.
This tight bound is what makes the structural selector an `E` computation. -/
theorem natBitLength_encodeUnary_le_twoPow (count : ℕ) :
    natBitLength (encodeUnary count) ≤ 2 ^ count := by
  by_cases hzero : encodeUnary count = 0
  · rw [hzero]
    unfold natBitLength
    change 1 ≤ 2 ^ count
    exact one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
  · have hnumeric :
        encodeUnary count < 2 ^ (2 ^ count) := by
      exact (Nat.lt_succ_self _).trans_le
        (encodeUnary_add_one_le_doublePow count)
    have hlog :
        Nat.log 2 (encodeUnary count) < 2 ^ count :=
      Nat.log_lt_of_lt_pow hzero hnumeric
    unfold natBitLength
    omega

/-! ## Interpreter-checked arithmetic loops -/

def innerFuel : ℕ → ℕ
  | 0 => 1
  | count + 1 => 5 + innerFuel count

def innerDoneState (state : NPOracleState) (accumulator count : ℕ) :
    NPOracleState :=
  (((state.write innerCursorRegister 0).write productRegister
      (accumulator + count)).write productUnaryRegister
      (encodeUnary (accumulator + count))).jump outerPc

private theorem encodeUnary_succ_ne_zero (count : ℕ) :
    encodeUnary (count + 1) ≠ 0 := by
  have hleft := Nat.left_le_pair 1 (encodeUnary count)
  simp only [encodeUnary]
  omega

private theorem state_ext
    {left right : NPOracleState}
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem innerDoneState_step
    (state : NPOracleState) (accumulator count : ℕ) :
    let next :=
      (((((((state.jump 15).write innerCursorRegister
          (encodeUnary count)).jump 16).write productRegister
          (accumulator + 1)).jump 17).write productUnaryRegister
          (encodeUnary (accumulator + 1))).jump 18).jump innerPc
    innerDoneState next (accumulator + 1) count =
      innerDoneState state accumulator (count + 1) := by
  dsimp only
  apply state_ext
  · rfl
  · funext register
    by_cases hproductUnary : register = productUnaryRegister
    · subst register
      simp [innerDoneState, Nat.add_comm, Nat.add_left_comm]
    · by_cases hproduct : register = productRegister
      · subst register
        simp [innerDoneState, Nat.add_comm, Nat.add_left_comm]
      · by_cases hinner : register = innerCursorRegister
        · subst register
          simp [innerDoneState]
        · simp [innerDoneState, hproductUnary, hproduct, hinner]

/-- Exact execution of the innermost unary addition loop. -/
theorem run_innerLoop
    (coefficient degree sourceOnset maximumBits extra accumulator count
      limit : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = innerPc)
    (hinner :
      state.registers innerCursorRegister = encodeUnary count)
    (hproduct : state.registers productRegister = accumulator)
    (hproductUnary :
      state.registers productUnaryRegister = encodeUnary accumulator)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hbound : accumulator + count ≤ limit)
    (hnat : ∀ value ≤ limit, natBitLength value ≤ maximumBits)
    (hunary : ∀ value ≤ limit,
      natBitLength (encodeUnary value) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (innerFuel count + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra (innerDoneState state accumulator count) := by
  induction count generalizing state accumulator with
  | zero =>
      rw [show innerFuel 0 + extra = extra + 1 by
        simp [innerFuel]
        omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hinner]
      simp only [encodeUnary, if_pos]
      congr 2
      apply state_ext
      · rfl
      · funext register
        by_cases hproductUnaryRegister :
            register = productUnaryRegister
        · subst register
          simpa [innerDoneState] using hproductUnary
        · by_cases hproductRegister : register = productRegister
          · subst register
            simpa [innerDoneState] using hproduct
          · by_cases hinnerRegister : register = innerCursorRegister
            · subst register
              simpa [innerDoneState, encodeUnary] using hinner
            · simp [hproductUnaryRegister,
                hproductRegister, hinnerRegister]
  | succ count ih =>
      have hcountBound : count ≤ limit := by omega
      have hnextBound : accumulator + 1 + count ≤ limit := by omega
      have hinnerBits := hunary count hcountBound
      have hproductBits := hnat (accumulator + 1) (by omega)
      have hproductUnaryBits :=
        hunary (accumulator + 1) (by omega)
      rw [show innerFuel (count + 1) + extra =
        (4 + innerFuel count + extra) + 1 by simp [innerFuel]; omega]
      rw [run_branchZero_instruction
        (fuel := 4 + innerFuel count + extra) (by rfl) hpc]
      rw [hinner, if_neg (encodeUnary_succ_ne_zero count)]
      rw [show 4 + innerFuel count + extra =
        (3 + innerFuel count + extra) + 1 by omega]
      rw [run_unpairRight_instruction
        (fuel := 3 + innerFuel count + extra) (by rfl) rfl
        (by simp [hinner, encodeUnary]) hinnerBits]
      let state₁ :=
        ((state.jump 15).write innerCursorRegister
          (encodeUnary count)).jump 16
      rw [show 3 + innerFuel count + extra =
        (2 + innerFuel count + extra) + 1 by omega]
      rw [run_increment_instruction
        (fuel := 2 + innerFuel count + extra) (by rfl) rfl
        (by
          simp [hproduct])
        hproductBits]
      let state₂ :=
        (state₁.write productRegister (accumulator + 1)).jump 17
      rw [show 2 + innerFuel count + extra =
        (1 + innerFuel count + extra) + 1 by omega]
      rw [run_pair_instruction
        (fuel := 1 + innerFuel count + extra) (by rfl) rfl
        (by
          simp [hone, hproductUnary, encodeUnary])
        hproductUnaryBits]
      let state₃ :=
        (state₂.write productUnaryRegister
          (encodeUnary (accumulator + 1))).jump 18
      rw [show 1 + innerFuel count + extra =
        (innerFuel count + extra) + 1 by omega]
      rw [run_branchZero_instruction
        (fuel := innerFuel count + extra) (by rfl) rfl]
      have hstate₃Zero :
          state₃.registers zeroRegister = 0 := by
        simp [state₃, state₂, state₁, hzero]
      simp only [ite_self]
      let nextState := state₃.jump innerPc
      have hnextPc : nextState.pc = innerPc := rfl
      have hnextInner :
          nextState.registers innerCursorRegister =
            encodeUnary count := by
        simp [nextState, state₃, state₂, state₁]
      have hnextProduct :
          nextState.registers productRegister =
            accumulator + 1 := by
        simp [nextState, state₃, state₂]
      have hnextProductUnary :
          nextState.registers productUnaryRegister =
            encodeUnary (accumulator + 1) := by
        simp [nextState, state₃]
      have hnextOne :
          nextState.registers oneRegister = 1 := by
        simp [nextState, state₃, state₂, state₁, hone]
      have hnextZero :
          nextState.registers zeroRegister = 0 := by
        simpa [nextState] using hstate₃Zero
      rw [ih (state := nextState) (accumulator := accumulator + 1)
        hnextPc hnextInner hnextProduct hnextProductUnary hnextOne hnextZero
        hnextBound]
      exact congrArg
        (runNPOracleProgram
          (selectorProgram coefficient degree sourceOnset)
          maximumBits extra)
        (innerDoneState_step state accumulator count)

def outerFuel (factor : ℕ) : ℕ → ℕ
  | 0 => 1
  | count + 1 => 3 + innerFuel factor + outerFuel factor count

def outerDoneState (state : NPOracleState)
    (accumulator count factor : ℕ) : NPOracleState :=
  (((state.write outerCursorRegister 0).write productRegister
      (accumulator + count * factor)).write productUnaryRegister
      (encodeUnary (accumulator + count * factor))).jump 19

private theorem outerDoneState_step
    (state : NPOracleState) (accumulator count factor : ℕ)
    (hinnerZero : state.registers innerCursorRegister = 0) :
    let entered :=
      (((((state.jump 12).write outerCursorRegister
          (encodeUnary count)).jump 13).write innerCursorRegister
          (encodeUnary factor)).jump innerPc)
    let next := innerDoneState entered accumulator factor
    outerDoneState next (accumulator + factor) count factor =
      outerDoneState state accumulator (count + 1) factor := by
  dsimp only
  apply state_ext
  · rfl
  · funext register
    by_cases hproductUnary : register = productUnaryRegister
    · subst register
      simp [outerDoneState, innerDoneState, Nat.succ_mul,
        Nat.add_assoc, Nat.add_comm]
    · by_cases hproduct : register = productRegister
      · subst register
        simp [outerDoneState, innerDoneState, Nat.succ_mul,
          Nat.add_assoc, Nat.add_comm]
      · by_cases houter : register = outerCursorRegister
        · subst register
          simp [outerDoneState, innerDoneState]
        · by_cases hinner : register = innerCursorRegister
          · subst register
            simp [outerDoneState, innerDoneState, hinnerZero]
          · simp [outerDoneState, innerDoneState, hproductUnary,
              hproduct, houter, hinner]

/-- Repeated unary addition computes one exact multiplication. -/
theorem run_outerLoop
    (coefficient degree sourceOnset maximumBits extra accumulator count factor
      limit : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = outerPc)
    (houter :
      state.registers outerCursorRegister = encodeUnary count)
    (hfactor :
      state.registers sourceUnaryRegister = encodeUnary factor)
    (hproduct : state.registers productRegister = accumulator)
    (hproductUnary :
      state.registers productUnaryRegister = encodeUnary accumulator)
    (hinnerZero : state.registers innerCursorRegister = 0)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hfactorPositive : 0 < factor)
    (hbound : accumulator + count * factor ≤ limit)
    (hnat : ∀ value ≤ limit, natBitLength value ≤ maximumBits)
    (hunary : ∀ value ≤ limit,
      natBitLength (encodeUnary value) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (outerFuel factor count + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra
        (outerDoneState state accumulator count factor) := by
  induction count generalizing state accumulator with
  | zero =>
      rw [show outerFuel factor 0 + extra = extra + 1 by
        simp [outerFuel]
        omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [houter]
      simp only [encodeUnary, if_pos]
      congr 2
      apply state_ext
      · rfl
      · funext register
        by_cases hproductUnaryRegister :
            register = productUnaryRegister
        · subst register
          simpa [outerDoneState] using hproductUnary
        · by_cases hproductRegister : register = productRegister
          · subst register
            simpa [outerDoneState] using hproduct
          · by_cases houterRegister : register = outerCursorRegister
            · subst register
              simpa [outerDoneState, encodeUnary] using houter
            · simp [hproductUnaryRegister,
                hproductRegister, houterRegister]
  | succ count ih =>
      have hcountBound : count ≤ limit := by
        have honeFactor : 1 ≤ factor := by omega
        have hscaled : count + 1 ≤ (count + 1) * factor := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left (count + 1) honeFactor
        omega
      have houterBits := hunary count hcountBound
      have hfactorBound : factor ≤ limit := by
        by_cases hcountZero : count = 0
        · subst count
          have : accumulator + factor ≤
              accumulator + (0 + 1) * factor := by simp
          omega
        · have hcountPositive : 1 ≤ count + 1 := by omega
          have : factor ≤ (count + 1) * factor := by
            simpa [one_mul] using
              Nat.mul_le_mul_right factor hcountPositive
          omega
      have hfactorBits := hunary factor hfactorBound
      rw [show outerFuel factor (count + 1) + extra =
        (2 + innerFuel factor + outerFuel factor count + extra) + 1 by
          simp [outerFuel]
          omega]
      rw [run_branchZero_instruction
        (fuel := 2 + innerFuel factor + outerFuel factor count + extra)
        (by rfl) hpc]
      rw [houter, if_neg (encodeUnary_succ_ne_zero count)]
      rw [show 2 + innerFuel factor + outerFuel factor count + extra =
        (1 + innerFuel factor + outerFuel factor count + extra) + 1 by omega]
      rw [run_unpairRight_instruction
        (fuel := 1 + innerFuel factor + outerFuel factor count + extra)
        (by rfl) rfl (by simp [houter, encodeUnary]) houterBits]
      let state₁ :=
        ((state.jump 12).write outerCursorRegister
          (encodeUnary count)).jump 13
      rw [show 1 + innerFuel factor + outerFuel factor count + extra =
        (innerFuel factor + outerFuel factor count + extra) + 1 by omega]
      rw [run_copy_instruction
        (fuel := innerFuel factor + outerFuel factor count + extra)
        (by rfl) rfl (by simp [hfactor]) hfactorBits]
      let entered :=
        (state₁.write innerCursorRegister (encodeUnary factor)).jump innerPc
      have henteredPc : entered.pc = innerPc := rfl
      have henteredInner :
          entered.registers innerCursorRegister =
            encodeUnary factor := by
        simp [entered]
      have henteredProduct :
          entered.registers productRegister = accumulator := by
        simp [entered, state₁, hproduct]
      have henteredProductUnary :
          entered.registers productUnaryRegister =
            encodeUnary accumulator := by
        simp [entered, state₁, hproductUnary]
      have henteredOne :
          entered.registers oneRegister = 1 := by
        simp [entered, state₁, hone]
      have henteredZero :
          entered.registers zeroRegister = 0 := by
        simp [entered, state₁, hzero]
      rw [show innerFuel factor + outerFuel factor count + extra =
        innerFuel factor + (outerFuel factor count + extra) by omega]
      rw [run_innerLoop coefficient degree sourceOnset maximumBits
        (outerFuel factor count + extra) accumulator factor limit entered
        henteredPc henteredInner henteredProduct henteredProductUnary
        henteredOne henteredZero (by
          have : accumulator + factor ≤
              accumulator + (count + 1) * factor := by
            simp only [Nat.succ_mul]
            omega
          omega)
        hnat hunary]
      let next := innerDoneState entered accumulator factor
      have hnextPc : next.pc = outerPc := rfl
      have hnextOuter :
          next.registers outerCursorRegister =
            encodeUnary count := by
        simp [next, innerDoneState, entered, state₁]
      have hnextFactor :
          next.registers sourceUnaryRegister =
            encodeUnary factor := by
        simp [next, innerDoneState, entered, state₁, hfactor]
      have hnextProduct :
          next.registers productRegister =
            accumulator + factor := by
        simp [next, innerDoneState]
      have hnextProductUnary :
          next.registers productUnaryRegister =
            encodeUnary (accumulator + factor) := by
        simp [next, innerDoneState]
      have hnextInnerZero :
          next.registers innerCursorRegister = 0 := by
        simp [next, innerDoneState]
      have hnextOne :
          next.registers oneRegister = 1 := by
        simp [next, innerDoneState, entered, state₁, hone]
      have hnextZero :
          next.registers zeroRegister = 0 := by
        simp [next, innerDoneState, entered, state₁, hzero]
      rw [ih (state := next) (accumulator := accumulator + factor)
        hnextPc hnextOuter hnextFactor hnextProduct hnextProductUnary
        hnextInnerZero hnextOne hnextZero (by
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hbound)]
      exact congrArg
        (runNPOracleProgram
          (selectorProgram coefficient degree sourceOnset)
          maximumBits extra)
        (outerDoneState_step state accumulator count factor hinnerZero)

def powerFuel (factor value : ℕ) : ℕ → ℕ
  | 0 => 1
  | degree + 1 =>
      8 + outerFuel factor value +
        powerFuel factor (value * factor) degree

def powerStepState (factor degree value : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let degreeState :=
    ((state.jump 7).write degreeCursorRegister
      (encodeUnary degree)).jump 8
  let outerState :=
    (degreeState.write outerCursorRegister (encodeUnary value)).jump 9
  let productState := (outerState.write productRegister 0).jump 10
  let entered :=
    (productState.write productUnaryRegister 0).jump outerPc
  let multiplied := outerDoneState entered 0 value factor
  let resultState :=
    (multiplied.write resultRegister (value * factor)).jump 20
  let unaryState :=
    (resultState.write resultUnaryRegister
      (encodeUnary (value * factor))).jump 21
  unaryState.jump degreePc

@[simp] theorem powerStepState_result
    (factor degree value : ℕ) (state : NPOracleState) :
    (powerStepState factor degree value state).registers resultRegister =
      value * factor := by
  simp [powerStepState]

@[simp] theorem powerStepState_resultUnary
    (factor degree value : ℕ) (state : NPOracleState) :
    (powerStepState factor degree value state).registers
        resultUnaryRegister =
      encodeUnary (value * factor) := by
  simp [powerStepState]

def powerDoneState (factor : ℕ) :
    ℕ → ℕ → NPOracleState → NPOracleState
  | 0, _value, state => state.jump 22
  | degree + 1, value, state =>
      powerDoneState factor degree (value * factor)
        (powerStepState factor degree value state)

/-- The fixed degree loop computes an exact natural power by invoking the
verified multiplication loop once per unary degree cell. -/
theorem run_powerLoop
    (coefficient degree sourceOnset maximumBits extra factor value remaining
      limit : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = degreePc)
    (hdegree :
      state.registers degreeCursorRegister = encodeUnary remaining)
    (hfactor :
      state.registers sourceUnaryRegister = encodeUnary factor)
    (hresult : state.registers resultRegister = value)
    (hresultUnary :
      state.registers resultUnaryRegister = encodeUnary value)
    (hinnerZero : state.registers innerCursorRegister = 0)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hfactorPositive : 0 < factor)
    (hvaluePositive : 0 < value)
    (hdegreeBound : remaining ≤ limit)
    (hbound : value * factor ^ remaining ≤ limit)
    (hnat : ∀ candidate ≤ limit,
      natBitLength candidate ≤ maximumBits)
    (hunary : ∀ candidate ≤ limit,
      natBitLength (encodeUnary candidate) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (powerFuel factor value remaining + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra
        (powerDoneState factor remaining value state) := by
  induction remaining generalizing state value with
  | zero =>
      rw [show powerFuel factor value 0 + extra = extra + 1 by
        simp [powerFuel]
        omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hdegree]
      simp [encodeUnary, powerDoneState]
  | succ remaining ih =>
      have hremainingBound : remaining ≤ limit := by omega
      have hdegreeBits := hunary remaining hremainingBound
      have hvalueBound : value ≤ limit := by
        calc
          value ≤ value * factor ^ (remaining + 1) := by
            have hpow :
                1 ≤ factor ^ (remaining + 1) :=
              one_le_pow₀ (by omega : 1 ≤ factor)
            simpa only [Nat.mul_one] using
              Nat.mul_le_mul_left value hpow
          _ ≤ limit := hbound
      have hvalueBits := hunary value hvalueBound
      have hzeroBits := hnat 0 (Nat.zero_le _)
      have hproductBound :
          value * factor ≤ limit := by
        calc
          value * factor ≤ value * factor ^ (remaining + 1) := by
            rw [pow_succ]
            gcongr
            have hpow :
                1 ≤ factor ^ remaining :=
              one_le_pow₀ (by omega : 1 ≤ factor)
            simpa only [one_mul] using
              Nat.mul_le_mul_right factor hpow
          _ ≤ limit := hbound
      rw [show powerFuel factor value (remaining + 1) + extra =
        (7 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra) + 1 by
          simp [powerFuel]
          omega]
      rw [run_branchZero_instruction
        (fuel := 7 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra)
        (by rfl) hpc]
      rw [hdegree, if_neg (encodeUnary_succ_ne_zero remaining)]
      rw [show 7 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra =
        (6 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_unpairRight_instruction
        (fuel := 6 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl (by simp [hdegree, encodeUnary]) hdegreeBits]
      let state₁ :=
        ((state.jump 7).write degreeCursorRegister
          (encodeUnary remaining)).jump 8
      rw [show 6 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra =
        (5 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_copy_instruction
        (fuel := 5 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl (by simp [hresultUnary]) hvalueBits]
      let state₂ :=
        (state₁.write outerCursorRegister (encodeUnary value)).jump 9
      rw [show 5 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra =
        (4 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_set_instruction
        (fuel := 4 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl hzeroBits]
      let state₃ := (state₂.write productRegister 0).jump 10
      rw [show 4 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra =
        (3 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_set_instruction
        (fuel := 3 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl (hunary 0 (Nat.zero_le _))]
      let entered := (state₃.write productUnaryRegister 0).jump outerPc
      have henteredPc : entered.pc = outerPc := rfl
      have henteredOuter :
          entered.registers outerCursorRegister =
            encodeUnary value := by
        simp [entered, state₃, state₂]
      have henteredFactor :
          entered.registers sourceUnaryRegister =
            encodeUnary factor := by
        simp [entered, state₃, state₂, state₁, hfactor]
      have henteredProduct :
          entered.registers productRegister = 0 := by
        simp [entered, state₃]
      have henteredProductUnary :
          entered.registers productUnaryRegister = encodeUnary 0 := by
        rfl
      have henteredInnerZero :
          entered.registers innerCursorRegister = 0 := by
        simp [entered, state₃, state₂, state₁, hinnerZero]
      have henteredOne :
          entered.registers oneRegister = 1 := by
        simp [entered, state₃, state₂, state₁, hone]
      have henteredZero :
          entered.registers zeroRegister = 0 := by
        simp [entered, state₃, state₂, state₁, hzero]
      rw [show 3 + outerFuel factor value +
          powerFuel factor (value * factor) remaining + extra =
        outerFuel factor value +
          (3 + powerFuel factor (value * factor) remaining + extra) by omega]
      change
        runNPOracleProgram
            (selectorProgram coefficient degree sourceOnset)
            maximumBits
            (outerFuel factor value +
              (3 + powerFuel factor (value * factor) remaining + extra))
            entered =
          _
      rw [run_outerLoop coefficient degree sourceOnset maximumBits
        (3 + powerFuel factor (value * factor) remaining + extra)
        0 value factor limit entered henteredPc henteredOuter
        henteredFactor henteredProduct henteredProductUnary henteredInnerZero
        henteredOne henteredZero hfactorPositive
        (by simpa using hproductBound) hnat hunary]
      let multiplied := outerDoneState entered 0 value factor
      have hmultipliedProduct :
          multiplied.registers productRegister =
            value * factor := by
        simp [multiplied, outerDoneState]
      have hmultipliedProductUnary :
          multiplied.registers productUnaryRegister =
            encodeUnary (value * factor) := by
        simp [multiplied, outerDoneState]
      have hproductNatBits := hnat (value * factor) hproductBound
      have hproductUnaryBits := hunary (value * factor) hproductBound
      rw [show 3 + powerFuel factor (value * factor) remaining + extra =
        (2 + powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_copy_instruction
        (fuel := 2 + powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl hmultipliedProduct hproductNatBits]
      let state₄ :=
        (multiplied.write resultRegister (value * factor)).jump 20
      rw [show 2 + powerFuel factor (value * factor) remaining + extra =
        (1 + powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_copy_instruction
        (fuel := 1 + powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl
        (by simp [hmultipliedProductUnary])
        hproductUnaryBits]
      let continued :=
        (state₄.write resultUnaryRegister
          (encodeUnary (value * factor))).jump 21
      rw [show 1 + powerFuel factor (value * factor) remaining + extra =
        (powerFuel factor (value * factor) remaining + extra) + 1 by omega]
      rw [run_branchZero_instruction
        (fuel := powerFuel factor (value * factor) remaining + extra)
        (by rfl) rfl]
      have hcontinuedZero :
          continued.registers zeroRegister = 0 := by
        simp [continued, state₄, multiplied, outerDoneState, entered,
          state₃, state₂, state₁, hzero]
      simp only [ite_self]
      let next := continued.jump degreePc
      have hnextPc : next.pc = degreePc := rfl
      have hnextDegree :
          next.registers degreeCursorRegister =
            encodeUnary remaining := by
        simp [next, continued, state₄, multiplied, outerDoneState,
          entered, state₃, state₂, state₁]
      have hnextFactor :
          next.registers sourceUnaryRegister =
            encodeUnary factor := by
        simp [next, continued, state₄, multiplied, outerDoneState,
          entered, state₃, state₂, state₁, hfactor]
      have hnextResult :
          next.registers resultRegister = value * factor := by
        simp [next, continued, state₄]
      have hnextResultUnary :
          next.registers resultUnaryRegister =
            encodeUnary (value * factor) := by
        simp [next, continued]
      have hnextOne :
          next.registers oneRegister = 1 := by
        simp [next, continued, state₄, multiplied, outerDoneState,
          entered, state₃, state₂, state₁, hone]
      have hnextZero :
          next.registers zeroRegister = 0 := by
        simpa [next] using hcontinuedZero
      have hnextInnerZero :
          next.registers innerCursorRegister = 0 := by
        simp [next, continued, state₄, multiplied, outerDoneState,
          entered, state₃, state₂, state₁, hinnerZero]
      rw [ih (state := next) (value := value * factor)
        hnextPc hnextDegree hnextFactor hnextResult hnextResultUnary
        hnextInnerZero hnextOne hnextZero
        (Nat.mul_pos hvaluePositive hfactorPositive)
        (by omega)
        (by
          rw [pow_succ] at hbound
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbound)]
      rfl

theorem powerDoneState_result
    (factor remaining value : ℕ) (state : NPOracleState)
    (hresult : state.registers resultRegister = value) :
    (powerDoneState factor remaining value state).registers resultRegister =
      value * factor ^ remaining := by
  induction remaining generalizing value state with
  | zero => simpa [powerDoneState] using hresult
  | succ remaining ih =>
      simp only [powerDoneState]
      have hrecursive :=
        ih (value * factor)
          (powerStepState factor remaining value state) (by simp)
      rw [hrecursive]
      rw [pow_succ]
      ring

theorem powerDoneState_resultUnary
    (factor remaining value : ℕ) (state : NPOracleState)
    (hresult :
      state.registers resultUnaryRegister = encodeUnary value) :
    (powerDoneState factor remaining value state).registers
        resultUnaryRegister =
      encodeUnary (value * factor ^ remaining) := by
  induction remaining generalizing value state with
  | zero => simpa [powerDoneState] using hresult
  | succ remaining ih =>
      simp only [powerDoneState]
      have hrecursive :=
        ih (value * factor)
          (powerStepState factor remaining value state) (by simp)
      rw [hrecursive]
      rw [pow_succ]
      congr 1
      ring

@[simp] theorem powerDoneState_pc
    (factor remaining value : ℕ) (state : NPOracleState) :
    (powerDoneState factor remaining value state).pc = 22 := by
  induction remaining generalizing value state with
  | zero => rfl
  | succ remaining ih =>
      simp only [powerDoneState]
      exact ih _ _

theorem powerDoneState_preserves
    (factor remaining value : ℕ) (state : NPOracleState) (register : ℕ)
    (hdegree : register ≠ degreeCursorRegister)
    (houter : register ≠ outerCursorRegister)
    (hproduct : register ≠ productRegister)
    (hproductUnary : register ≠ productUnaryRegister)
    (hresult : register ≠ resultRegister)
    (hresultUnary : register ≠ resultUnaryRegister) :
    (powerDoneState factor remaining value state).registers register =
      state.registers register := by
  induction remaining generalizing value state with
  | zero => rfl
  | succ remaining ih =>
      simp only [powerDoneState]
      rw [ih]
      simp [powerStepState, outerDoneState,
        hdegree, houter, hproduct, hproductUnary,
        hresult, hresultUnary]

/-! ## Exact structural comparison -/

def comparisonFuel : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, Nat.succ _ => 3
  | Nat.succ 0, Nat.succ _ => 5
  | Nat.succ (Nat.succ target), Nat.succ core =>
      7 + comparisonFuel target core

def comparisonState : ℕ → ℕ → NPOracleState → NPOracleState
  | _, 0, state => state.jump advancePc
  | 0, Nat.succ core, state =>
      let coreState :=
        ((state.jump 25).write coreCursorRegister
          (encodeUnary core)).jump 26
      coreState.jump emitPc
  | Nat.succ 0, Nat.succ core, state =>
      let coreState :=
        ((state.jump 25).write coreCursorRegister
          (encodeUnary core)).jump 26
      let targetBranch := coreState.jump 27
      let targetState :=
        (targetBranch.write targetCursorRegister 0).jump 28
      targetState.jump emitPc
  | Nat.succ (Nat.succ target), Nat.succ core, state =>
      let coreState :=
        ((state.jump 25).write coreCursorRegister
          (encodeUnary core)).jump 26
      let firstBranch := coreState.jump 27
      let firstTarget :=
        (firstBranch.write targetCursorRegister
          (encodeUnary (target + 1))).jump 28
      let secondBranch := firstTarget.jump 29
      let secondTarget :=
        (secondBranch.write targetCursorRegister
          (encodeUnary target)).jump 30
      comparisonState target core (secondTarget.jump comparePc)

/-- Interpreter semantics of consuming two target cells per core cell. -/
theorem run_comparison
    (coefficient degree sourceOnset maximumBits extra target core limit : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = comparePc)
    (htarget :
      state.registers targetCursorRegister = encodeUnary target)
    (hcore :
      state.registers coreCursorRegister = encodeUnary core)
    (hzero : state.registers zeroRegister = 0)
    (htargetBound : target ≤ limit)
    (hcoreBound : core ≤ limit)
    (hunary : ∀ value ≤ limit,
      natBitLength (encodeUnary value) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (comparisonFuel target core + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra (comparisonState target core state) := by
  induction core generalizing target state with
  | zero =>
      rw [show comparisonFuel target 0 + extra = extra + 1 by
        simp [comparisonFuel]
        omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
      rw [hcore]
      simp [encodeUnary, comparisonState]
  | succ core ih =>
      cases target with
      | zero =>
          have hcoreBits := hunary core (by omega)
          rw [show comparisonFuel 0 (core + 1) + extra =
            (2 + extra) + 1 by simp [comparisonFuel]; omega]
          rw [run_branchZero_instruction (fuel := 2 + extra)
            (by rfl) hpc]
          rw [hcore, if_neg (encodeUnary_succ_ne_zero core)]
          rw [show 2 + extra = (1 + extra) + 1 by omega]
          rw [run_unpairRight_instruction (fuel := 1 + extra)
            (by rfl) rfl (by simp [hcore, encodeUnary]) hcoreBits]
          let state₁ :=
            ((state.jump 25).write coreCursorRegister
              (encodeUnary core)).jump 26
          rw [show 1 + extra = extra + 1 by omega]
          rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
          have htargetZero :
              state₁.registers targetCursorRegister = 0 := by
            simp [state₁, htarget, encodeUnary]
          rw [htargetZero, if_pos rfl]
          rfl
      | succ target =>
          cases target with
          | zero =>
              have hcoreBits := hunary core (by omega)
              have hzeroBits := hunary 0 (Nat.zero_le _)
              rw [show comparisonFuel 1 (core + 1) + extra =
                (4 + extra) + 1 by simp [comparisonFuel]; omega]
              rw [run_branchZero_instruction (fuel := 4 + extra)
                (by rfl) hpc]
              rw [hcore, if_neg (encodeUnary_succ_ne_zero core)]
              rw [show 4 + extra = (3 + extra) + 1 by omega]
              rw [run_unpairRight_instruction (fuel := 3 + extra)
                (by rfl) rfl (by simp [hcore, encodeUnary]) hcoreBits]
              let state₁ :=
                ((state.jump 25).write coreCursorRegister
                  (encodeUnary core)).jump 26
              rw [show 3 + extra = (2 + extra) + 1 by omega]
              rw [run_branchZero_instruction (fuel := 2 + extra)
                (by rfl) rfl]
              have htargetOne :
                  state₁.registers targetCursorRegister =
                    encodeUnary 1 := by
                simp [state₁, htarget]
              rw [htargetOne, if_neg (encodeUnary_succ_ne_zero 0)]
              rw [show 2 + extra = (1 + extra) + 1 by omega]
              rw [run_unpairRight_instruction (fuel := 1 + extra)
                (by rfl) rfl
                (by
                  change
                    (Nat.unpair
                      ((state₁.jump 27).registers
                        targetCursorRegister)).2 = 0
                  rw [show
                    (state₁.jump 27).registers targetCursorRegister =
                      encodeUnary 1 by simpa using htargetOne]
                  simp [encodeUnary])
                hzeroBits]
              let state₂ :=
                ((state₁.jump 27).write targetCursorRegister 0).jump 28
              rw [show 1 + extra = extra + 1 by omega]
              rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
              have htargetZero :
                  state₂.registers targetCursorRegister = 0 := by
                simp [state₂]
              change
                runNPOracleProgram
                    (selectorProgram coefficient degree sourceOnset)
                    maximumBits extra
                    (state₂.jump
                      (if state₂.registers targetCursorRegister = 0 then
                        emitPc else 29)) =
                  _
              rw [htargetZero, if_pos rfl]
              rfl
          | succ target =>
              have hcoreBits := hunary core (by omega)
              have htargetSuccBound : target + 1 ≤ limit := by omega
              have htargetBound' : target ≤ limit := by omega
              have htargetSuccBits :=
                hunary (target + 1) htargetSuccBound
              have htargetBits := hunary target htargetBound'
              rw [show
                comparisonFuel (target + 2) (core + 1) + extra =
                  (6 + comparisonFuel target core + extra) + 1 by
                    simp [comparisonFuel]
                    omega]
              rw [run_branchZero_instruction
                (fuel := 6 + comparisonFuel target core + extra)
                (by rfl) hpc]
              rw [hcore, if_neg (encodeUnary_succ_ne_zero core)]
              rw [show 6 + comparisonFuel target core + extra =
                (5 + comparisonFuel target core + extra) + 1 by omega]
              rw [run_unpairRight_instruction
                (fuel := 5 + comparisonFuel target core + extra)
                (by rfl) rfl (by simp [hcore, encodeUnary]) hcoreBits]
              let state₁ :=
                ((state.jump 25).write coreCursorRegister
                  (encodeUnary core)).jump 26
              rw [show 5 + comparisonFuel target core + extra =
                (4 + comparisonFuel target core + extra) + 1 by omega]
              rw [run_branchZero_instruction
                (fuel := 4 + comparisonFuel target core + extra)
                (by rfl) rfl]
              have htargetSuccSucc :
                  state₁.registers targetCursorRegister =
                    encodeUnary (target + 2) := by
                simp [state₁, htarget]
              rw [htargetSuccSucc,
                if_neg (encodeUnary_succ_ne_zero (target + 1))]
              rw [show 4 + comparisonFuel target core + extra =
                (3 + comparisonFuel target core + extra) + 1 by omega]
              rw [run_unpairRight_instruction
                (fuel := 3 + comparisonFuel target core + extra)
                (by rfl) rfl
                (by
                  change
                    (Nat.unpair
                      ((state₁.jump 27).registers
                        targetCursorRegister)).2 =
                      encodeUnary (target + 1)
                  rw [show
                    (state₁.jump 27).registers targetCursorRegister =
                      encodeUnary (target + 2) by
                        simpa using htargetSuccSucc]
                  simp [encodeUnary])
                htargetSuccBits]
              let state₂ :=
                ((state₁.jump 27).write targetCursorRegister
                  (encodeUnary (target + 1))).jump 28
              rw [show 3 + comparisonFuel target core + extra =
                (2 + comparisonFuel target core + extra) + 1 by omega]
              rw [run_branchZero_instruction
                (fuel := 2 + comparisonFuel target core + extra)
                (by rfl) rfl]
              have htargetSucc :
                  state₂.registers targetCursorRegister =
                    encodeUnary (target + 1) := by
                simp [state₂]
              change
                runNPOracleProgram
                    (selectorProgram coefficient degree sourceOnset)
                    maximumBits
                    (2 + comparisonFuel target core + extra)
                    (state₂.jump
                      (if state₂.registers targetCursorRegister = 0 then
                        emitPc else 29)) =
                  _
              rw [htargetSucc, if_neg (encodeUnary_succ_ne_zero target)]
              rw [show 2 + comparisonFuel target core + extra =
                (1 + comparisonFuel target core + extra) + 1 by omega]
              rw [run_unpairRight_instruction
                (fuel := 1 + comparisonFuel target core + extra)
                (by rfl) rfl
                (by
                  rw [show
                    (state₂.jump 29).registers targetCursorRegister =
                      encodeUnary (target + 1) by
                        simpa using htargetSucc]
                  simp [encodeUnary])
                htargetBits]
              let state₃ :=
                ((state₂.jump 29).write targetCursorRegister
                  (encodeUnary target)).jump 30
              rw [show 1 + comparisonFuel target core + extra =
                (comparisonFuel target core + extra) + 1 by omega]
              rw [run_branchZero_instruction
                (fuel := comparisonFuel target core + extra)
                (by rfl) rfl]
              have hstate₃Zero :
                  state₃.registers zeroRegister = 0 := by
                simp [state₃, state₂, state₁, hzero]
              simp only [ite_self]
              let next := state₃.jump comparePc
              have hnextPc : next.pc = comparePc := rfl
              have hnextTarget :
                  next.registers targetCursorRegister =
                    encodeUnary target := by
                simp [next, state₃]
              have hnextCore :
                  next.registers coreCursorRegister =
                    encodeUnary core := by
                simp [next, state₃, state₂, state₁]
              have hnextZero :
                  next.registers zeroRegister = 0 := by
                simpa [next] using hstate₃Zero
              rw [ih (target := target) (state := next)
                hnextPc hnextTarget hnextCore
                hnextZero htargetBound' (by omega)]
              rfl

@[simp] theorem comparisonState_pc
    (target core : ℕ) (state : NPOracleState) :
    (comparisonState target core state).pc =
      if target < 2 * core then emitPc else advancePc := by
  induction core generalizing target state with
  | zero => simp [comparisonState]
  | succ core ih =>
      cases target with
      | zero => simp [comparisonState]
      | succ target =>
          cases target with
          | zero =>
              simp [comparisonState]
              omega
          | succ target =>
              simp only [comparisonState]
              rw [ih]
              simp only [show target + 2 < 2 * (core + 1) ↔
                target < 2 * core by omega]

theorem comparisonState_preserves
    (target core : ℕ) (state : NPOracleState) (register : ℕ)
    (htarget : register ≠ targetCursorRegister)
    (hcore : register ≠ coreCursorRegister) :
    (comparisonState target core state).registers register =
      state.registers register := by
  induction core generalizing target state with
  | zero => simp [comparisonState]
  | succ core ih =>
      cases target with
      | zero => simp [comparisonState, hcore]
      | succ target =>
          cases target with
          | zero => simp [comparisonState, htarget, hcore]
          | succ target =>
              simp only [comparisonState]
              rw [ih]
              simp [htarget, hcore]

/-! ## One complete candidate evaluation -/

def candidatePowerEntry (coefficient degree : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let resultState :=
    (state.write resultRegister coefficient).jump 4
  let unaryState :=
    (resultState.write resultUnaryRegister
      (encodeUnary coefficient)).jump 5
  (unaryState.write degreeCursorRegister
    (encodeUnary degree)).jump degreePc

def candidateComparisonEntry
    (factor coefficient degree target : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let powered :=
    powerDoneState factor degree coefficient
      (candidatePowerEntry coefficient degree state)
  let targetState :=
    (powered.write targetCursorRegister (encodeUnary target)).jump 23
  (targetState.write coreCursorRegister
    (encodeUnary (coefficient * factor ^ degree))).jump comparePc

def candidateDoneState
    (factor coefficient degree target : ℕ)
    (state : NPOracleState) : NPOracleState :=
  comparisonState target (coefficient * factor ^ degree)
    (candidateComparisonEntry factor coefficient degree target state)

def candidateFuel
    (factor coefficient degree target : ℕ) : ℕ :=
  5 + powerFuel factor coefficient degree +
    comparisonFuel target (coefficient * factor ^ degree)

theorem run_candidate
    (coefficient degree sourceOnset maximumBits extra factor target limit : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = candidatePc)
    (htarget :
      state.registers 0 = encodeUnary target)
    (hfactor :
      state.registers sourceUnaryRegister = encodeUnary factor)
    (hinnerZero : state.registers innerCursorRegister = 0)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hcoefficientPositive : 0 < coefficient)
    (hfactorPositive : 0 < factor)
    (hcoefficientBound : coefficient ≤ limit)
    (hdegreeBound : degree ≤ limit)
    (_hfactorBound : factor ≤ limit)
    (htargetBound : target ≤ limit)
    (hcoreBound : coefficient * factor ^ degree ≤ limit)
    (hnat : ∀ value ≤ limit,
      natBitLength value ≤ maximumBits)
    (hunary : ∀ value ≤ limit,
      natBitLength (encodeUnary value) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits
        (candidateFuel factor coefficient degree target + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra
        (candidateDoneState factor coefficient degree target state) := by
  have hcoefficientNatBits := hnat coefficient hcoefficientBound
  have hcoefficientUnaryBits :=
    hunary coefficient hcoefficientBound
  have hdegreeUnaryBits := hunary degree hdegreeBound
  rw [show candidateFuel factor coefficient degree target + extra =
    (4 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra) + 1 by
      simp [candidateFuel]
      omega]
  rw [run_set_instruction
    (fuel := 4 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra)
    (by rfl) hpc hcoefficientNatBits]
  let resultState :=
    (state.write resultRegister coefficient).jump 4
  rw [show 4 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra =
    (3 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra) + 1 by
        omega]
  rw [run_set_instruction
    (fuel := 3 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra)
    (by rfl) rfl hcoefficientUnaryBits]
  let unaryState :=
    (resultState.write resultUnaryRegister
      (encodeUnary coefficient)).jump 5
  rw [show 3 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra =
    (2 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra) + 1 by
        omega]
  rw [run_set_instruction
    (fuel := 2 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra)
    (by rfl) rfl hdegreeUnaryBits]
  let powerEntry :=
    (unaryState.write degreeCursorRegister
      (encodeUnary degree)).jump degreePc
  have hpowerPc : powerEntry.pc = degreePc := rfl
  have hpowerDegree :
      powerEntry.registers degreeCursorRegister =
        encodeUnary degree := by
    simp [powerEntry]
  have hpowerFactor :
      powerEntry.registers sourceUnaryRegister =
        encodeUnary factor := by
    simp [powerEntry, unaryState, resultState, hfactor]
  have hpowerResult :
      powerEntry.registers resultRegister = coefficient := by
    simp [powerEntry, unaryState, resultState]
  have hpowerResultUnary :
      powerEntry.registers resultUnaryRegister =
        encodeUnary coefficient := by
    simp [powerEntry, unaryState]
  have hpowerInnerZero :
      powerEntry.registers innerCursorRegister = 0 := by
    simp [powerEntry, unaryState, resultState, hinnerZero]
  have hpowerOne :
      powerEntry.registers oneRegister = 1 := by
    simp [powerEntry, unaryState, resultState, hone]
  have hpowerZero :
      powerEntry.registers zeroRegister = 0 := by
    simp [powerEntry, unaryState, resultState, hzero]
  rw [show 2 + powerFuel factor coefficient degree +
      comparisonFuel target (coefficient * factor ^ degree) + extra =
    powerFuel factor coefficient degree +
      (2 + comparisonFuel target
        (coefficient * factor ^ degree) + extra) by omega]
  change
    runNPOracleProgram
        (selectorProgram coefficient degree sourceOnset)
        maximumBits
        (powerFuel factor coefficient degree +
          (2 + comparisonFuel target
            (coefficient * factor ^ degree) + extra))
        powerEntry =
      _
  rw [run_powerLoop coefficient degree sourceOnset maximumBits
    (2 + comparisonFuel target
      (coefficient * factor ^ degree) + extra)
    factor coefficient degree limit powerEntry hpowerPc hpowerDegree
    hpowerFactor hpowerResult hpowerResultUnary hpowerInnerZero hpowerOne
    hpowerZero hfactorPositive hcoefficientPositive hdegreeBound
    hcoreBound hnat hunary]
  let powered :=
    powerDoneState factor degree coefficient powerEntry
  have hpoweredPc : powered.pc = 22 :=
    powerDoneState_pc factor degree coefficient powerEntry
  have hpoweredTarget :
      powered.registers 0 = encodeUnary target := by
    rw [powerDoneState_preserves factor degree coefficient powerEntry 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [powerEntry, unaryState, resultState, htarget]
  have hpoweredResultUnary :
      powered.registers resultUnaryRegister =
        encodeUnary (coefficient * factor ^ degree) :=
    powerDoneState_resultUnary factor degree coefficient powerEntry
      hpowerResultUnary
  have htargetUnaryBits := hunary target htargetBound
  have hcoreUnaryBits :=
    hunary (coefficient * factor ^ degree) hcoreBound
  rw [show 2 + comparisonFuel target
      (coefficient * factor ^ degree) + extra =
    (1 + comparisonFuel target
      (coefficient * factor ^ degree) + extra) + 1 by omega]
  rw [run_copy_instruction
    (fuel := 1 + comparisonFuel target
      (coefficient * factor ^ degree) + extra)
    (by rfl) hpoweredPc hpoweredTarget htargetUnaryBits]
  let targetState :=
    (powered.write targetCursorRegister
      (encodeUnary target)).jump 23
  rw [show 1 + comparisonFuel target
      (coefficient * factor ^ degree) + extra =
    (comparisonFuel target
      (coefficient * factor ^ degree) + extra) + 1 by omega]
  rw [run_copy_instruction
    (fuel := comparisonFuel target
      (coefficient * factor ^ degree) + extra)
    (by rfl) rfl
    (by simp [hpoweredResultUnary])
    hcoreUnaryBits]
  let compareEntry :=
    (targetState.write coreCursorRegister
      (encodeUnary (coefficient * factor ^ degree))).jump comparePc
  have hcomparePc : compareEntry.pc = comparePc := rfl
  have hcompareTarget :
      compareEntry.registers targetCursorRegister =
        encodeUnary target := by
    simp [compareEntry, targetState]
  have hcompareCore :
      compareEntry.registers coreCursorRegister =
        encodeUnary (coefficient * factor ^ degree) := by
    simp [compareEntry]
  have hcompareZero :
      compareEntry.registers zeroRegister = 0 := by
    rw [show compareEntry.registers zeroRegister =
      powered.registers zeroRegister by
        simp [compareEntry, targetState]]
    rw [powerDoneState_preserves factor degree coefficient powerEntry
      zeroRegister (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hpowerZero
  change
    runNPOracleProgram
        (selectorProgram coefficient degree sourceOnset)
        maximumBits
        (comparisonFuel target
          (coefficient * factor ^ degree) + extra)
        compareEntry =
      _
  rw [run_comparison coefficient degree sourceOnset maximumBits extra
    target (coefficient * factor ^ degree) limit compareEntry
    hcomparePc hcompareTarget hcompareCore hcompareZero htargetBound
    hcoreBound hunary]
  rfl

@[simp] theorem candidateDoneState_pc
    (factor coefficient degree target : ℕ) (state : NPOracleState) :
    (candidateDoneState factor coefficient degree target state).pc =
      if target < 2 * (coefficient * factor ^ degree) then
        emitPc
      else
        advancePc := by
  simp [candidateDoneState]

theorem candidateDoneState_result
    (factor coefficient degree target : ℕ) (state : NPOracleState) :
    (candidateDoneState factor coefficient degree target state).registers
        resultRegister =
      coefficient * factor ^ degree := by
  change
    (comparisonState target (coefficient * factor ^ degree)
      (candidateComparisonEntry factor coefficient degree target state)).registers
        resultRegister =
      coefficient * factor ^ degree
  rw [comparisonState_preserves target (coefficient * factor ^ degree)
    (candidateComparisonEntry factor coefficient degree target state)
    resultRegister (by decide) (by decide)]
  simp only [candidateComparisonEntry]
  exact powerDoneState_result factor degree coefficient
    (candidatePowerEntry coefficient degree state) (by
      simp [candidatePowerEntry])

theorem candidateDoneState_preserves
    (factor coefficient degree target : ℕ) (state : NPOracleState)
    (register : ℕ)
    (hdegree : register ≠ degreeCursorRegister)
    (houter : register ≠ outerCursorRegister)
    (hproduct : register ≠ productRegister)
    (hproductUnary : register ≠ productUnaryRegister)
    (hresult : register ≠ resultRegister)
    (hresultUnary : register ≠ resultUnaryRegister)
    (htarget : register ≠ targetCursorRegister)
    (hcore : register ≠ coreCursorRegister) :
    (candidateDoneState factor coefficient degree target state).registers
        register =
      state.registers register := by
  change
    (comparisonState target (coefficient * factor ^ degree)
      (candidateComparisonEntry factor coefficient degree target state)).registers
        register =
      state.registers register
  rw [comparisonState_preserves target (coefficient * factor ^ degree)
    (candidateComparisonEntry factor coefficient degree target state)
    register htarget hcore]
  simp only [candidateComparisonEntry]
  rw [show
    ((powerDoneState factor degree coefficient
        (candidatePowerEntry coefficient degree state)).write
          targetCursorRegister (encodeUnary target) |>.jump 23 |>.write
            coreCursorRegister
              (encodeUnary (coefficient * factor ^ degree)) |>.jump
                comparePc).registers register =
      (powerDoneState factor degree coefficient
        (candidatePowerEntry coefficient degree state)).registers
          register by
    simp [htarget, hcore]]
  rw [powerDoneState_preserves factor degree coefficient
    (candidatePowerEntry coefficient degree state) register
    hdegree houter hproduct hproductUnary hresult hresultUnary]
  simp [candidatePowerEntry, hdegree, hresult, hresultUnary]

/-! ## Exact scan transitions -/

def advanceDoneState
    (source factor core : ℕ) (state : NPOracleState) : NPOracleState :=
  let previousSourceState :=
    (state.write previousSourceRegister source).jump 32
  let previousCoreState :=
    (previousSourceState.write previousCoreRegister core).jump 33
  let sourceState :=
    (previousCoreState.write sourceRegister (source + 1)).jump 34
  let unaryState :=
    (sourceState.write sourceUnaryRegister
      (encodeUnary (factor + 1))).jump 35
  unaryState.jump candidatePc

theorem run_advance
    (coefficient degree sourceOnset maximumBits extra source factor core : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = advancePc)
    (hsource : state.registers sourceRegister = source)
    (hfactor :
      state.registers sourceUnaryRegister = encodeUnary factor)
    (hcore : state.registers resultRegister = core)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hsourceBits : natBitLength source ≤ maximumBits)
    (hcoreBits : natBitLength core ≤ maximumBits)
    (hsourceSuccBits : natBitLength (source + 1) ≤ maximumBits)
    (hfactorSuccBits :
      natBitLength (encodeUnary (factor + 1)) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (5 + extra) state =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra
        (advanceDoneState source factor core state) := by
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 4 + extra)
    (by rfl) hpc hsource hsourceBits]
  let previousSourceState :=
    (state.write previousSourceRegister source).jump 32
  have hpreviousCore :
      previousSourceState.registers resultRegister = core := by
    simp [previousSourceState, hcore]
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 3 + extra)
    (by rfl) rfl hpreviousCore hcoreBits]
  let previousCoreState :=
    (previousSourceState.write previousCoreRegister core).jump 33
  have hsourceSucc :
      previousCoreState.registers sourceRegister + 1 = source + 1 := by
    simp [previousCoreState, previousSourceState, hsource]
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_increment_instruction (fuel := 2 + extra)
    (by rfl) rfl hsourceSucc hsourceSuccBits]
  let sourceState :=
    (previousCoreState.write sourceRegister (source + 1)).jump 34
  have hpair :
      Nat.pair (sourceState.registers oneRegister)
          (sourceState.registers sourceUnaryRegister) =
        encodeUnary (factor + 1) := by
    simp [sourceState, previousCoreState, previousSourceState,
      hone, hfactor, encodeUnary]
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 1 + extra)
    (by rfl) rfl hpair hfactorSuccBits]
  let unaryState :=
    (sourceState.write sourceUnaryRegister
      (encodeUnary (factor + 1))).jump 35
  have hbranchZero : unaryState.registers zeroRegister = 0 := by
    simp [unaryState, sourceState, previousCoreState,
      previousSourceState, hzero]
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra)
    (by rfl) (show unaryState.pc = 35 by rfl)]
  simp only [hbranchZero, if_pos]
  rfl

def emittedSelection
    (previousSource source previousCore core : ℕ) :
    ExecutableScheduleSelection where
  source := previousSource
  nextSource := source
  core := previousCore
  nextCore := core

theorem run_emit
    (coefficient degree sourceOnset maximumBits extra
      previousSource source previousCore core : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = emitPc)
    (hpreviousSource :
      state.registers previousSourceRegister = previousSource)
    (hsource : state.registers sourceRegister = source)
    (hpreviousCore :
      state.registers previousCoreRegister = previousCore)
    (hcore : state.registers resultRegister = core)
    (hinnerBits :
      natBitLength (Nat.pair previousCore core) ≤ maximumBits)
    (hmiddleBits :
      natBitLength
        (Nat.pair source (Nat.pair previousCore core)) ≤ maximumBits)
    (houtputBits :
      natBitLength
        (emittedSelection previousSource source previousCore core).code ≤
          maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (4 + extra) state =
      some
        (emittedSelection previousSource source previousCore core).code := by
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 3 + extra)
    (by rfl) hpc
    (by simp [hpreviousCore, hcore]) hinnerBits]
  let innerState :=
    (state.write temporaryRegister
      (Nat.pair previousCore core)).jump 37
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 2 + extra)
    (by rfl) rfl
    (by simp [hsource]) hmiddleBits]
  let middleState :=
    (innerState.write temporaryRegister
      (Nat.pair source (Nat.pair previousCore core))).jump 38
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 1 + extra)
    (by rfl) rfl
    (by
      simp [hpreviousSource,
        emittedSelection, ExecutableScheduleSelection.code])
    houtputBits]
  let outputState :=
    (middleState.write 0
      (emittedSelection previousSource source previousCore core).code).jump 39
  rw [show 1 + extra = extra + 1 by omega]
  exact run_halt_instruction
    (program := selectorProgram coefficient degree sourceOnset)
    (fuel := extra) (by rfl) (show outputState.pc = 39 by rfl)
    (by simp) houtputBits

/-! ## Complete first-crossing scan -/

def scanFuel
    (coefficient degree sourceOnset target : ℕ) :
    ℕ → ℕ → ℕ
  | 0, offset =>
      candidateFuel (sourceOnset + offset + 1)
        coefficient degree target + 4
  | gap + 1, offset =>
      candidateFuel (sourceOnset + offset + 1)
          coefficient degree target +
        5 + scanFuel coefficient degree sourceOnset target gap (offset + 1)

def selectorEntryState (sourceOnset target : ℕ) : NPOracleState :=
  let oneState :=
    ((initialNPOracleState target (encodeUnary target)).write
      oneRegister 1).jump 1
  let sourceState :=
    (oneState.write sourceRegister sourceOnset).jump 2
  (sourceState.write sourceUnaryRegister
    (encodeUnary (sourceOnset + 1))).jump candidatePc

theorem run_selector_setup
    (coefficient degree sourceOnset target maximumBits extra : ℕ)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hsourceBits : natBitLength sourceOnset ≤ maximumBits)
    (hfactorBits :
      natBitLength (encodeUnary (sourceOnset + 1)) ≤ maximumBits) :
    runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits (3 + extra)
        (initialNPOracleState target (encodeUnary target)) =
      runNPOracleProgram (selectorProgram coefficient degree sourceOnset)
        maximumBits extra (selectorEntryState sourceOnset target) := by
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 2 + extra) (pc := 0)
    (register := oneRegister) (value := 1) (next := 1)
    (by rfl) (by rfl) honeBits]
  let oneState :=
    ((initialNPOracleState target (encodeUnary target)).write
      oneRegister 1).jump 1
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 1 + extra) (pc := 1)
    (register := sourceRegister) (value := sourceOnset) (next := 2)
    (by rfl) (show oneState.pc = 1 by rfl) hsourceBits]
  let sourceState :=
    (oneState.write sourceRegister sourceOnset).jump 2
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_set_instruction (fuel := extra) (pc := 2)
    (register := sourceUnaryRegister)
    (value := encodeUnary (sourceOnset + 1)) (next := candidatePc)
    (by rfl) (show sourceState.pc = 2 by rfl) hfactorBits]
  rfl

/-- Successful interpreter runs are stable under additional fuel.  The
register-bit budget is unchanged; this lemma only accounts for unused steps
remaining when the fixed program reaches `halt`. -/
theorem runNPOracleProgram_add_fuel_of_some
    {program : NPOracleProgram} {maximumBits fuel extra : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hrun :
      runNPOracleProgram program maximumBits fuel state = some output) :
    runNPOracleProgram program maximumBits (fuel + extra) state =
      some output := by
  induction fuel generalizing state with
  | zero =>
      simp [runNPOracleProgram] at hrun
  | succ fuel ih =>
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      simp only [runNPOracleProgram] at hrun ⊢
      cases hinstruction : program[state.pc]? with
      | none =>
          rw [hinstruction] at hrun
          contradiction
      | some instruction =>
          rw [hinstruction] at hrun
          cases instruction with
          | halt outputRegister =>
              simp only at hrun ⊢
              exact hrun
          | set register value next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits register value with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | copy source destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (state.registers source) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | increment register next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits register
                    (state.registers register + 1) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | decrement register next =>
              simp only at hrun ⊢
              simp only [Nat.pred_eq_sub_one] at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits register
                    (state.registers register - 1) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | add left right destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (state.registers left + state.registers right) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | subtract left right destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (state.registers left - state.registers right) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | pair left right destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (Nat.pair (state.registers left)
                      (state.registers right)) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | unpairLeft source destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (Nat.unpair (state.registers source)).1 with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | unpairRight source destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (Nat.unpair (state.registers source)).2 with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | branchZero register zeroTarget nonzeroTarget =>
              simp only at hrun ⊢
              exact ih hrun
          | encodeNat source destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (CanonicalBinary.encodeNat
                      (state.registers source)) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | shiftRight source amount destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (Nat.shiftRight (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | shiftLeft source amount destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (Nat.shiftLeft (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | testBit source index destination next =>
              simp only at hrun ⊢
              cases hwrite :
                  state.boundedWrite maximumBits destination
                    (((state.registers source).testBit
                      (state.registers index)).toNat) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [hwrite] at hrun
                  exact ih hrun
          | sat queryRegister destination next =>
              simp only at hrun ⊢
              by_cases hquery :
                  natBitLength (state.registers queryRegister) ≤ maximumBits
              · simp only [if_pos hquery] at hrun ⊢
                cases hwrite :
                    state.boundedWrite maximumBits destination
                      (encodedSat
                        (state.registers queryRegister)).toNat with
                | none =>
                    rw [hwrite] at hrun
                    contradiction
                | some nextState =>
                    rw [hwrite] at hrun
                    exact ih hrun
              · simp only [if_neg hquery] at hrun
                contradiction

theorem run_scan_to_firstCrossing
    (coefficient degree target maximumBits limit offset gap : ℕ)
    (data :
      FirstCrossingData (polynomialCore coefficient degree) target)
    (state : NPOracleState)
    (hnext : data.nextOffset = offset + gap)
    (hpc : state.pc = candidatePc)
    (htarget : state.registers 0 = encodeUnary target)
    (hsource :
      state.registers sourceRegister = data.sourceOnset + offset)
    (hfactor :
      state.registers sourceUnaryRegister =
        encodeUnary (data.sourceOnset + offset + 1))
    (hpreviousSource :
      offset = 0 ∨
        state.registers previousSourceRegister =
          data.sourceOnset + offset - 1)
    (hpreviousCore :
      offset = 0 ∨
        state.registers previousCoreRegister =
          polynomialCore coefficient degree
            (data.sourceOnset + offset - 1))
    (hinnerZero : state.registers innerCursorRegister = 0)
    (hone : state.registers oneRegister = 1)
    (hzero : state.registers zeroRegister = 0)
    (hcoefficientPositive : 0 < coefficient)
    (hcoefficientBound : coefficient ≤ limit)
    (hdegreeBound : degree ≤ limit)
    (htargetBound : target ≤ limit)
    (hfactorBound : ∀ candidate ≤ data.nextOffset,
      data.sourceOnset + candidate + 1 ≤ limit)
    (hcoreBound : ∀ candidate ≤ data.nextOffset,
      polynomialCore coefficient degree
        (data.sourceOnset + candidate) ≤ limit)
    (hnat : ∀ value ≤ limit,
      natBitLength value ≤ maximumBits)
    (hunary : ∀ value ≤ limit,
      natBitLength (encodeUnary value) ≤ maximumBits)
    (hemitInnerBits :
      natBitLength
        (Nat.pair
          (polynomialCore coefficient degree data.source)
          (polynomialCore coefficient degree data.nextSource)) ≤
        maximumBits)
    (hemitMiddleBits :
      natBitLength
        (Nat.pair data.nextSource
          (Nat.pair
            (polynomialCore coefficient degree data.source)
            (polynomialCore coefficient degree data.nextSource))) ≤
        maximumBits)
    (hemitOutputBits :
      natBitLength (firstCrossingSelection data).code ≤ maximumBits) :
    runNPOracleProgram
        (selectorProgram coefficient degree data.sourceOnset)
        maximumBits
        (scanFuel coefficient degree data.sourceOnset target gap offset)
        state =
      some (firstCrossingSelection data).code := by
  induction gap generalizing offset state with
  | zero =>
      have hoffset : data.nextOffset = offset := by
        simpa using hnext
      have hoffsetPositive : 0 < offset := by
        rw [← hoffset]
        exact data.nextOffset_positive
      have hoffsetLe : offset ≤ data.nextOffset := by omega
      have hfactorPositive :
          0 < data.sourceOnset + offset + 1 := by omega
      have hcoreExpression :
          coefficient * (data.sourceOnset + offset + 1) ^ degree =
            polynomialCore coefficient degree
              (data.sourceOnset + offset) := by
        rfl
      rw [show
        scanFuel coefficient degree data.sourceOnset target 0 offset =
          candidateFuel (data.sourceOnset + offset + 1)
              coefficient degree target + 4 by rfl]
      rw [run_candidate coefficient degree data.sourceOnset maximumBits 4
        (data.sourceOnset + offset + 1) target limit state
        hpc htarget hfactor hinnerZero hone hzero
        hcoefficientPositive hfactorPositive hcoefficientBound
        hdegreeBound (hfactorBound offset hoffsetLe) htargetBound
        (by simpa only [hcoreExpression] using
          hcoreBound offset hoffsetLe)
        hnat hunary]
      let done :=
        candidateDoneState (data.sourceOnset + offset + 1)
          coefficient degree target state
      have hcross :
          target <
            2 * (coefficient *
              (data.sourceOnset + offset + 1) ^ degree) := by
        simpa [polynomialCore, hoffset] using
          data.crossesAtNextOffset
      have hdonePc : done.pc = emitPc := by
        simp [done, hcross]
      have hdoneSource :
          done.registers sourceRegister =
            data.sourceOnset + offset := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          sourceRegister (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        exact hsource
      have hdoneCore :
          done.registers resultRegister =
            polynomialCore coefficient degree
              (data.sourceOnset + offset) := by
        simpa only [hcoreExpression] using
          candidateDoneState_result
            (data.sourceOnset + offset + 1)
            coefficient degree target state
      have hdonePreviousSource :
          done.registers previousSourceRegister =
            data.sourceOnset + offset - 1 := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          previousSourceRegister (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hpreviousSource.resolve_left (by omega)
      have hdonePreviousCore :
          done.registers previousCoreRegister =
            polynomialCore coefficient degree
              (data.sourceOnset + offset - 1) := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          previousCoreRegister (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hpreviousCore.resolve_left (by omega)
      have hsourceSub :
          data.sourceOnset + offset - 1 =
            data.sourceOnset + (offset - 1) := by
        omega
      have hselection :
          emittedSelection
              (data.sourceOnset + offset - 1)
              (data.sourceOnset + offset)
              (polynomialCore coefficient degree
                (data.sourceOnset + offset - 1))
              (polynomialCore coefficient degree
                (data.sourceOnset + offset)) =
            firstCrossingSelection data := by
        simp [emittedSelection, firstCrossingSelection,
          FirstCrossingData.source, FirstCrossingData.nextSource,
          FirstCrossingData.sourceOffset, hoffset, hsourceSub]
      rw [run_emit coefficient degree data.sourceOnset maximumBits 0
        (data.sourceOnset + offset - 1)
        (data.sourceOnset + offset)
        (polynomialCore coefficient degree
          (data.sourceOnset + offset - 1))
        (polynomialCore coefficient degree
          (data.sourceOnset + offset))
        done hdonePc hdonePreviousSource hdoneSource
        hdonePreviousCore hdoneCore]
      · simp only [hselection]
      · simpa [FirstCrossingData.source, FirstCrossingData.nextSource,
          FirstCrossingData.sourceOffset, hoffset, hsourceSub] using
          hemitInnerBits
      · simpa [FirstCrossingData.source, FirstCrossingData.nextSource,
          FirstCrossingData.sourceOffset, hoffset, hsourceSub] using
          hemitMiddleBits
      · simpa only [hselection] using hemitOutputBits
  | succ gap ih =>
      have hoffsetBefore : offset < data.nextOffset := by
        omega
      have hoffsetLe : offset ≤ data.nextOffset := by omega
      have hnextOffsetLe : offset + 1 ≤ data.nextOffset := by omega
      have hnotCross :
          ¬target <
            2 * polynomialCore coefficient degree
              (data.sourceOnset + offset) := by
        exact Nat.find_min data.crossingExists hoffsetBefore
      have hfactorPositive :
          0 < data.sourceOnset + offset + 1 := by omega
      have hcoreExpression :
          coefficient * (data.sourceOnset + offset + 1) ^ degree =
            polynomialCore coefficient degree
              (data.sourceOnset + offset) := by
        rfl
      let remaining :=
        scanFuel coefficient degree data.sourceOnset target
          gap (offset + 1)
      rw [show
        scanFuel coefficient degree data.sourceOnset target
            (gap + 1) offset =
          candidateFuel (data.sourceOnset + offset + 1)
              coefficient degree target +
            (5 + remaining) by
          simp [scanFuel, remaining, Nat.add_assoc]]
      rw [run_candidate coefficient degree data.sourceOnset maximumBits
        (5 + remaining) (data.sourceOnset + offset + 1) target limit
        state hpc htarget hfactor hinnerZero hone hzero
        hcoefficientPositive hfactorPositive hcoefficientBound
        hdegreeBound (hfactorBound offset hoffsetLe) htargetBound
        (by simpa only [hcoreExpression] using
          hcoreBound offset hoffsetLe)
        hnat hunary]
      let done :=
        candidateDoneState (data.sourceOnset + offset + 1)
          coefficient degree target state
      have hdonePc : done.pc = advancePc := by
        simp [done, hcoreExpression, hnotCross]
      have hdoneSource :
          done.registers sourceRegister =
            data.sourceOnset + offset := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          sourceRegister (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        exact hsource
      have hdoneFactor :
          done.registers sourceUnaryRegister =
            encodeUnary (data.sourceOnset + offset + 1) := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          sourceUnaryRegister (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hfactor
      have hdoneCore :
          done.registers resultRegister =
            polynomialCore coefficient degree
              (data.sourceOnset + offset) := by
        simpa only [hcoreExpression] using
          candidateDoneState_result
            (data.sourceOnset + offset + 1)
            coefficient degree target state
      have hdoneOne : done.registers oneRegister = 1 := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          oneRegister (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        exact hone
      have hdoneZero : done.registers zeroRegister = 0 := by
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          zeroRegister (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        exact hzero
      rw [show 5 + remaining = 5 + remaining by rfl]
      rw [run_advance coefficient degree data.sourceOnset maximumBits
        remaining (data.sourceOnset + offset)
        (data.sourceOnset + offset + 1)
        (polynomialCore coefficient degree
          (data.sourceOnset + offset))
        done hdonePc hdoneSource hdoneFactor hdoneCore hdoneOne hdoneZero
        (hnat _ (by
          exact (Nat.le_add_right _ 1).trans
            (hfactorBound offset hoffsetLe)))
        (hnat _ (hcoreBound offset hoffsetLe))
        (hnat _ (hfactorBound offset hoffsetLe))
        (hunary _ (by
          simpa [Nat.add_assoc] using
            hfactorBound (offset + 1) hnextOffsetLe))]
      let nextState :=
        advanceDoneState
          (data.sourceOnset + offset)
          (data.sourceOnset + offset + 1)
          (polynomialCore coefficient degree
            (data.sourceOnset + offset))
          done
      apply ih (offset := offset + 1) (state := nextState)
      · omega
      · rfl
      · simp [nextState, advanceDoneState, done,
          candidateDoneState_preserves, htarget]
      · simp [nextState, advanceDoneState, Nat.add_assoc]
      · simp [nextState, advanceDoneState, Nat.add_assoc]
      · right
        simp [nextState, advanceDoneState]
      · right
        simp [nextState, advanceDoneState]
      · rw [show nextState.registers innerCursorRegister =
          done.registers innerCursorRegister by
            simp [nextState, advanceDoneState]]
        rw [candidateDoneState_preserves
          (data.sourceOnset + offset + 1) coefficient degree target state
          innerCursorRegister (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hinnerZero
      · simp [nextState, advanceDoneState, hdoneOne]
      · simp [nextState, advanceDoneState, hdoneZero]

/-! ## Uniform resource envelope -/

@[simp] theorem innerFuel_eq (count : ℕ) :
    innerFuel count = 5 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [innerFuel, ih]
      omega

@[simp] theorem outerFuel_eq (factor count : ℕ) :
    outerFuel factor count =
      (3 + innerFuel factor) * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [outerFuel, ih]
      ring

theorem outerFuel_le
    {factor count limit : ℕ}
    (hfactor : factor ≤ limit)
    (hcount : count ≤ limit) :
    outerFuel factor count ≤ 10 * (limit + 1) ^ 2 := by
  rw [outerFuel_eq, innerFuel_eq]
  have hfactor' : 5 * factor + 4 ≤ 5 * (limit + 1) + 4 := by
    omega
  have hcount' : count ≤ limit + 1 := by omega
  have hmul :
      (5 * factor + 4) * count ≤
        (5 * (limit + 1) + 4) * (limit + 1) :=
    Nat.mul_le_mul hfactor' hcount'
  calc
    (3 + (5 * factor + 1)) * count + 1 =
        (5 * factor + 4) * count + 1 := by ring
    _ ≤ (5 * (limit + 1) + 4) * (limit + 1) + 1 :=
      Nat.add_le_add_right hmul 1
    _ ≤ 10 * (limit + 1) ^ 2 := by nlinarith

theorem powerFuel_le
    {factor value degree limit : ℕ}
    (hfactorPositive : 0 < factor)
    (hvaluePositive : 0 < value)
    (hfactor : factor ≤ limit)
    (hdegree : degree ≤ limit)
    (hbound : value * factor ^ degree ≤ limit) :
    powerFuel factor value degree ≤
      20 * (degree + 1) * (limit + 1) ^ 2 := by
  induction degree generalizing value with
  | zero =>
      simp [powerFuel]
      have hone : 1 ≤ (limit + 1) ^ 2 :=
        one_le_pow₀ (by omega)
      nlinarith
  | succ degree ih =>
      have hpowPositive : 0 < factor ^ (degree + 1) :=
        pow_pos hfactorPositive _
      have hvalueLe : value ≤ limit :=
        (Nat.le_mul_of_pos_right value hpowPositive).trans hbound
      have hrecursiveBound :
          value * factor * factor ^ degree ≤ limit := by
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using hbound
      have hrecursive :=
        ih (value := value * factor)
          (Nat.mul_pos hvaluePositive hfactorPositive)
          (by omega) hrecursiveBound
      have houter := outerFuel_le hfactor hvalueLe
      simp only [powerFuel]
      have hsquarePositive : 0 < (limit + 1) ^ 2 := by positivity
      nlinarith

theorem comparisonFuel_le (target core : ℕ) :
    comparisonFuel target core ≤ 7 * (target + core + 1) := by
  induction core generalizing target with
  | zero =>
      simp [comparisonFuel]
      omega
  | succ core ih =>
      cases target with
      | zero =>
          simp [comparisonFuel]
          omega
      | succ target =>
          cases target with
          | zero =>
              simp [comparisonFuel]
              omega
          | succ target =>
              simp only [comparisonFuel]
              have hrecursive := ih target
              omega

theorem candidateFuel_le
    {factor coefficient degree target core limit : ℕ}
    (hfactorPositive : 0 < factor)
    (hcoefficientPositive : 0 < coefficient)
    (hfactor : factor ≤ limit)
    (_hcoefficient : coefficient ≤ limit)
    (hdegree : degree ≤ limit)
    (htarget : target ≤ limit)
    (hcore : coefficient * factor ^ degree = core)
    (hcoreBound : core ≤ limit) :
    candidateFuel factor coefficient degree target ≤
      40 * (limit + 1) ^ 3 := by
  have hpower :=
    powerFuel_le hfactorPositive hcoefficientPositive
      hfactor hdegree (by simpa only [hcore] using hcoreBound)
  have hcomparison := comparisonFuel_le target core
  rw [candidateFuel, hcore]
  have hdegreeSucc : degree + 1 ≤ limit + 1 := by omega
  have hpowerCubic :
      20 * (degree + 1) * (limit + 1) ^ 2 ≤
        20 * (limit + 1) ^ 3 := by
    calc
      20 * (degree + 1) * (limit + 1) ^ 2 ≤
          20 * (limit + 1) * (limit + 1) ^ 2 :=
        Nat.mul_le_mul_right ((limit + 1) ^ 2)
          (Nat.mul_le_mul_left 20 hdegreeSucc)
      _ = 20 * (limit + 1) ^ 3 := by ring
  have hcomparisonLinear :
      7 * (target + core + 1) ≤ 14 * (limit + 1) := by
    omega
  have hlinearCubic :
      14 * (limit + 1) ≤ 14 * (limit + 1) ^ 3 := by
    have hone : 1 ≤ (limit + 1) ^ 2 :=
      one_le_pow₀ (by omega)
    calc
      14 * (limit + 1) =
          14 * (limit + 1) * 1 := by ring
      _ ≤ 14 * (limit + 1) * (limit + 1) ^ 2 :=
        Nat.mul_le_mul_left (14 * (limit + 1)) hone
      _ = 14 * (limit + 1) ^ 3 := by ring
  have hcubicPositive : 1 ≤ (limit + 1) ^ 3 :=
    one_le_pow₀ (by omega)
  nlinarith

theorem scanFuel_le
    {coefficient degree sourceOnset target gap offset horizon limit : ℕ}
    (hcoefficientPositive : 0 < coefficient)
    (hcoefficient : coefficient ≤ limit)
    (hdegree : degree ≤ limit)
    (htarget : target ≤ limit)
    (hrange : offset + gap ≤ horizon)
    (hfactor : ∀ candidate ≤ horizon,
      sourceOnset + candidate + 1 ≤ limit)
    (hcore : ∀ candidate ≤ horizon,
      polynomialCore coefficient degree
        (sourceOnset + candidate) ≤ limit) :
    scanFuel coefficient degree sourceOnset target gap offset ≤
      45 * (gap + 1) * (limit + 1) ^ 3 := by
  induction gap generalizing offset with
  | zero =>
      have hoffset : offset ≤ horizon := by omega
      have hcandidate :=
        candidateFuel_le
          (hfactorPositive := by omega)
          hcoefficientPositive
          (hfactor offset hoffset) hcoefficient hdegree htarget
          (core := polynomialCore coefficient degree
            (sourceOnset + offset))
          (by rfl) (hcore offset hoffset)
      simp only [scanFuel]
      have hcubicPositive : 1 ≤ (limit + 1) ^ 3 :=
        one_le_pow₀ (by omega)
      nlinarith
  | succ gap ih =>
      have hoffset : offset ≤ horizon := by omega
      have hnextRange : offset + 1 + gap ≤ horizon := by omega
      have hcandidate :=
        candidateFuel_le
          (hfactorPositive := by omega)
          hcoefficientPositive
          (hfactor offset hoffset) hcoefficient hdegree htarget
          (core := polynomialCore coefficient degree
            (sourceOnset + offset))
          (by rfl) (hcore offset hoffset)
      have hrecursive := ih (offset := offset + 1) hnextRange
      simp only [scanFuel]
      have hcubicPositive : 1 ≤ (limit + 1) ^ 3 :=
        one_le_pow₀ (by omega)
      nlinarith

def selectorScale (coefficient degree : ℕ) : ℕ :=
  coefficient + degree + polynomialSourceOnset degree +
    polynomialCore coefficient degree (polynomialSourceOnset degree) + 16

def selectorExponent (coefficient degree : ℕ) : ℕ :=
  16 * (selectorScale coefficient degree + 1)

def selectorLimit (coefficient degree target : ℕ) : ℕ :=
  selectorScale coefficient degree * (target + 1)

theorem selectorScale_positive (coefficient degree : ℕ) :
    0 < selectorScale coefficient degree := by
  simp [selectorScale]

theorem selectorExponent_positive (coefficient degree : ℕ) :
    0 < selectorExponent coefficient degree := by
  simp [selectorExponent]

theorem natBitLength_le_succ (value : ℕ) :
    natBitLength value ≤ value + 1 := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_le_self 2 value)

theorem succ_le_two_pow_succ (value : ℕ) :
    value + 1 ≤ 2 ^ (value + 1) := by
  induction value with
  | zero => norm_num
  | succ value ih =>
      calc
        value + 2 ≤ 2 * (value + 1) := by omega
        _ ≤ 2 * 2 ^ (value + 1) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (value + 2) := by ring

theorem selectorLimit_add_one_le_exponent
    (coefficient degree target : ℕ) :
    selectorLimit coefficient degree target + 1 ≤
      selectorExponent coefficient degree * (target + 1) := by
  unfold selectorLimit selectorExponent
  have hmeasure : 1 ≤ target + 1 := by omega
  have hscale := selectorScale_positive coefficient degree
  nlinarith

theorem eight_selectorLimit_add_one_le_exponent
    (coefficient degree target : ℕ) :
    8 * (selectorLimit coefficient degree target + 1) ≤
      selectorExponent coefficient degree * (target + 1) := by
  let scale := selectorScale coefficient degree
  have hmeasure : 1 ≤ target + 1 := by omega
  have hstep :
      scale * (target + 1) + 1 ≤
        (scale + 1) * (target + 1) := by
    rw [add_mul, one_mul]
    omega
  calc
    8 * (selectorLimit coefficient degree target + 1) =
        8 * (scale * (target + 1) + 1) := by
      rfl
    _ ≤ 8 * ((scale + 1) * (target + 1)) :=
      Nat.mul_le_mul_left 8 hstep
    _ ≤ 16 * ((scale + 1) * (target + 1)) := by omega
    _ = selectorExponent coefficient degree * (target + 1) := by
      simp [selectorExponent, scale]
      ring

theorem natBits_le_selectorBudget
    (coefficient degree target value : ℕ)
    (hvalue : value ≤ selectorLimit coefficient degree target) :
    natBitLength value ≤
      exponentialBudget (selectorExponent coefficient degree)
        (target + 1) := by
  have hbits := natBitLength_le_succ value
  have hsucc :
      value + 1 ≤ selectorLimit coefficient degree target + 1 := by
    omega
  have htwo :=
    succ_le_two_pow_succ
      (selectorLimit coefficient degree target)
  have hexponent :=
    selectorLimit_add_one_le_exponent coefficient degree target
  unfold exponentialBudget
  exact hbits.trans <| hsucc.trans <| htwo.trans <|
    Nat.pow_le_pow_right (by omega) hexponent

theorem unaryBits_le_selectorBudget
    (coefficient degree target value : ℕ)
    (hvalue : value ≤ selectorLimit coefficient degree target) :
    natBitLength (encodeUnary value) ≤
      exponentialBudget (selectorExponent coefficient degree)
        (target + 1) := by
  have hbits := natBitLength_encodeUnary_le_twoPow value
  have hexponent :
      value ≤ selectorExponent coefficient degree * (target + 1) :=
    hvalue.trans <| (Nat.le_succ _).trans
      (selectorLimit_add_one_le_exponent coefficient degree target)
  unfold exponentialBudget
  exact hbits.trans
    (Nat.pow_le_pow_right (by omega) hexponent)

theorem pair_add_one_le_square
    {left right bound : ℕ}
    (hleft : left + 1 ≤ bound)
    (hright : right + 1 ≤ bound) :
    Nat.pair left right + 1 ≤ bound ^ 2 := by
  have hmax : max left right + 1 ≤ bound := by
    rw [← max_add_add_right]
    exact max_le hleft hright
  exact Nat.succ_le_iff.mpr <|
    (Nat.pair_lt_max_add_one_sq left right).trans_le
      (Nat.pow_le_pow_left hmax 2)

theorem selectionBits_le_selectorBudget
    (coefficient degree target : ℕ)
    (selection : ExecutableScheduleSelection)
    (hsource :
      selection.source ≤ selectorLimit coefficient degree target)
    (hnextSource :
      selection.nextSource ≤ selectorLimit coefficient degree target)
    (hcore :
      selection.core ≤ selectorLimit coefficient degree target)
    (hnextCore :
      selection.nextCore ≤ selectorLimit coefficient degree target) :
    let budget :=
      exponentialBudget (selectorExponent coefficient degree) (target + 1)
    natBitLength (Nat.pair selection.core selection.nextCore) ≤ budget ∧
      natBitLength
        (Nat.pair selection.nextSource
          (Nat.pair selection.core selection.nextCore)) ≤ budget ∧
      natBitLength selection.code ≤ budget := by
  let limit := selectorLimit coefficient degree target
  let base := limit + 1
  let inner := Nat.pair selection.core selection.nextCore
  let middle := Nat.pair selection.nextSource inner
  have hsourceSucc : selection.source + 1 ≤ base := by
    simp [base, limit]
    omega
  have hnextSourceSucc : selection.nextSource + 1 ≤ base := by
    simp [base, limit]
    omega
  have hcoreSucc : selection.core + 1 ≤ base := by
    simp [base, limit]
    omega
  have hnextCoreSucc : selection.nextCore + 1 ≤ base := by
    simp [base, limit]
    omega
  have hinner : inner + 1 ≤ base ^ 2 :=
    pair_add_one_le_square hcoreSucc hnextCoreSucc
  have hbaseSquare : base ≤ base ^ 2 := by
    have hbasePositive : 0 < base := by
      simp [base]
    simpa [pow_two] using
      Nat.le_mul_of_pos_right base hbasePositive
  have hmiddle : middle + 1 ≤ base ^ 4 := by
    have hnextSourceSquare :
        selection.nextSource + 1 ≤ base ^ 2 :=
      hnextSourceSucc.trans hbaseSquare
    have :=
      pair_add_one_le_square hnextSourceSquare hinner
    calc
      middle + 1 ≤ (base ^ 2) ^ 2 := this
      _ = base ^ (2 * 2) := (pow_mul base 2 2).symm
      _ = base ^ 4 := by norm_num
  have hbaseFourth : base ≤ base ^ 4 := by
    have hbaseOne : 1 ≤ base ^ 3 :=
      one_le_pow₀ (by simp [base])
    calc
      base = base * 1 := by ring
      _ ≤ base * base ^ 3 := Nat.mul_le_mul_left base hbaseOne
      _ = base ^ 4 := by ring
  have houtput :
      selection.code + 1 ≤ base ^ 8 := by
    have hsourceFourth :
        selection.source + 1 ≤ base ^ 4 :=
      hsourceSucc.trans hbaseFourth
    have hpair :=
      pair_add_one_le_square hsourceFourth hmiddle
    calc
      selection.code + 1 =
          Nat.pair selection.source middle + 1 := by
        rfl
      _ ≤ (base ^ 4) ^ 2 := hpair
      _ = base ^ (4 * 2) := (pow_mul base 4 2).symm
      _ = base ^ 8 := by norm_num
  have hbasePow :
      base ^ 8 ≤ 2 ^ (8 * base) := by
    have hbaseTwo : base ≤ 2 ^ base := by
      simpa [base] using succ_le_two_pow_succ limit
    calc
      base ^ 8 ≤ (2 ^ base) ^ 8 :=
        Nat.pow_le_pow_left hbaseTwo 8
      _ = 2 ^ (base * 8) := (pow_mul 2 base 8).symm
      _ = 2 ^ (8 * base) := by rw [Nat.mul_comm]
  have hexponent :
      8 * base ≤ selectorExponent coefficient degree * (target + 1) := by
    simpa [base, limit] using
      eight_selectorLimit_add_one_le_exponent
        coefficient degree target
  have hbudget :
      base ^ 8 ≤
        exponentialBudget (selectorExponent coefficient degree)
          (target + 1) := by
    unfold exponentialBudget
    exact hbasePow.trans
      (Nat.pow_le_pow_right (by omega) hexponent)
  have hinnerBits : natBitLength inner ≤ inner + 1 :=
    natBitLength_le_succ inner
  have hmiddleBits : natBitLength middle ≤ middle + 1 :=
    natBitLength_le_succ middle
  have houtputBits :
      natBitLength selection.code ≤ selection.code + 1 :=
    natBitLength_le_succ selection.code
  have htwoEight : base ^ 2 ≤ base ^ 8 :=
    Nat.pow_le_pow_right (by simp [base]) (by omega)
  have hfourEight : base ^ 4 ≤ base ^ 8 :=
    Nat.pow_le_pow_right (by simp [base]) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact hinnerBits.trans (hinner.trans (htwoEight.trans hbudget))
  · exact hmiddleBits.trans (hmiddle.trans (hfourEight.trans hbudget))
  · exact houtputBits.trans (houtput.trans hbudget)

theorem coefficient_le_selectorScale (coefficient degree : ℕ) :
    coefficient ≤ selectorScale coefficient degree := by
  unfold selectorScale
  omega

theorem degree_le_selectorScale (coefficient degree : ℕ) :
    degree ≤ selectorScale coefficient degree := by
  unfold selectorScale
  omega

theorem sourceOnset_succ_le_selectorScale (coefficient degree : ℕ) :
    polynomialSourceOnset degree + 1 ≤
      selectorScale coefficient degree := by
  unfold selectorScale
  omega

theorem initialCore_le_selectorScale (coefficient degree : ℕ) :
    polynomialCore coefficient degree (polynomialSourceOnset degree) ≤
      selectorScale coefficient degree := by
  unfold selectorScale
  omega

theorem seven_le_selectorScale (coefficient degree : ℕ) :
    7 ≤ selectorScale coefficient degree := by
  unfold selectorScale
  omega

theorem selectorScale_le_limit (coefficient degree target : ℕ) :
    selectorScale coefficient degree ≤
      selectorLimit coefficient degree target := by
  unfold selectorLimit
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem target_le_selectorLimit (coefficient degree target : ℕ) :
    target ≤ selectorLimit coefficient degree target := by
  unfold selectorLimit
  have hscale := selectorScale_positive coefficient degree
  have hmeasure :
      target + 1 ≤ selectorScale coefficient degree * (target + 1) := by
    simpa [Nat.mul_comm] using
      Nat.le_mul_of_pos_right (target + 1) hscale
  omega

theorem polynomialFirstCrossing_resourceBounds
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    let data :=
      polynomialFirstCrossingData coefficient degree target
        hcoefficient hdegree htarget
    data.nextOffset ≤ target ∧
      data.source ≤ selectorLimit coefficient degree target ∧
      data.nextSource ≤ selectorLimit coefficient degree target ∧
      polynomialCore coefficient degree data.source ≤
        selectorLimit coefficient degree target ∧
      polynomialCore coefficient degree data.nextSource ≤
        selectorLimit coefficient degree target := by
  let data :=
    polynomialFirstCrossingData coefficient degree target
      hcoefficient hdegree htarget
  have hnextOffset :
      data.nextOffset ≤ target :=
    polynomialFirstCrossingData_nextOffset_le_target
      coefficient degree target hcoefficient hdegree htarget
  have honsetScale :=
    sourceOnset_succ_le_selectorScale coefficient degree
  have honsetTarget :
      polynomialSourceOnset degree + target + 1 ≤
        selectorLimit coefficient degree target := by
    calc
      polynomialSourceOnset degree + target + 1 ≤
          (polynomialSourceOnset degree + 1) * (target + 1) := by
        nlinarith
      _ ≤ selectorScale coefficient degree * (target + 1) :=
        Nat.mul_le_mul_right (target + 1) honsetScale
      _ = selectorLimit coefficient degree target := rfl
  have hnextSource :
      data.nextSource ≤ selectorLimit coefficient degree target := by
    change
      polynomialSourceOnset degree + data.nextOffset ≤
        selectorLimit coefficient degree target
    omega
  have hsource :
      data.source ≤ selectorLimit coefficient degree target :=
    data.sourceBeforeNext.le.trans hnextSource
  have hcore :
      polynomialCore coefficient degree data.source ≤
        selectorLimit coefficient degree target :=
    data.coreAtMostTarget.trans
      (target_le_selectorLimit coefficient degree target)
  have hnextCoreRaw :
      polynomialCore coefficient degree data.nextSource ≤ 7 * target := by
    have hjump := data.jumpAtMostSixth
    have hnextPositive :
        0 < polynomialCore coefficient degree data.nextSource := by
      have hcross := data.crossesHalf
      omega
    have hsourceCore := data.coreAtMostTarget
    omega
  have hnextCore :
      polynomialCore coefficient degree data.nextSource ≤
        selectorLimit coefficient degree target := by
    apply hnextCoreRaw.trans
    calc
      7 * target ≤ 7 * (target + 1) := by omega
      _ ≤ selectorScale coefficient degree * (target + 1) :=
        Nat.mul_le_mul_right (target + 1)
          (seven_le_selectorScale coefficient degree)
      _ = selectorLimit coefficient degree target := rfl
  exact ⟨hnextOffset, hsource, hnextSource, hcore, hnextCore⟩

theorem fortyEightFourth_le_selectorBudget
    (coefficient degree target : ℕ) :
    48 * (selectorLimit coefficient degree target + 1) ^ 4 ≤
      exponentialBudget (selectorExponent coefficient degree)
        (target + 1) := by
  let limit := selectorLimit coefficient degree target
  let base := limit + 1
  have hbaseTwo : base ≤ 2 ^ base := by
    simpa [base] using succ_le_two_pow_succ limit
  have hpoly :
      48 * base ^ 4 ≤ 2 ^ (6 + 4 * base) := by
    have hcoefficient : 48 ≤ 2 ^ 6 := by norm_num
    have hpower :
        base ^ 4 ≤ (2 ^ base) ^ 4 :=
      Nat.pow_le_pow_left hbaseTwo 4
    calc
      48 * base ^ 4 ≤ 2 ^ 6 * (2 ^ base) ^ 4 :=
        Nat.mul_le_mul hcoefficient hpower
      _ = 2 ^ 6 * 2 ^ (base * 4) := by
        rw [← pow_mul]
      _ = 2 ^ (6 + base * 4) := by rw [pow_add]
      _ = 2 ^ (6 + 4 * base) := by rw [Nat.mul_comm]
  have hbaseLarge : 2 ≤ base := by
    dsimp [base, limit]
    have hscale := selectorScale_positive coefficient degree
    have hscaleLimit :=
      selectorScale_le_limit coefficient degree target
    omega
  have hexponent :
      6 + 4 * base ≤
        selectorExponent coefficient degree * (target + 1) := by
    have height :=
      eight_selectorLimit_add_one_le_exponent
        coefficient degree target
    change
      8 * base ≤
        selectorExponent coefficient degree * (target + 1) at height
    omega
  unfold exponentialBudget
  exact hpoly.trans
    (Nat.pow_le_pow_right (by omega) hexponent)

theorem setupScanFuel_le_selectorBudget
    {coefficient degree target gap offset : ℕ}
    (hgap : gap ≤ target)
    (hscan :
      scanFuel coefficient degree (polynomialSourceOnset degree)
          target gap offset ≤
        45 * (gap + 1) *
          (selectorLimit coefficient degree target + 1) ^ 3) :
    3 +
        scanFuel coefficient degree (polynomialSourceOnset degree)
          target gap offset ≤
      exponentialBudget (selectorExponent coefficient degree)
        (target + 1) := by
  let base := selectorLimit coefficient degree target + 1
  have hgapBase : gap + 1 ≤ base := by
    dsimp [base]
    have := target_le_selectorLimit coefficient degree target
    omega
  have hscanFourth :
      scanFuel coefficient degree (polynomialSourceOnset degree)
          target gap offset ≤
        45 * base ^ 4 := by
    apply hscan.trans
    calc
      45 * (gap + 1) * base ^ 3 ≤ 45 * base * base ^ 3 :=
        Nat.mul_le_mul_right (base ^ 3)
          (Nat.mul_le_mul_left 45 hgapBase)
      _ = 45 * base ^ 4 := by ring
  have hbaseFourth : 1 ≤ base ^ 4 :=
    one_le_pow₀ (by simp [base])
  apply (show
    3 +
        scanFuel coefficient degree (polynomialSourceOnset degree)
          target gap offset ≤
      48 * base ^ 4 by nlinarith).trans
  simpa [base] using
    fortyEightFourth_le_selectorBudget coefficient degree target

theorem run_selector_at_firstCrossing
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    let data :=
      polynomialFirstCrossingData coefficient degree target
        hcoefficient hdegree htarget
    let budget :=
      exponentialBudget (selectorExponent coefficient degree) (target + 1)
    runNPOracleProgram
        (selectorProgram coefficient degree (polynomialSourceOnset degree))
        budget budget
        (initialNPOracleState target (encodeUnary target)) =
      some (firstCrossingSelection data).code := by
  let data :=
    polynomialFirstCrossingData coefficient degree target
      hcoefficient hdegree htarget
  let limit := selectorLimit coefficient degree target
  let budget :=
    exponentialBudget (selectorExponent coefficient degree) (target + 1)
  obtain
      ⟨hnextOffset, hsource, hnextSource, hcore, hnextCore⟩ :=
    polynomialFirstCrossing_resourceBounds
      coefficient degree target hcoefficient hdegree htarget
  have hcoefficientLimit : coefficient ≤ limit := by
    exact (coefficient_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have hdegreeLimit : degree ≤ limit := by
    exact (degree_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have htargetLimit : target ≤ limit := by
    exact target_le_selectorLimit coefficient degree target
  have hfactorLimit :
      ∀ candidate ≤ data.nextOffset,
        data.sourceOnset + candidate + 1 ≤ limit := by
    intro candidate hcandidate
    have hcandidateTarget : candidate ≤ target :=
      hcandidate.trans hnextOffset
    have honsetScale :=
      sourceOnset_succ_le_selectorScale coefficient degree
    change
      polynomialSourceOnset degree + candidate + 1 ≤ limit
    calc
      polynomialSourceOnset degree + candidate + 1 ≤
          (polynomialSourceOnset degree + 1) * (target + 1) := by
        nlinarith
      _ ≤ selectorScale coefficient degree * (target + 1) :=
        Nat.mul_le_mul_right (target + 1) honsetScale
      _ = limit := rfl
  have hcoreLimit :
      ∀ candidate ≤ data.nextOffset,
        polynomialCore coefficient degree
          (data.sourceOnset + candidate) ≤ limit := by
    intro candidate hcandidate
    have hsourceLe :
        data.sourceOnset + candidate ≤ data.nextSource := by
      unfold FirstCrossingData.nextSource
      omega
    exact (data.monotone hsourceLe).trans hnextCore
  have hnat :
      ∀ value ≤ limit, natBitLength value ≤ budget := by
    intro value hvalue
    simpa [limit, budget] using
      natBits_le_selectorBudget coefficient degree target value hvalue
  have hunary :
      ∀ value ≤ limit,
        natBitLength (encodeUnary value) ≤ budget := by
    intro value hvalue
    simpa [limit, budget] using
      unaryBits_le_selectorBudget coefficient degree target value hvalue
  have hselectionBits :=
    selectionBits_le_selectorBudget coefficient degree target
      (firstCrossingSelection data) hsource hnextSource hcore hnextCore
  have hscan :
      scanFuel coefficient degree (polynomialSourceOnset degree)
          target data.nextOffset 0 ≤
        45 * (data.nextOffset + 1) * (limit + 1) ^ 3 := by
    apply scanFuel_le hcoefficient hcoefficientLimit hdegreeLimit
      htargetLimit (horizon := data.nextOffset)
    · omega
    · intro candidate hcandidate
      exact hfactorLimit candidate hcandidate
    · intro candidate hcandidate
      exact hcoreLimit candidate hcandidate
  let exactFuel :=
    3 + scanFuel coefficient degree (polynomialSourceOnset degree)
      target data.nextOffset 0
  have hexact :
      runNPOracleProgram
          (selectorProgram coefficient degree
            (polynomialSourceOnset degree))
          budget exactFuel
          (initialNPOracleState target (encodeUnary target)) =
        some (firstCrossingSelection data).code := by
    rw [show exactFuel =
      3 + scanFuel coefficient degree (polynomialSourceOnset degree)
        target data.nextOffset 0 by rfl]
    rw [run_selector_setup coefficient degree
      (polynomialSourceOnset degree) target budget
      (scanFuel coefficient degree (polynomialSourceOnset degree)
        target data.nextOffset 0)]
    · apply run_scan_to_firstCrossing coefficient degree target budget limit
        0 data.nextOffset data (selectorEntryState
          (polynomialSourceOnset degree) target)
      · omega
      · rfl
      · simp [selectorEntryState, initialNPOracleState]
      · simp [selectorEntryState, data, polynomialFirstCrossingData]
      · simp [selectorEntryState, data, polynomialFirstCrossingData]
      · exact Or.inl rfl
      · exact Or.inl rfl
      · simp [selectorEntryState, initialNPOracleState]
      · simp [selectorEntryState]
      · simp [selectorEntryState, initialNPOracleState]
      · exact hcoefficient
      · exact hcoefficientLimit
      · exact hdegreeLimit
      · exact htargetLimit
      · exact hfactorLimit
      · exact hcoreLimit
      · exact hnat
      · exact hunary
      · simpa [budget, firstCrossingSelection] using hselectionBits.1
      · simpa [budget, firstCrossingSelection] using hselectionBits.2.1
      · simpa [budget] using hselectionBits.2.2
    · exact hnat 1 (by
        exact (Nat.one_le_of_lt
          (selectorScale_positive coefficient degree)).trans
          (selectorScale_le_limit coefficient degree target))
    · exact hnat _ (by
        exact (Nat.le_of_lt
          (sourceOnset_succ_le_selectorScale coefficient degree)).trans
            (selectorScale_le_limit coefficient degree target))
    · exact hunary _ (by
        exact (sourceOnset_succ_le_selectorScale coefficient degree).trans
          (selectorScale_le_limit coefficient degree target))
  have hfuel : exactFuel ≤ budget := by
    apply setupScanFuel_le_selectorBudget hnextOffset
    simpa [limit] using hscan
  have hmore :=
    runNPOracleProgram_add_fuel_of_some
      (extra := budget - exactFuel) hexact
  simpa [Nat.add_sub_of_le hfuel] using hmore

theorem run_selector_belowOnset
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (_hdegree : 0 < degree)
    (htarget :
      target <
        2 * polynomialCore coefficient degree
          (polynomialSourceOnset degree)) :
    let selection :=
      emittedSelection 0 (polynomialSourceOnset degree) 0
        (polynomialCore coefficient degree
          (polynomialSourceOnset degree))
    let budget :=
      exponentialBudget (selectorExponent coefficient degree) (target + 1)
    runNPOracleProgram
        (selectorProgram coefficient degree (polynomialSourceOnset degree))
        budget budget
        (initialNPOracleState target (encodeUnary target)) =
      some selection.code := by
  let sourceOnset := polynomialSourceOnset degree
  let core :=
    polynomialCore coefficient degree (polynomialSourceOnset degree)
  let factor := sourceOnset + 1
  let selection := emittedSelection 0 sourceOnset 0 core
  let limit := selectorLimit coefficient degree target
  let budget :=
    exponentialBudget (selectorExponent coefficient degree) (target + 1)
  have hcoefficientLimit : coefficient ≤ limit :=
    (coefficient_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have hdegreeLimit : degree ≤ limit :=
    (degree_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have htargetLimit : target ≤ limit :=
    target_le_selectorLimit coefficient degree target
  have hfactorLimit : factor ≤ limit := by
    exact (sourceOnset_succ_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have hcoreLimit : core ≤ limit := by
    exact (initialCore_le_selectorScale coefficient degree).trans
      (selectorScale_le_limit coefficient degree target)
  have hnat :
      ∀ value ≤ limit, natBitLength value ≤ budget := by
    intro value hvalue
    simpa [limit, budget] using
      natBits_le_selectorBudget coefficient degree target value hvalue
  have hunary :
      ∀ value ≤ limit,
        natBitLength (encodeUnary value) ≤ budget := by
    intro value hvalue
    simpa [limit, budget] using
      unaryBits_le_selectorBudget coefficient degree target value hvalue
  have hsourceLimit : sourceOnset ≤ limit := by
    exact (Nat.le_succ sourceOnset).trans hfactorLimit
  have hselectionBits :=
    selectionBits_le_selectorBudget coefficient degree target selection
      (by simp [selection, emittedSelection])
      (by simpa [selection, emittedSelection, limit] using hsourceLimit)
      (by simp [selection, emittedSelection])
      (by simpa [selection, emittedSelection, limit] using hcoreLimit)
  let entry := selectorEntryState sourceOnset target
  let done :=
    candidateDoneState factor coefficient degree target entry
  have hdonePc : done.pc = emitPc := by
    have hcross :
        target < 2 * (coefficient * factor ^ degree) := by
      simpa [core, factor, sourceOnset, polynomialCore] using htarget
    simp [done, hcross]
  have hdonePreviousSource :
      done.registers previousSourceRegister = 0 := by
    rw [candidateDoneState_preserves factor coefficient degree target entry
      previousSourceRegister (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [entry, selectorEntryState, initialNPOracleState]
  have hdoneSource :
      done.registers sourceRegister = sourceOnset := by
    rw [candidateDoneState_preserves factor coefficient degree target entry
      sourceRegister (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [entry, selectorEntryState]
  have hdonePreviousCore :
      done.registers previousCoreRegister = 0 := by
    rw [candidateDoneState_preserves factor coefficient degree target entry
      previousCoreRegister (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [entry, selectorEntryState, initialNPOracleState]
  have hdoneCore : done.registers resultRegister = core := by
    simpa [core, factor, sourceOnset, polynomialCore] using
      candidateDoneState_result factor coefficient degree target entry
  let exactFuel :=
    3 + candidateFuel factor coefficient degree target + 4
  have hexact :
      runNPOracleProgram
          (selectorProgram coefficient degree sourceOnset)
          budget exactFuel
          (initialNPOracleState target (encodeUnary target)) =
        some selection.code := by
    rw [show exactFuel =
      3 + (candidateFuel factor coefficient degree target + 4) by
        simp [exactFuel]
        omega]
    rw [run_selector_setup coefficient degree sourceOnset target budget
      (candidateFuel factor coefficient degree target + 4)]
    · rw [run_candidate coefficient degree sourceOnset budget 4 factor
        target limit entry]
      · rw [run_emit coefficient degree sourceOnset budget 0
          0 sourceOnset 0 core done hdonePc hdonePreviousSource
          hdoneSource hdonePreviousCore hdoneCore]
        · simpa [selection, emittedSelection, budget] using hselectionBits.1
        · simpa [selection, emittedSelection, budget] using
            hselectionBits.2.1
        · simpa [selection, emittedSelection, budget] using
            hselectionBits.2.2
      · rfl
      · simp [entry, selectorEntryState, initialNPOracleState]
      · simp [entry, selectorEntryState, factor]
      · simp [entry, selectorEntryState, initialNPOracleState]
      · simp [entry, selectorEntryState]
      · simp [entry, selectorEntryState, initialNPOracleState]
      · exact hcoefficient
      · simp [factor]
      · exact hcoefficientLimit
      · exact hdegreeLimit
      · exact hfactorLimit
      · exact htargetLimit
      · simpa [core, factor, sourceOnset, polynomialCore] using hcoreLimit
      · exact hnat
      · exact hunary
    · exact hnat 1 <|
        (Nat.one_le_of_lt
          (selectorScale_positive coefficient degree)).trans
            (selectorScale_le_limit coefficient degree target)
    · exact hnat sourceOnset hsourceLimit
    · exact hunary factor hfactorLimit
  have hcandidateFuel :
      candidateFuel factor coefficient degree target ≤
        40 * (limit + 1) ^ 3 := by
    apply candidateFuel_le (core := core)
    · simp [factor]
    · exact hcoefficient
    · exact hfactorLimit
    · exact hcoefficientLimit
    · exact hdegreeLimit
    · exact htargetLimit
    · rfl
    · exact hcoreLimit
  have hfuelPolynomial :
      exactFuel ≤ 48 * (limit + 1) ^ 4 := by
    have hcubic : 1 ≤ (limit + 1) ^ 3 :=
      one_le_pow₀ (by omega)
    have hcubicFourth :
        (limit + 1) ^ 3 ≤ (limit + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    dsimp [exactFuel]
    nlinarith
  have hfuel : exactFuel ≤ budget := by
    exact hfuelPolynomial.trans <| by
      simpa [limit, budget] using
        fortyEightFourth_le_selectorBudget coefficient degree target
  have hmore :=
    runNPOracleProgram_add_fuel_of_some
      (extra := budget - exactFuel) hexact
  simpa [Nat.add_sub_of_le hfuel] using hmore

/-- The public selector runner contains only the fixed 40-instruction program.
Both the high-target correctness branch and the below-onset totality branch
are theorems about that same interpreter execution. -/
def selectorRunner
    (coefficient degree : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree) :
    ExponentialNatProgram ℕ id encodeUnary (fun target => target + 1) where
  program :=
    selectorProgram coefficient degree (polynomialSourceOnset degree)
  exponent := selectorExponent coefficient degree
  exponentPositive := selectorExponent_positive coefficient degree
  initialBitsFit := by
    intro target
    simp only [id_eq]
    have htarget :=
      target_le_selectorLimit coefficient degree target
    rcases le_total target (encodeUnary target) with hle | hle
    · rw [max_eq_right hle]
      exact unaryBits_le_selectorBudget
        coefficient degree target target htarget
    · rw [max_eq_left hle]
      exact natBits_le_selectorBudget
        coefficient degree target target htarget
  halts := by
    intro target
    by_cases htarget :
        2 * polynomialCore coefficient degree
          (polynomialSourceOnset degree) ≤ target
    · let data :=
        polynomialFirstCrossingData coefficient degree target
          hcoefficient hdegree htarget
      exact ⟨(firstCrossingSelection data).code,
        run_selector_at_firstCrossing coefficient degree target
          hcoefficient hdegree htarget⟩
    · have hbelow :
          target <
            2 * polynomialCore coefficient degree
              (polynomialSourceOnset degree) := by
        omega
      let selection :=
        emittedSelection 0 (polynomialSourceOnset degree) 0
          (polynomialCore coefficient degree
            (polynomialSourceOnset degree))
      exact ⟨selection.code,
        run_selector_belowOnset coefficient degree target
          hcoefficient hdegree hbelow⟩

@[simp] theorem selectorRunner_oracleFree
    (coefficient degree : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree) :
    OracleFree
      (selectorRunner coefficient degree hcoefficient hdegree).program := by
  exact selectorProgram_oracleFree coefficient degree
    (polynomialSourceOnset degree)

/-- Explicit total-domain regression theorem: even the zero target executes
the real program and emits the below-onset tuple within the published budget.
-/
theorem selectorRunner_runs_at_zero
    (coefficient degree : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree) :
    let selection :=
      emittedSelection 0 (polynomialSourceOnset degree) 0
        (polynomialCore coefficient degree
          (polynomialSourceOnset degree))
    runNPOracleProgram
        (selectorRunner coefficient degree hcoefficient hdegree).program
        ((selectorRunner coefficient degree hcoefficient hdegree).budget 0)
        ((selectorRunner coefficient degree hcoefficient hdegree).budget 0)
        (initialNPOracleState 0 (encodeUnary 0)) =
      some selection.code := by
  have hcorePositive :
      0 <
        polynomialCore coefficient degree
          (polynomialSourceOnset degree) := by
    unfold polynomialCore
    positivity
  simpa [selectorRunner, ExponentialNatProgram.budget] using
    run_selector_belowOnset coefficient degree 0
      hcoefficient hdegree (by omega)

theorem selectorRunner_execute_eq
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    let data :=
      polynomialFirstCrossingData coefficient degree target
        hcoefficient hdegree htarget
    (selectorRunner coefficient degree hcoefficient hdegree).execute target =
      (firstCrossingSelection data).code := by
  have hrun :=
    run_selector_at_firstCrossing coefficient degree target
      hcoefficient hdegree htarget
  simp [ExponentialNatProgram.execute, ExponentialNatProgram.toBounded,
    ExponentialNatProgram.budget, BoundedNatProgram.execute,
    selectorRunner, hrun]

/-- Canonical executable schedule for every derived smooth envelope.  Callers
provide no selector, decoded tuple, schedule witness, or local correctness
argument. -/
def executableEnvelopeSchedule
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) :
    ExecutableEnvelopeSchedule envelope where
  selector :=
    selectorRunner envelope.coefficient envelope.degree
      envelope.coefficientPositive envelope.degreePositive
  output_eq := by
    intro target htarget
    change
      2 * polynomialCore envelope.coefficient envelope.degree
        (polynomialSourceOnset envelope.degree) ≤ target at htarget
    rw [selectorRunner_execute_eq envelope.coefficient envelope.degree target
      envelope.coefficientPositive envelope.degreePositive htarget]
    rw [ExecutableScheduleSelection.decode_code]
    rfl

end NearCubicWires.UnaryPolynomialSelector
