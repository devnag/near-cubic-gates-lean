import Proof.MachineModel.ProjectionRunnerCallProgram

/-!
# Canonical projection-runner atom construction

The public range generator enumerates one flat coordinate.  This fixed,
oracle-free callee turns that coordinate and the public projection shape into
the exact query/decision atom consumed by `projectionRunnerCallProgram`.
Neither a host-generated call list nor a semantic callback crosses this ABI.
-/

namespace NearCubicWires.ProjectionRunnerAtomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ProjectionRunnerCallProgram

/-- Context shared by every generated coordinate:
`pair(input bits, pair(randomness width, query count))`. -/
def projectionRunnerAtomContext
    {n : ℕ} (input : BitInput n) (width count : ℕ) : ℕ :=
  Nat.pair (encodeBitInput input) (Nat.pair width count)

/-- Request body accepted by the fixed atom constructor.  The input arity
continues to live in interpreter register one. -/
def projectionRunnerAtomRequest
    {n : ℕ} (input : BitInput n) (width count index : ℕ) : ℕ :=
  Nat.pair index (projectionRunnerAtomContext input width count)

def projectionQueryAtomCode
    (inputArity inputCode width count query bit : ℕ) : ℕ :=
  let requestCode :=
    Nat.pair inputArity <|
      Nat.pair inputCode (Nat.pair query bit)
  let context :=
    Nat.pair width <| Nat.pair count (Nat.pair query bit)
  Nat.pair inputArity <| Nat.pair 0 (Nat.pair requestCode context)

def projectionDecisionAtomCode
    (inputArity inputCode width count randomnessCode : ℕ) : ℕ :=
  let requestCode :=
    Nat.pair inputArity <| Nat.pair inputCode randomnessCode
  let context := Nat.pair width count
  Nat.pair inputArity <| Nat.pair 1 (Nat.pair requestCode context)

/-- Structural specification matching the controller loop.  At every
recursive step one complete query row has been skipped. -/
def projectionRunnerAtomCursorOutput
    (inputArity inputCode width originalCount : ℕ) :
    (remaining rowsLeft query : ℕ) → ℕ
  | remaining, 0, _query =>
      projectionDecisionAtomCode inputArity inputCode width originalCount
        remaining
  | remaining, rowsLeft + 1, query =>
      if width = 0 then
        projectionDecisionAtomCode inputArity inputCode width originalCount
          remaining
      else if remaining < width then
        projectionQueryAtomCode inputArity inputCode width originalCount
          query remaining
      else
        projectionRunnerAtomCursorOutput inputArity inputCode width
          originalCount (remaining - width) rowsLeft (query + 1)

def projectionRunnerAtomOutput
    (inputArity inputCode width count index : ℕ) : ℕ :=
  projectionRunnerAtomCursorOutput inputArity inputCode width count
    index count 0

/-- A flat query coordinate is decoded row-major.  The proof follows the same
subtraction loop as the executable controller, so later schedule refinement
does not rely on an unverified division primitive. -/
theorem projectionRunnerAtomCursorOutput_query
    (inputArity inputCode width originalCount : ℕ)
    (remainingRows query offset bit : ℕ)
    (hwidth : 0 < width) (hoffset : offset < remainingRows)
    (hbit : bit < width) :
    projectionRunnerAtomCursorOutput inputArity inputCode width
        originalCount (offset * width + bit) remainingRows query =
      projectionQueryAtomCode inputArity inputCode width originalCount
        (query + offset) bit := by
  induction offset generalizing remainingRows query with
  | zero =>
      cases remainingRows with
      | zero => omega
      | succ remainingRows =>
          simp [projectionRunnerAtomCursorOutput, hwidth.ne', hbit]
  | succ offset inductionHypothesis =>
      cases remainingRows with
      | zero => omega
      | succ remainingRows =>
          have hoffsetNext : offset < remainingRows := by
            omega
          have hnotShort :
              ¬((offset + 1) * width + bit < width) := by
            rw [Nat.add_mul]
            omega
          rw [projectionRunnerAtomCursorOutput, if_neg hwidth.ne',
            if_neg hnotShort]
          rw [show (offset + 1) * width + bit - width =
            offset * width + bit by
              rw [Nat.add_mul]
              omega]
          rw [inductionHypothesis remainingRows (query + 1)
            hoffsetNext]
          congr 1
          omega

/-- Once every query row has been skipped, the remaining flat coordinate is
the decision randomness code.  Width zero is handled explicitly and reaches
the same canonical decision branch without division-by-zero conventions. -/
theorem projectionRunnerAtomCursorOutput_decision
    (inputArity inputCode width originalCount rows query randomnessCode : ℕ) :
    projectionRunnerAtomCursorOutput inputArity inputCode width
        originalCount (rows * width + randomnessCode) rows query =
      projectionDecisionAtomCode inputArity inputCode width originalCount
        randomnessCode := by
  induction rows generalizing query with
  | zero =>
      simp [projectionRunnerAtomCursorOutput]
  | succ rows inductionHypothesis =>
      by_cases hwidthZero : width = 0
      · simp [projectionRunnerAtomCursorOutput, hwidthZero]
      · have hnotShort :
            ¬((rows + 1) * width + randomnessCode < width) := by
          rw [Nat.add_mul]
          omega
        rw [projectionRunnerAtomCursorOutput, if_neg hwidthZero,
          if_neg hnotShort]
        rw [show (rows + 1) * width + randomnessCode - width =
          rows * width + randomnessCode by
            rw [Nat.add_mul]
            omega]
        exact inductionHypothesis (query + 1)

/-- Closed query-coordinate view of the public atom constructor. -/
theorem projectionRunnerAtomOutput_query
    (inputArity inputCode width count query bit : ℕ)
    (hwidth : 0 < width) (hquery : query < count) (hbit : bit < width) :
    projectionRunnerAtomOutput inputArity inputCode width count
        (query * width + bit) =
      projectionQueryAtomCode inputArity inputCode width count query bit := by
  simpa only [projectionRunnerAtomOutput, Nat.zero_add] using
    projectionRunnerAtomCursorOutput_query inputArity inputCode width count
      count 0 query bit hwidth hquery hbit

/-- Closed decision-coordinate view of the public atom constructor. -/
theorem projectionRunnerAtomOutput_decision
    (inputArity inputCode width count randomnessCode : ℕ) :
    projectionRunnerAtomOutput inputArity inputCode width count
        (count * width + randomnessCode) =
      projectionDecisionAtomCode inputArity inputCode width count
        randomnessCode := by
  exact projectionRunnerAtomCursorOutput_decision inputArity inputCode width
    count count 0 randomnessCode

/-- The raw query atom is exactly the fixed heterogeneous callee ABI. -/
@[simp] theorem projectionQueryAtomCode_eq_callAtom
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    projectionQueryAtomCode n (encodeBitInput input) (pcp.nativeWidth n)
        (pcp.queryCount n) query.val bit.val =
      (ProjectionRunnerCall.query
        (pcp.queryRequest input query bit)).atom := by
  rfl

/-- The raw decision atom is exactly the fixed heterogeneous callee ABI. -/
@[simp] theorem projectionDecisionAtomCode_eq_callAtom
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    projectionDecisionAtomCode n (encodeBitInput input) (pcp.nativeWidth n)
        (pcp.queryCount n) (encodeBitInput randomness) =
      (ProjectionRunnerCall.decision
        (pcp.decisionRequest input randomness)).atom := by
  rfl

/-- Exact controller fuel from the row-dispatch loop at `pc = 8`. -/
def projectionRunnerAtomCursorFuel :
    (width remaining rowsLeft : ℕ) → ℕ
  | _width, _remaining, 0 => 9
  | width, remaining, rowsLeft + 1 =>
      if width = 0 then
        10
      else if remaining < width then
        17 + 4 * remaining
      else
        8 + 4 * width +
          projectionRunnerAtomCursorFuel width
            (remaining - width) rowsLeft

def projectionRunnerAtomFuel
    (width count index : ℕ) : ℕ :=
  8 + projectionRunnerAtomCursorFuel width index count

/-- Register ABI:

* `r1`: input arity;
* `r2`: flat schedule index;
* `r4`: encoded public input;
* `r6`/`r14`: randomness width and original query count;
* `r7`/`r8`/`r9`: rows left, remaining index, and query coordinate.

The loop subtracts one full width at a time.  Falling short identifies a query
bit; exhausting the public row count identifies a decision randomness code.
-/
def projectionRunnerAtomProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .copy 7 14 7
  , .copy 2 8 8
  , .branchZero 7 19 9
  , .branchZero 6 19 10
  , .copy 6 10 11
  , .copy 8 11 12
  , .branchZero 10 16 13
  , .branchZero 11 27 14
  , .decrement 10 15
  , .decrement 11 12
  , .copy 11 8 17
  , .decrement 7 18
  , .increment 9 8
    -- Decision request.
  , .pair 4 8 12 20
  , .pair 1 12 12 21
  , .pair 6 14 13 22
  , .pair 12 13 12 23
  , .set 15 1 24
  , .pair 15 12 12 25
  , .pair 1 12 0 26
  , .halt 0
    -- Query request.
  , .pair 9 8 12 28
  , .pair 4 12 12 29
  , .pair 1 12 12 30
  , .pair 9 8 13 31
  , .pair 14 13 13 32
  , .pair 6 13 13 33
  , .pair 12 13 12 34
  , .set 15 0 35
  , .pair 15 12 12 36
  , .pair 1 12 0 37
  , .halt 0
  ]

@[simp] theorem projectionRunnerAtomProgram_length :
    projectionRunnerAtomProgram.length = 38 := by
  rfl

theorem projectionRunnerAtomProgram_oracleFree :
    OracleFree projectionRunnerAtomProgram := by
  rfl

/-- A single honest width envelope: the packed request and exact output bound
all loop cursors and every intermediate pair. -/
def projectionRunnerAtomMaximumBits
    (inputArity inputCode width count index : ℕ) : ℕ :=
  natBitLength <|
    max (Nat.pair index (Nat.pair inputCode (Nat.pair width count)))
      (projectionRunnerAtomOutput inputArity inputCode width count index)

private theorem npOracleState_ext
    (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Successful width subtraction reaches the completed-row branch. -/
private theorem run_widthSubtractionSuccess
    (width remaining maximumBits extra : ℕ) (state : NPOracleState)
    (hwidth : width ≤ remaining)
    (hpc : state.pc = 12)
    (hwidthRegister : state.registers 10 = width)
    (hremainingRegister : state.registers 11 = remaining)
    (hwidthBits : natBitLength width ≤ maximumBits)
    (hremainingBits : natBitLength remaining ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (extra + (4 * width + 1)) state =
      runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
        (((state.write 10 0).write 11 (remaining - width)).jump 16) := by
  induction width generalizing remaining state with
  | zero =>
      rw [show extra + (4 * 0 + 1) = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwidthRegister, if_pos rfl]
      congr 2
      apply npOracleState_ext
      · rfl
      · funext register
        simp only [NPOracleState.write]
        by_cases hten : register = 10
        · subst register
          simp [hwidthRegister]
        · by_cases heleven : register = 11
          · subst register
            simp [hremainingRegister]
          · simp [hten, heleven]
  | succ width inductionHypothesis =>
      have hremainingPositive : 0 < remaining := by
        omega
      let state1 := state.jump 13
      let state2 := state1.jump 14
      let state3 := (state2.write 10 width).jump 15
      let state4 := (state3.write 11 remaining.pred).jump 12
      have hnext : width ≤ remaining.pred := by
        rw [Nat.pred_eq_sub_one]
        omega
      have hwidthPredBits :
          natBitLength width ≤ maximumBits :=
        (decrement_bits_le (width + 1)).trans (by
          simpa only [Nat.succ_eq_add_one] using hwidthBits)
      have hremainingPredBits :
          natBitLength remaining.pred ≤ maximumBits :=
        (decrement_bits_le remaining).trans hremainingBits
      rw [show extra + (4 * (width + 1) + 1) =
        (extra + (4 * width + 1) + 3) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwidthRegister, if_neg (by omega)]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * width + 1) + 3) state1 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10 0).write 11
              (remaining - (width + 1))).jump 16)
      rw [show extra + (4 * width + 1) + 3 =
        (extra + (4 * width + 1) + 2) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state1.registers 11 = remaining by
        simp [state1, hremainingRegister], if_neg (by omega)]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * width + 1) + 2) state2 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10 0).write 11
              (remaining - (width + 1))).jump 16)
      rw [show extra + (4 * width + 1) + 2 =
        (extra + (4 * width + 1) + 1) + 1 by omega]
      rw [run_decrement_instruction (value := width) (by rfl) rfl
        (by simp [state2, state1, hwidthRegister]) hwidthPredBits]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * width + 1) + 1) state3 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10 0).write 11
              (remaining - (width + 1))).jump 16)
      rw [show extra + (4 * width + 1) + 1 =
        (extra + (4 * width + 1)) + 1 by omega]
      rw [run_decrement_instruction
        (value := remaining.pred) (by rfl) rfl
        (by simp [state3, state2, state1, hremainingRegister])
        hremainingPredBits]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * width + 1)) state4 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10 0).write 11
              (remaining - (width + 1))).jump 16)
      rw [inductionHypothesis remaining.pred state4 hnext rfl
        (by simp [state4, state3, state2, state1])
        (by simp [state4, state3, state2, state1])
        hwidthPredBits hremainingPredBits]
      have hsub' :
          remaining - 1 - width = remaining - (width + 1) := by
        omega
      have hstateEq :
          (((state4.write 10 0).write 11
              (remaining.pred - width)).jump 16) =
            (((state.write 10 0).write 11
              (remaining - (width + 1))).jump 16) := by
        apply npOracleState_ext
        · simp [state4]
        · funext register
          simp only [NPOracleState.write]
          by_cases hten : register = 10
          · subst register
            simp
          · by_cases heleven : register = 11
            · subst register
              simp [hsub']
            · simp [state4, state3, state2, state1, hten, heleven]
      rw [hstateEq]

/-- A short row leaves its remainder intact in `r8` and reaches the query
constructor. -/
private theorem run_widthSubtractionShort
    (width remaining maximumBits extra : ℕ) (state : NPOracleState)
    (hshort : remaining < width)
    (hpc : state.pc = 12)
    (hwidthRegister : state.registers 10 = width)
    (hremainingRegister : state.registers 11 = remaining)
    (hwidthBits : natBitLength width ≤ maximumBits)
    (hremainingBits : natBitLength remaining ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (extra + (4 * remaining + 2)) state =
      runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
        (((state.write 10 (width - remaining)).write 11 0).jump 27) := by
  induction remaining generalizing width state with
  | zero =>
      have hwidthNonzero : width ≠ 0 := by omega
      rw [show extra + (4 * 0 + 2) = (extra + 1) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwidthRegister, if_neg hwidthNonzero]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show (state.jump 13).registers 11 = 0 by
        simpa [NPOracleState.jump] using hremainingRegister, if_pos rfl]
      have hstateEq :
          state.jump 27 =
            (((state.write 10 (width - 0)).write 11 0).jump 27) := by
        apply npOracleState_ext
        · rfl
        · funext register
          simp only [NPOracleState.write]
          by_cases hten : register = 10
          · subst register
            simp [hwidthRegister]
          · by_cases heleven : register = 11
            · subst register
              simp [hremainingRegister]
            · simp [hten, heleven]
      simpa only [NPOracleState.jump] using
        congrArg
          (runNPOracleProgram projectionRunnerAtomProgram maximumBits extra)
          hstateEq
  | succ remaining inductionHypothesis =>
      have hwidthPositive : 0 < width := by omega
      have hnext : remaining < width.pred := by
        rw [Nat.pred_eq_sub_one]
        omega
      let state1 := state.jump 13
      let state2 := state1.jump 14
      let state3 := (state2.write 10 width.pred).jump 15
      let state4 := (state3.write 11 remaining).jump 12
      have hwidthPredBits :
          natBitLength width.pred ≤ maximumBits :=
        (decrement_bits_le width).trans hwidthBits
      have hremainingPredBits :
          natBitLength remaining ≤ maximumBits :=
        (decrement_bits_le (remaining + 1)).trans (by
          simpa only [Nat.succ_eq_add_one] using hremainingBits)
      rw [show extra + (4 * (remaining + 1) + 2) =
        (extra + (4 * remaining + 2) + 3) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwidthRegister, if_neg (by omega)]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * remaining + 2) + 3) state1 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10
              (width - (remaining + 1))).write 11 0).jump 27)
      rw [show extra + (4 * remaining + 2) + 3 =
        (extra + (4 * remaining + 2) + 2) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state1.registers 11 = remaining + 1 by
        simp [state1, hremainingRegister], if_neg (by omega)]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * remaining + 2) + 2) state2 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10
              (width - (remaining + 1))).write 11 0).jump 27)
      rw [show extra + (4 * remaining + 2) + 2 =
        (extra + (4 * remaining + 2) + 1) + 1 by omega]
      rw [run_decrement_instruction (value := width.pred) (by rfl) rfl
        (by simp [state2, state1, hwidthRegister]) hwidthPredBits]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * remaining + 2) + 1) state3 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10
              (width - (remaining + 1))).write 11 0).jump 27)
      rw [show extra + (4 * remaining + 2) + 1 =
        (extra + (4 * remaining + 2)) + 1 by omega]
      rw [run_decrement_instruction (value := remaining) (by rfl) rfl
        (by simp [state3, state2, state1, hremainingRegister])
        hremainingPredBits]
      change
        runNPOracleProgram projectionRunnerAtomProgram maximumBits
            (extra + (4 * remaining + 2)) state4 =
          runNPOracleProgram projectionRunnerAtomProgram maximumBits extra
            (((state.write 10
              (width - (remaining + 1))).write 11 0).jump 27)
      rw [inductionHypothesis width.pred state4 hnext rfl
        (by simp [state4, state3, state2, state1])
        (by simp [state4, state3, state2, state1])
        hwidthPredBits hremainingPredBits]
      have hsub' :
          width - 1 - remaining = width - (remaining + 1) := by
        omega
      have hstateEq :
          (((state4.write 10
              (width.pred - remaining)).write 11 0).jump 27) =
            (((state.write 10
              (width - (remaining + 1))).write 11 0).jump 27) := by
        apply npOracleState_ext
        · simp [state4]
        · funext register
          simp only [NPOracleState.write]
          by_cases hten : register = 10
          · subst register
            simp [hsub']
          · by_cases heleven : register = 11
            · subst register
              simp
            · simp [state4, state3, state2, state1, hten, heleven]
      rw [hstateEq]

private theorem run_decisionBuilder
    (inputArity inputCode width count randomnessCode maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 19)
    (hinputArity : state.registers 1 = inputArity)
    (hinputCode : state.registers 4 = inputCode)
    (hwidth : state.registers 6 = width)
    (hcount : state.registers 14 = count)
    (hrandomness : state.registers 8 = randomnessCode)
    (houtputBits :
      natBitLength
          (projectionDecisionAtomCode inputArity inputCode width count
            randomnessCode) ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 8 state =
      some
        (projectionDecisionAtomCode inputArity inputCode width count
          randomnessCode) := by
  let requestPayload := Nat.pair inputCode randomnessCode
  let request := Nat.pair inputArity requestPayload
  let context := Nat.pair width count
  let payload := Nat.pair request context
  let tagged := Nat.pair 1 payload
  let output := Nat.pair inputArity tagged
  have fits :
      ∀ candidate ≤ output, natBitLength candidate ≤ maximumBits := by
    intro candidate hcandidate
    exact
      (PolynomialClock.natBitLength_mono hcandidate).trans
        (by simpa only [output, projectionDecisionAtomCode] using houtputBits)
  have htaggedLe : tagged ≤ output :=
    Nat.right_le_pair inputArity tagged
  have hpayloadLe : payload ≤ output :=
    (Nat.right_le_pair 1 payload).trans htaggedLe
  have hrequestLe : request ≤ output :=
    (Nat.left_le_pair request context).trans hpayloadLe
  have hcontextLe : context ≤ output :=
    (Nat.right_le_pair request context).trans hpayloadLe
  have hrequestPayloadLe : requestPayload ≤ output :=
    (Nat.right_le_pair inputArity requestPayload).trans hrequestLe
  let state1 := (state.write 12 requestPayload).jump 20
  let state2 := (state1.write 12 request).jump 21
  let state3 := (state2.write 13 context).jump 22
  let state4 := (state3.write 12 payload).jump 23
  let state5 := (state4.write 15 1).jump 24
  let state6 := (state5.write 12 tagged).jump 25
  let state7 := (state6.write 0 output).jump 26
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction (value := requestPayload) (by rfl) hpc
    (by simp [requestPayload, hinputCode, hrandomness])
    (fits requestPayload hrequestPayloadLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 7 state1 =
      some output
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := request) (by rfl) rfl
    (by simp [state1, request, hinputArity])
    (fits request hrequestLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 6 state2 =
      some output
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := context) (by rfl) rfl
    (by simp [state2, state1, context, hwidth, hcount])
    (fits context hcontextLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 5 state3 =
      some output
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := payload) (by rfl) rfl
    (by rfl) (fits payload hpayloadLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 4 state4 =
      some output
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl
    (fits 1 ((Nat.left_le_pair 1 payload).trans htaggedLe))]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 3 state5 =
      some output
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := tagged) (by rfl) rfl
    (by rfl) (fits tagged htaggedLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 2 state6 =
      some output
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output) (by rfl) rfl
    (by simp [state6, state5, state4, state3, state2, state1,
      output, hinputArity]) (fits output (le_refl output))]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 1 state7 =
      some output
  exact run_halt_instruction (value := output) (by rfl) rfl
    (by rfl) (fits output (le_refl output))

private theorem run_queryBuilder
    (inputArity inputCode width count query bit maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 27)
    (hinputArity : state.registers 1 = inputArity)
    (hinputCode : state.registers 4 = inputCode)
    (hwidth : state.registers 6 = width)
    (hcount : state.registers 14 = count)
    (hquery : state.registers 9 = query)
    (hbit : state.registers 8 = bit)
    (houtputBits :
      natBitLength
          (projectionQueryAtomCode inputArity inputCode width count query bit) ≤
        maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 11 state =
      some
        (projectionQueryAtomCode inputArity inputCode width count query bit) := by
  let coordinate := Nat.pair query bit
  let requestPayload := Nat.pair inputCode coordinate
  let request := Nat.pair inputArity requestPayload
  let countContext := Nat.pair count coordinate
  let context := Nat.pair width countContext
  let payload := Nat.pair request context
  let tagged := Nat.pair 0 payload
  let output := Nat.pair inputArity tagged
  have fits :
      ∀ candidate ≤ output, natBitLength candidate ≤ maximumBits := by
    intro candidate hcandidate
    exact
      (PolynomialClock.natBitLength_mono hcandidate).trans
        (by simpa only [output, projectionQueryAtomCode] using houtputBits)
  have htaggedLe : tagged ≤ output :=
    Nat.right_le_pair inputArity tagged
  have hpayloadLe : payload ≤ output :=
    (Nat.right_le_pair 0 payload).trans htaggedLe
  have hrequestLe : request ≤ output :=
    (Nat.left_le_pair request context).trans hpayloadLe
  have hcontextLe : context ≤ output :=
    (Nat.right_le_pair request context).trans hpayloadLe
  have hrequestPayloadLe : requestPayload ≤ output :=
    (Nat.right_le_pair inputArity requestPayload).trans hrequestLe
  have hcoordinateRequestLe : coordinate ≤ output :=
    (Nat.right_le_pair inputCode coordinate).trans hrequestPayloadLe
  have hcountContextLe : countContext ≤ output :=
    (Nat.right_le_pair width countContext).trans hcontextLe
  have hcoordinateContextLe : coordinate ≤ output :=
    (Nat.right_le_pair count coordinate).trans hcountContextLe
  let state1 := (state.write 12 coordinate).jump 28
  let state2 := (state1.write 12 requestPayload).jump 29
  let state3 := (state2.write 12 request).jump 30
  let state4 := (state3.write 13 coordinate).jump 31
  let state5 := (state4.write 13 countContext).jump 32
  let state6 := (state5.write 13 context).jump 33
  let state7 := (state6.write 12 payload).jump 34
  let state8 := (state7.write 15 0).jump 35
  let state9 := (state8.write 12 tagged).jump 36
  let state10 := (state9.write 0 output).jump 37
  rw [show 11 = 10 + 1 by omega]
  rw [run_pair_instruction (value := coordinate) (by rfl) hpc
    (by simp [coordinate, hquery, hbit])
    (fits coordinate hcoordinateRequestLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 10 state1 =
      some output
  rw [show 10 = 9 + 1 by omega]
  rw [run_pair_instruction (value := requestPayload) (by rfl) rfl
    (by simp [state1, requestPayload, hinputCode])
    (fits requestPayload hrequestPayloadLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 9 state2 =
      some output
  rw [show 9 = 8 + 1 by omega]
  rw [run_pair_instruction (value := request) (by rfl) rfl
    (by simp [state2, state1, request, hinputArity])
    (fits request hrequestLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 8 state3 =
      some output
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction (value := coordinate) (by rfl) rfl
    (by simp [state3, state2, state1, coordinate, hquery, hbit])
    (fits coordinate hcoordinateContextLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 7 state4 =
      some output
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := countContext) (by rfl) rfl
    (by simp [state4, state3, state2, state1, countContext, hcount])
    (fits countContext hcountContextLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 6 state5 =
      some output
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := context) (by rfl) rfl
    (by simp [state5, state4, state3, state2, state1, context, hwidth])
    (fits context hcontextLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 5 state6 =
      some output
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := payload) (by rfl) rfl
    (by rfl) (fits payload hpayloadLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 4 state7 =
      some output
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl
    (fits 0 (Nat.zero_le output))]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 3 state8 =
      some output
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := tagged) (by rfl) rfl
    (by rfl) (fits tagged htaggedLe)]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 2 state9 =
      some output
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output) (by rfl) rfl
    (by simp [state9, state8, state7, state6, state5, state4, state3,
      state2, state1, output, hinputArity])
    (fits output (le_refl output))]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits 1 state10 =
      some output
  exact run_halt_instruction (value := output) (by rfl) rfl
    (by rfl) (fits output (le_refl output))

/-- Exact row controller.  The invariant `query + rowsLeft = originalCount`
is what makes the flat schedule split canonical rather than heuristic. -/
private theorem run_projectionRunnerAtomCursor
    (inputArity inputCode width originalCount remaining rowsLeft query
      maximumBits : ℕ)
    (state : NPOracleState)
    (hrows : query + rowsLeft = originalCount)
    (hpc : state.pc = 8)
    (hinputArity : state.registers 1 = inputArity)
    (hinputCode : state.registers 4 = inputCode)
    (hwidth : state.registers 6 = width)
    (hrowsLeft : state.registers 7 = rowsLeft)
    (hremaining : state.registers 8 = remaining)
    (hquery : state.registers 9 = query)
    (horiginalCount : state.registers 14 = originalCount)
    (hwidthBits : natBitLength width ≤ maximumBits)
    (horiginalCountBits :
      natBitLength originalCount ≤ maximumBits)
    (hremainingBits :
      natBitLength remaining ≤ maximumBits)
    (houtputBits :
      natBitLength
          (projectionRunnerAtomCursorOutput inputArity inputCode width
            originalCount remaining rowsLeft query) ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (projectionRunnerAtomCursorFuel width remaining rowsLeft) state =
      some
        (projectionRunnerAtomCursorOutput inputArity inputCode width
          originalCount remaining rowsLeft query) := by
  induction rowsLeft generalizing remaining query state with
  | zero =>
      rw [projectionRunnerAtomCursorFuel,
        projectionRunnerAtomCursorOutput]
      rw [show 9 = 8 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hrowsLeft, if_pos rfl]
      apply run_decisionBuilder inputArity inputCode width originalCount
        remaining maximumBits (state.jump 19) rfl
      · simpa [NPOracleState.jump] using hinputArity
      · simpa [NPOracleState.jump] using hinputCode
      · simpa [NPOracleState.jump] using hwidth
      · simpa [NPOracleState.jump] using horiginalCount
      · simpa [NPOracleState.jump] using hremaining
      · exact houtputBits
  | succ rowsLeft inductionHypothesis =>
      have hrowsLeftNonzero : rowsLeft + 1 ≠ 0 := by omega
      have hqueryLe : query ≤ originalCount := by omega
      by_cases hwidthZero : width = 0
      · have houtputDecision :
            natBitLength
                (projectionDecisionAtomCode inputArity inputCode width
                  originalCount remaining) ≤ maximumBits := by
          simpa only [projectionRunnerAtomCursorOutput,
            if_pos hwidthZero] using houtputBits
        rw [projectionRunnerAtomCursorFuel,
          projectionRunnerAtomCursorOutput, if_pos hwidthZero]
        rw [show 10 = 9 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hrowsLeft, if_neg hrowsLeftNonzero]
        rw [show 9 = 8 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show (state.jump 9).registers 6 = 0 by
          simpa [NPOracleState.jump, hwidthZero] using hwidth, if_pos rfl]
        simp only [if_pos hwidthZero]
        apply run_decisionBuilder inputArity inputCode width originalCount
          remaining maximumBits ((state.jump (8 + 1)).jump 19) rfl
        · simpa [NPOracleState.jump] using hinputArity
        · simpa [NPOracleState.jump] using hinputCode
        · simpa [NPOracleState.jump] using hwidth
        · simpa [NPOracleState.jump] using horiginalCount
        · simpa [NPOracleState.jump] using hremaining
        · exact houtputDecision
      · by_cases hshort : remaining < width
        · have houtputQuery :
              natBitLength
                  (projectionQueryAtomCode inputArity inputCode width
                    originalCount query remaining) ≤ maximumBits := by
            simpa only [projectionRunnerAtomCursorOutput,
              if_neg hwidthZero, if_pos hshort] using houtputBits
          rw [projectionRunnerAtomCursorFuel,
            projectionRunnerAtomCursorOutput, if_neg hwidthZero,
            if_pos hshort]
          let state1 := state.jump 9
          let state2 := state1.jump 10
          let state3 := (state2.write 10 width).jump 11
          let state4 := (state3.write 11 remaining).jump 12
          rw [show 17 + 4 * remaining =
            (16 + 4 * remaining) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) hpc]
          rw [hrowsLeft, if_neg hrowsLeftNonzero]
          simp only [if_neg hwidthZero, if_pos hshort]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (16 + 4 * remaining) state1 =
              some
                (projectionQueryAtomCode inputArity inputCode width
                  originalCount query remaining)
          rw [show 16 + 4 * remaining =
            (15 + 4 * remaining) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          rw [show state1.registers 6 = width by
            simp [state1, hwidth], if_neg hwidthZero]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (15 + 4 * remaining) state2 =
              some
                (projectionQueryAtomCode inputArity inputCode width
                  originalCount query remaining)
          rw [show 15 + 4 * remaining =
            (14 + 4 * remaining) + 1 by omega]
          rw [run_copy_instruction (value := width) (by rfl) rfl
            (by simp [state2, state1, hwidth]) hwidthBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (14 + 4 * remaining) state3 =
              some
                (projectionQueryAtomCode inputArity inputCode width
                  originalCount query remaining)
          rw [show 14 + 4 * remaining =
            (13 + 4 * remaining) + 1 by omega]
          rw [run_copy_instruction (value := remaining) (by rfl) rfl
            (by simp [state3, state2, state1, hremaining])
            hremainingBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (13 + 4 * remaining) state4 =
              some
                (projectionQueryAtomCode inputArity inputCode width
                  originalCount query remaining)
          rw [show 13 + 4 * remaining =
            11 + (4 * remaining + 2) by omega]
          rw [run_widthSubtractionShort width remaining maximumBits 11
            state4 hshort rfl (by rfl) (by rfl)
            hwidthBits hremainingBits]
          apply run_queryBuilder inputArity inputCode width originalCount
            query remaining maximumBits
              (((state4.write 10 (width - remaining)).write 11 0).jump 27)
            rfl
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using hinputArity
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using hinputCode
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using hwidth
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using horiginalCount
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using hquery
          · simpa [state4, state3, state2, state1,
              NPOracleState.write] using hremaining
          · exact houtputQuery
        · have hfull : width ≤ remaining :=
            Nat.le_of_not_gt hshort
          have houtputRecursive :
              natBitLength
                  (projectionRunnerAtomCursorOutput inputArity inputCode
                    width originalCount (remaining - width) rowsLeft
                    (query + 1)) ≤ maximumBits := by
            simpa only [projectionRunnerAtomCursorOutput,
              if_neg hwidthZero, if_neg hshort] using houtputBits
          let recursiveFuel :=
            projectionRunnerAtomCursorFuel width
              (remaining - width) rowsLeft
          let state1 := state.jump 9
          let state2 := state1.jump 10
          let state3 := (state2.write 10 width).jump 11
          let state4 := (state3.write 11 remaining).jump 12
          let state5 :=
            (((state4.write 10 0).write 11
              (remaining - width)).jump 16)
          let state6 :=
            (state5.write 8 (remaining - width)).jump 17
          let state7 := (state6.write 7 rowsLeft).jump 18
          let state8 := (state7.write 9 (query + 1)).jump 8
          have hremainingNextBits :
              natBitLength (remaining - width) ≤ maximumBits :=
            (PolynomialClock.natBitLength_mono
              (Nat.sub_le remaining width)).trans hremainingBits
          have hrowsNextBits :
              natBitLength rowsLeft ≤ maximumBits :=
            (PolynomialClock.natBitLength_mono (by omega)).trans
              horiginalCountBits
          have hqueryNextBits :
              natBitLength (query + 1) ≤ maximumBits :=
            (PolynomialClock.natBitLength_mono (by omega)).trans
              horiginalCountBits
          rw [projectionRunnerAtomCursorFuel,
            projectionRunnerAtomCursorOutput, if_neg hwidthZero,
            if_neg hshort]
          simp only [if_neg hwidthZero, if_neg hshort]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (8 + 4 * width + recursiveFuel) state =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 8 + 4 * width + recursiveFuel =
            (7 + 4 * width + recursiveFuel) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) hpc]
          rw [hrowsLeft, if_neg hrowsLeftNonzero]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (7 + 4 * width + recursiveFuel) state1 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 7 + 4 * width + recursiveFuel =
            (6 + 4 * width + recursiveFuel) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          rw [show state1.registers 6 = width by
            simp [state1, hwidth], if_neg hwidthZero]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (6 + 4 * width + recursiveFuel) state2 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 6 + 4 * width + recursiveFuel =
            (5 + 4 * width + recursiveFuel) + 1 by omega]
          rw [run_copy_instruction (value := width) (by rfl) rfl
            (by simp [state2, state1, hwidth]) hwidthBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (5 + 4 * width + recursiveFuel) state3 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 5 + 4 * width + recursiveFuel =
            (4 + 4 * width + recursiveFuel) + 1 by omega]
          rw [run_copy_instruction (value := remaining) (by rfl) rfl
            (by simp [state3, state2, state1, hremaining])
            hremainingBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (4 + 4 * width + recursiveFuel) state4 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 4 + 4 * width + recursiveFuel =
            (3 + recursiveFuel) + (4 * width + 1) by omega]
          rw [run_widthSubtractionSuccess width remaining maximumBits
            (3 + recursiveFuel) state4 hfull rfl (by rfl) (by rfl)
            hwidthBits hremainingBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (3 + recursiveFuel) state5 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 3 + recursiveFuel =
            (2 + recursiveFuel) + 1 by omega]
          rw [run_copy_instruction
            (value := remaining - width) (by rfl) rfl
            (by rfl) hremainingNextBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (2 + recursiveFuel) state6 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 2 + recursiveFuel =
            (1 + recursiveFuel) + 1 by omega]
          rw [run_decrement_instruction (value := rowsLeft) (by rfl) rfl
            (by simp [state6, state5, state4, state3, state2, state1,
              hrowsLeft]) hrowsNextBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                (1 + recursiveFuel) state7 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          rw [show 1 + recursiveFuel = recursiveFuel + 1 by omega]
          rw [run_increment_instruction (value := query + 1) (by rfl) rfl
            (by simp [state7, state6, state5, state4, state3, state2,
              state1, hquery]) hqueryNextBits]
          change
            runNPOracleProgram projectionRunnerAtomProgram maximumBits
                recursiveFuel state8 =
              some
                (projectionRunnerAtomCursorOutput inputArity inputCode
                  width originalCount (remaining - width) rowsLeft
                  (query + 1))
          exact inductionHypothesis (remaining - width) (query + 1)
            state8 (by omega) rfl
            (by simp [state8, state7, state6, state5, state4, state3,
              state2, state1, hinputArity])
            (by simp [state8, state7, state6, state5, state4, state3,
              state2, state1, hinputCode])
            (by simp [state8, state7, state6, state5, state4, state3,
              state2, state1, hwidth])
            (by rfl) (by rfl) (by rfl)
            (by simp [state8, state7, state6, state5, state4, state3,
              state2, state1, horiginalCount])
            hremainingNextBits houtputRecursive

/-- Exact execution under any width budget covering the public request and
the exact emitted atom.  This is the callee contract used by the balanced
range pipeline; no semantic call list is supplied to the interpreter. -/
theorem run_projectionRunnerAtomProgram_of_fits
    (inputArity inputCode width count index maximumBits : ℕ)
    (hrequest :
      natBitLength
          (Nat.pair index (Nat.pair inputCode (Nat.pair width count))) ≤
        maximumBits)
    (houtput :
      natBitLength
          (projectionRunnerAtomOutput inputArity inputCode width count
            index) ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (projectionRunnerAtomFuel width count index)
        (initialNPOracleState inputArity
          (Nat.pair index (Nat.pair inputCode (Nat.pair width count)))) =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index) := by
  let shape := Nat.pair width count
  let context := Nat.pair inputCode shape
  let request := Nat.pair index context
  let state0 := initialNPOracleState inputArity request
  let state1 := (state0.write 2 index).jump 1
  let state2 := (state1.write 3 context).jump 2
  let state3 := (state2.write 4 inputCode).jump 3
  let state4 := (state3.write 5 shape).jump 4
  let state5 := (state4.write 6 width).jump 5
  let state6 := (state5.write 7 count).jump 6
  let state7 := (state6.write 14 count).jump 7
  let state8 := (state7.write 8 index).jump 8
  have hcontextLe : context ≤ request := by
    exact Nat.right_le_pair index context
  have hindexLe : index ≤ request := by
    exact Nat.left_le_pair index context
  have hshapeLe : shape ≤ request :=
    (Nat.right_le_pair inputCode shape).trans hcontextLe
  have hinputCodeLe : inputCode ≤ request :=
    (Nat.left_le_pair inputCode shape).trans hcontextLe
  have hwidthLe : width ≤ request :=
    (Nat.left_le_pair width count).trans hshapeLe
  have hcountLe : count ≤ request :=
    (Nat.right_le_pair width count).trans hshapeLe
  have fits :
      ∀ candidate ≤ request, natBitLength candidate ≤ maximumBits := by
    intro candidate hcandidate
    exact
      (PolynomialClock.natBitLength_mono hcandidate).trans
        (by simpa only [request, context, shape] using hrequest)
  have hindexBits := fits index hindexLe
  have hcontextBits := fits context hcontextLe
  have hinputCodeBits := fits inputCode hinputCodeLe
  have hshapeBits := fits shape hshapeLe
  have hwidthBits := fits width hwidthLe
  have hcountBits := fits count hcountLe
  rw [show projectionRunnerAtomFuel width count index =
    (7 + projectionRunnerAtomCursorFuel width index count) + 1 by
      simp only [projectionRunnerAtomFuel]
      omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState]) hindexBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (7 + projectionRunnerAtomCursorFuel width index count) state1 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 7 + projectionRunnerAtomCursorFuel width index count =
    (6 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_unpairRight_instruction (value := context) (by rfl) rfl
    (by simp [state1, state0, request, initialNPOracleState])
    hcontextBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (6 + projectionRunnerAtomCursorFuel width index count) state2 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 6 + projectionRunnerAtomCursorFuel width index count =
    (5 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputCode) (by rfl) rfl
    (by simp [state2, state1, context]) hinputCodeBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (5 + projectionRunnerAtomCursorFuel width index count) state3 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 5 + projectionRunnerAtomCursorFuel width index count =
    (4 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_unpairRight_instruction (value := shape) (by rfl) rfl
    (by simp [state3, state2, state1, context]) hshapeBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (4 + projectionRunnerAtomCursorFuel width index count) state4 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 4 + projectionRunnerAtomCursorFuel width index count =
    (3 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [state4, state3, shape]) hwidthBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (3 + projectionRunnerAtomCursorFuel width index count) state5 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 3 + projectionRunnerAtomCursorFuel width index count =
    (2 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_unpairRight_instruction (value := count) (by rfl) rfl
    (by simp [state5, state4, state3, shape]) hcountBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (2 + projectionRunnerAtomCursorFuel width index count) state6 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 2 + projectionRunnerAtomCursorFuel width index count =
    (1 + projectionRunnerAtomCursorFuel width index count) + 1 by omega]
  rw [run_copy_instruction (value := count) (by rfl) rfl
    (by rfl) hcountBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (1 + projectionRunnerAtomCursorFuel width index count) state7 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  rw [show 1 + projectionRunnerAtomCursorFuel width index count =
    projectionRunnerAtomCursorFuel width index count + 1 by omega]
  rw [run_copy_instruction (value := index) (by rfl) rfl
    (by simp [state7, state6, state5, state4, state3, state2, state1,
      state0, request, initialNPOracleState]) hindexBits]
  change
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (projectionRunnerAtomCursorFuel width index count) state8 =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index)
  exact run_projectionRunnerAtomCursor inputArity inputCode width count
    index count 0 maximumBits state8 (by omega) rfl
    (by simp [state8, state7, state6, state5, state4, state3, state2,
      state1, state0, request, initialNPOracleState])
    (by simp [state8, state7, state6, state5, state4, state3, state2,
      state1, state0, request, initialNPOracleState])
    (by rfl) (by rfl) (by rfl)
    (by simp [state8, state7, state6, state5, state4, state3, state2,
      state1, state0, request, initialNPOracleState])
    (by rfl) hwidthBits hcountBits hindexBits
    (by simpa only [projectionRunnerAtomOutput] using houtput)

/-- The canonical request/output maximum is a sufficient exact width budget. -/
theorem run_projectionRunnerAtomProgram
    (inputArity inputCode width count index : ℕ) :
    runNPOracleProgram projectionRunnerAtomProgram
        (projectionRunnerAtomMaximumBits inputArity inputCode width count
          index)
        (projectionRunnerAtomFuel width count index)
        (initialNPOracleState inputArity
          (Nat.pair index (Nat.pair inputCode (Nat.pair width count)))) =
      some
        (projectionRunnerAtomOutput inputArity inputCode width count
          index) := by
  apply run_projectionRunnerAtomProgram_of_fits
  · exact
      (PolynomialClock.natBitLength_mono
        (Nat.le_max_left _ _)).trans (le_refl _)
  · exact
      (PolynomialClock.natBitLength_mono
        (Nat.le_max_right _ _)).trans (le_refl _)

end NearCubicWires.ProjectionRunnerAtomProgram
