import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed random access into canonical balanced sequences

Structural compilers reuse finite runner tables.  Those tables are encoded with
`encodeBalancedList`, so random access must follow the canonical midpoint tree
without first expanding it to a linked spine.  This fixed oracle-free program
does exactly that.  Every live value is a subterm of the input or a decrement
of the public length/index, which gives an honest width bound by the encoded
request itself.
-/

namespace NearCubicWires.CanonicalBalancedLookupProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces

/-- Public request `pair(length, pair(index, balancedCode))`. -/
def balancedLookupInput (values : List ℕ) (index : ℕ) : ℕ :=
  Nat.pair values.length (Nat.pair index (encodeBalancedList values))

/-- Register ABI:

* `r0`: request, then the current balanced subtree, then the selected atom;
* `r2`: current subtree length;
* `r4`: index relative to the current subtree;
* `r6`/`r7`: left/right subtree lengths;
* `r8`/`r9`: destructive comparison copies;
* `r10`: constant one used by `shiftRight`.

The zero-length branch is total but is outside the public lookup theorem.
-/
def canonicalBalancedLookupProgram : NPOracleProgram :=
  [ .set 10 1 1
  , .unpairLeft 0 2 2
  , .unpairRight 0 3 3
  , .unpairLeft 3 4 4
  , .unpairRight 3 0 5
  , .branchZero 2 30 6
  , .copy 2 5 7
  , .decrement 5 8
  , .branchZero 5 29 9
  , .shiftRight 2 1 7 10
  , .copy 2 6 11
  , .copy 7 9 12
    -- `r6 := count - floor(count / 2)`.
  , .branchZero 9 16 13
  , .decrement 9 14
  , .decrement 6 12
    -- Unreachable padding keeps the branch targets visually aligned.
  , .branchZero 10 16 16
  , .copy 4 8 17
  , .copy 6 9 18
    -- Simultaneously subtract the left length from the candidate index.
  , .branchZero 9 22 19
  , .branchZero 8 26 20
  , .decrement 9 21
  , .decrement 8 18
    -- Right subtree; `r8` is the relative right index.
  , .unpairRight 0 3 23
  , .unpairRight 3 0 24
  , .copy 7 2 25
  , .copy 8 4 5
    -- Left subtree; the original relative index in `r4` is unchanged.
  , .unpairRight 0 3 27
  , .unpairLeft 3 0 28
  , .copy 6 2 5
    -- Singleton leaf.
  , .unpairRight 0 0 30
  , .halt 0
  ]

@[simp] theorem canonicalBalancedLookupProgram_length :
    canonicalBalancedLookupProgram.length = 31 := by
  rfl

theorem canonicalBalancedLookupProgram_oracleFree :
    OracleFree canonicalBalancedLookupProgram := by
  rfl

/-- Exact remaining fuel from the loop head (`pc = 5`). -/
def balancedLookupLoopFuel : (values : List ℕ) → ℕ → ℕ
  | [], _index => 2
  | [_value], _index => 6
  | first :: second :: rest, index =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      let left := values.take leftLength
      let right := values.drop leftLength
      if index < leftLength then
        15 + 3 * right.length + 4 * index +
          balancedLookupLoopFuel left index
      else
        15 + 3 * right.length + 4 * left.length +
          balancedLookupLoopFuel right (index - leftLength)
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

def balancedLookupFuel (values : List ℕ) (index : ℕ) : ℕ :=
  5 + balancedLookupLoopFuel values index

/-- The packed request dominates all values touched by the lookup trace. -/
def balancedLookupMaximumBits (values : List ℕ) (index : ℕ) : ℕ :=
  natBitLength (balancedLookupInput values index)

private theorem npOracleState_ext
    (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Exact simultaneous subtraction used to recover the larger midpoint half.
Only `r6` and `r9` are modified. -/
private theorem run_subtractRight
    (count right maximumBits extra : ℕ) (state : NPOracleState)
    (hright : right ≤ count)
    (hpc : state.pc = 12)
    (hcount : state.registers 6 = count)
    (hrightRegister : state.registers 9 = right)
    (hcountBits : natBitLength count ≤ maximumBits)
    (hrightBits : natBitLength right ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (extra + (3 * right + 1)) state =
      runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
        (((state.write 9 0).write 6 (count - right)).jump 16) := by
  induction right generalizing count state with
  | zero =>
      rw [show extra + (3 * 0 + 1) = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hrightRegister, if_pos rfl]
      congr 2
      apply npOracleState_ext
      · rfl
      · funext register
        simp only [NPOracleState.write]
        by_cases hnine : register = 9
        · subst register
          simp [hrightRegister]
        · by_cases hsix : register = 6
          · subst register
            simp [hcount]
          · simp [hnine, hsix]
  | succ right inductionHypothesis =>
      have hcountPositive : 0 < count := by omega
      let state1 := state.jump 13
      let state2 := (state1.write 9 right).jump 14
      let state3 := (state2.write 6 count.pred).jump 12
      have hrightNext : right ≤ count.pred :=
        Nat.le_pred_of_lt hright
      have hcountPredBits :
          natBitLength count.pred ≤ maximumBits :=
        (decrement_bits_le count).trans hcountBits
      have hrightPredBits :
          natBitLength right ≤ maximumBits :=
        (decrement_bits_le (right + 1)).trans (by
          simpa only [Nat.succ_eq_add_one] using hrightBits)
      rw [show extra + (3 * (right + 1) + 1) =
        (extra + (3 * right + 1) + 2) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hrightRegister, if_neg (by omega)]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (3 * right + 1) + 2) state1 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 6 (count - (right + 1))).jump 16)
      rw [show extra + (3 * right + 1) + 2 =
        (extra + (3 * right + 1) + 1) + 1 by omega]
      rw [run_decrement_instruction (value := right) (by rfl) rfl
        (by simp [state1, hrightRegister]) hrightPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (3 * right + 1) + 1) state2 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 6 (count - (right + 1))).jump 16)
      rw [show extra + (3 * right + 1) + 1 =
        (extra + (3 * right + 1)) + 1 by omega]
      rw [run_decrement_instruction (value := count.pred) (by rfl) rfl
        (by simp [state2, state1, hcount]) hcountPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (3 * right + 1)) state3 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 6 (count - (right + 1))).jump 16)
      rw [inductionHypothesis count.pred state3 hrightNext rfl
        (by simp [state3, state2, state1, NPOracleState.write])
        (by simp [state3, state2, state1, NPOracleState.write])
        hcountPredBits
        hrightPredBits]
      have hsub :
          count - 1 - right = count - (right + 1) := by
        omega
      have hstateEq :
          (((state3.write 9 0).write 6 (count.pred - right)).jump 16) =
            (((state.write 9 0).write 6
              (count - (right + 1))).jump 16) := by
        apply npOracleState_ext
        · simp [state3]
        · funext register
          simp only [NPOracleState.write]
          by_cases hnine : register = 9
          · subst register
            simp
          · by_cases hsix : register = 6
            · subst register
              simp [state3, hsub]
            · simp [state3, state2, state1, hnine, hsix]
      rw [hstateEq]

/-- Exact comparison path when the target remains in the left subtree. -/
private theorem run_compareLeft
    (left index maximumBits extra : ℕ) (state : NPOracleState)
    (hindex : index < left)
    (hpc : state.pc = 18)
    (hleft : state.registers 9 = left)
    (hindexRegister : state.registers 8 = index)
    (hleftBits : natBitLength left ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (extra + (4 * index + 2)) state =
      runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
        (((state.write 9 (left - index)).write 8 0).jump 26) := by
  induction index generalizing left state with
  | zero =>
      have hleftNonzero : left ≠ 0 := by omega
      rw [show extra + (4 * 0 + 2) = (extra + 1) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hleft, if_neg hleftNonzero]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show (state.jump 19).registers 8 = 0 by
        simpa [NPOracleState.jump] using hindexRegister, if_pos rfl]
      have hstateEq :
          (state.jump 26) =
            (((state.write 9 (left - 0)).write 8 0).jump 26) := by
        apply npOracleState_ext
        · rfl
        · funext register
          simp only [NPOracleState.write]
          by_cases hnine : register = 9
          · subst register
            simp [hleft]
          · by_cases height : register = 8
            · subst register
              simp [hindexRegister]
            · simp [hnine, height]
      simpa only [NPOracleState.jump] using
        congrArg
          (runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra)
          hstateEq
  | succ index inductionHypothesis =>
      have hleftPositive : 0 < left := by omega
      have hnext : index < left.pred := by
        rw [Nat.pred_eq_sub_one]
        omega
      let state1 := state.jump 19
      let state2 := state1.jump 20
      let state3 := (state2.write 9 left.pred).jump 21
      let state4 := (state3.write 8 index).jump 18
      have hleftPredBits :
          natBitLength left.pred ≤ maximumBits :=
        (decrement_bits_le left).trans hleftBits
      have hindexPredBits :
          natBitLength index ≤ maximumBits :=
        (decrement_bits_le (index + 1)).trans (by
          simpa only [Nat.succ_eq_add_one] using hindexBits)
      rw [show extra + (4 * (index + 1) + 2) =
        (extra + (4 * index + 2) + 3) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hleft, if_neg (by omega)]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * index + 2) + 3) state1 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 (left - (index + 1))).write 8 0).jump 26)
      rw [show extra + (4 * index + 2) + 3 =
        (extra + (4 * index + 2) + 2) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state1.registers 8 = index + 1 by
        simp [state1, hindexRegister]]
      rw [if_neg (by omega)]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * index + 2) + 2) state2 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 (left - (index + 1))).write 8 0).jump 26)
      rw [show extra + (4 * index + 2) + 2 =
        (extra + (4 * index + 2) + 1) + 1 by omega]
      rw [run_decrement_instruction (value := left.pred) (by rfl) rfl
        (by simp [state2, state1, hleft]) hleftPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * index + 2) + 1) state3 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 (left - (index + 1))).write 8 0).jump 26)
      rw [show extra + (4 * index + 2) + 1 =
        (extra + (4 * index + 2)) + 1 by omega]
      rw [run_decrement_instruction (value := index) (by rfl) rfl
        (by simp [state3, state2, state1, hindexRegister])
        hindexPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * index + 2)) state4 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 (left - (index + 1))).write 8 0).jump 26)
      rw [inductionHypothesis left.pred state4 hnext rfl
        (by simp [state4, state3, state2, state1, NPOracleState.write])
        (by simp [state4, state3, state2, state1, NPOracleState.write])
        hleftPredBits hindexPredBits]
      have hsub :
          left - 1 - index = left - (index + 1) := by
        omega
      have hstateEq :
          (((state4.write 9 (left.pred - index)).write 8 0).jump 26) =
            (((state.write 9 (left - (index + 1))).write 8 0).jump 26) := by
        apply npOracleState_ext
        · simp [state4]
        · funext register
          simp only [NPOracleState.write]
          by_cases hnine : register = 9
          · subst register
            simp [state4, hsub]
          · by_cases height : register = 8
            · subst register
              simp
            · simp [state4, state3, state2, state1, hnine, height]
      rw [hstateEq]

/-- Exact comparison path when the target belongs to the right subtree. -/
private theorem run_compareRight
    (left index maximumBits extra : ℕ) (state : NPOracleState)
    (hindex : left ≤ index)
    (hpc : state.pc = 18)
    (hleft : state.registers 9 = left)
    (hindexRegister : state.registers 8 = index)
    (hleftBits : natBitLength left ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (extra + (4 * left + 1)) state =
      runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
        (((state.write 9 0).write 8 (index - left)).jump 22) := by
  induction left generalizing index state with
  | zero =>
      rw [show extra + (4 * 0 + 1) = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hleft, if_pos rfl]
      have hstateEq :
          state.jump 22 =
            (((state.write 9 0).write 8 (index - 0)).jump 22) := by
        apply npOracleState_ext
        · rfl
        · funext register
          simp only [NPOracleState.write]
          by_cases hnine : register = 9
          · subst register
            simp [hleft]
          · by_cases height : register = 8
            · subst register
              simp [hindexRegister]
            · simp [hnine, height]
      simpa only using
        congrArg
          (runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra)
          hstateEq
  | succ left inductionHypothesis =>
      have hindexPositive : 0 < index := by omega
      have hnext : left ≤ index.pred := by
        rw [Nat.pred_eq_sub_one]
        omega
      let state1 := state.jump 19
      let state2 := state1.jump 20
      let state3 := (state2.write 9 left).jump 21
      let state4 := (state3.write 8 index.pred).jump 18
      have hleftPredBits :
          natBitLength left ≤ maximumBits :=
        (decrement_bits_le (left + 1)).trans (by
          simpa only [Nat.succ_eq_add_one] using hleftBits)
      have hindexPredBits :
          natBitLength index.pred ≤ maximumBits :=
        (decrement_bits_le index).trans hindexBits
      rw [show extra + (4 * (left + 1) + 1) =
        (extra + (4 * left + 1) + 3) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hleft, if_neg (by omega)]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * left + 1) + 3) state1 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 8 (index - (left + 1))).jump 22)
      rw [show extra + (4 * left + 1) + 3 =
        (extra + (4 * left + 1) + 2) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state1.registers 8 = index by
        simp [state1, hindexRegister]]
      rw [if_neg (by omega)]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * left + 1) + 2) state2 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 8 (index - (left + 1))).jump 22)
      rw [show extra + (4 * left + 1) + 2 =
        (extra + (4 * left + 1) + 1) + 1 by omega]
      rw [run_decrement_instruction (value := left) (by rfl) rfl
        (by simp [state2, state1, hleft]) hleftPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * left + 1) + 1) state3 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 8 (index - (left + 1))).jump 22)
      rw [show extra + (4 * left + 1) + 1 =
        (extra + (4 * left + 1)) + 1 by omega]
      rw [run_decrement_instruction (value := index.pred) (by rfl) rfl
        (by simp [state3, state2, state1, hindexRegister])
        hindexPredBits]
      change
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (extra + (4 * left + 1)) state4 =
          runNPOracleProgram canonicalBalancedLookupProgram maximumBits extra
            (((state.write 9 0).write 8 (index - (left + 1))).jump 22)
      rw [inductionHypothesis index.pred state4 hnext rfl
        (by simp [state4, state3, state2, state1, NPOracleState.write])
        (by simp [state4, state3, state2, state1, NPOracleState.write])
        hleftPredBits hindexPredBits]
      have hsub :
          index - 1 - left = index - (left + 1) := by
        omega
      have hstateEq :
          (((state4.write 9 0).write 8 (index.pred - left)).jump 22) =
            (((state.write 9 0).write 8
              (index - (left + 1))).jump 22) := by
        apply npOracleState_ext
        · simp [state4]
        · funext register
          simp only [NPOracleState.write]
          by_cases hnine : register = 9
          · subst register
            simp
          · by_cases height : register = 8
            · subst register
              simp [state4, hsub]
            · simp [state4, state3, state2, state1, hnine, height]
      rw [hstateEq]

private theorem run_singletonLoop
    (value maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 5)
    (hcode : state.registers 0 = encodeBalancedList [value])
    (hcount : state.registers 2 = 1)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hvalueBits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (balancedLookupLoopFuel [value] 0) state =
      some value := by
  let state1 := state.jump 6
  let state2 := (state1.write 5 1).jump 7
  let state3 := (state2.write 5 0).jump 8
  let state4 := state3.jump 29
  let state5 := (state4.write 0 value).jump 30
  rw [show balancedLookupLoopFuel [value] 0 = 6 by
    simp [balancedLookupLoopFuel]]
  rw [show 6 = 5 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc]
  rw [hcount, if_neg (by omega)]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits 5 state1 =
      some value
  rw [show 5 = 4 + 1 by omega]
  rw [run_copy_instruction (value := 1) (by rfl) rfl
    (by simp [state1, hcount]) honeBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits 4 state2 =
      some value
  rw [show 4 = 3 + 1 by omega]
  rw [run_decrement_instruction (value := 0) (by rfl) rfl
    (by simp [state2]) hzeroBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits 3 state3 =
      some value
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show state3.registers 5 = 0 by simp [state3], if_pos rfl]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits 2 state4 =
      some value
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := value) (by rfl) rfl
    (by simp [state4, state3, state2, state1, hcode,
      encodeBalancedList.eq_def]) hvalueBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits 1 state5 =
      some value
  exact run_halt_instruction (value := value) (by rfl) rfl
    (by simp [state5]) hvalueBits

/-- Exact lookup from the shared loop head.  The proof follows the same
midpoint split as `encodeBalancedList`, so no alternate tree shape is admitted. -/
private theorem run_balancedLookupLoop
    (values : List ℕ) (index maximumBits : ℕ) (state : NPOracleState)
    (hindex : index < values.length)
    (hpc : state.pc = 5)
    (hcode : state.registers 0 = encodeBalancedList values)
    (hcount : state.registers 2 = values.length)
    (hindexRegister : state.registers 4 = index)
    (hcodeBits :
      natBitLength (encodeBalancedList values) ≤ maximumBits)
    (hcountBits : natBitLength values.length ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (balancedLookupLoopFuel values index) state =
      some values[index] := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values index state with
  | h length inductionHypothesis =>
      cases values with
      | nil =>
          simp at hindex
      | cons first rest =>
          cases rest with
          | nil =>
              have hindexZero : index = 0 := by simpa using hindex
              cases hindexZero
              have honeBits : natBitLength 1 ≤ maximumBits := by
                simpa using hcountBits
              have hzeroBits : natBitLength 0 ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono (Nat.zero_le 1)).trans
                  honeBits
              have hvalueLe :
                  first ≤ encodeBalancedList [first] := by
                rw [encodeBalancedList.eq_def]
                exact Nat.right_le_pair 1 first
              have hvalueBits :
                  natBitLength first ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono hvalueLe).trans hcodeBits
              exact
                run_singletonLoop first maximumBits state hpc hcode
                  (by simpa using hcount) honeBits hzeroBits hvalueBits
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              let leftCode := encodeBalancedList left
              let rightCode := encodeBalancedList right
              let branchPayload := Nat.pair leftCode rightCode
              let code := Nat.pair 2 branchPayload
              have hindexValues : index < values.length := by
                simpa only [values] using hindex
              have hcodeValues :
                  state.registers 0 = encodeBalancedList values := by
                simpa only [values] using hcode
              have hcountValues :
                  state.registers 2 = values.length := by
                simpa only [values] using hcount
              have hcodeBitsValues :
                  natBitLength (encodeBalancedList values) ≤ maximumBits := by
                simpa only [values] using hcodeBits
              have hcountBitsValues :
                  natBitLength values.length ≤ maximumBits := by
                simpa only [values] using hcountBits
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLeValues : leftLength ≤ values.length :=
                hleftLtValues.le
              have hleftLength : left.length = leftLength := by
                simp [left, hleftLeValues]
              have hrightLength :
                  right.length = values.length - leftLength := by
                simp [right]
              have hrightPositive : 0 < right.length := by
                rw [hrightLength]
                dsimp [leftLength]
                omega
              have hrightLeLeft : right.length ≤ left.length := by
                rw [hrightLength, hleftLength]
                dsimp [leftLength]
                omega
              have hleftLt : left.length < length := by
                rw [hleftLength, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length :=
                lt_of_le_of_lt hrightLeLeft hleftLt
              have hsplit : left ++ right = values :=
                List.take_append_drop leftLength values
              have hrightHalf :
                  Nat.shiftRight values.length 1 = right.length := by
                change values.length / 2 = right.length
                rw [hrightLength]
                dsimp [leftLength]
                omega
              have hleftFromRight :
                  values.length - right.length = left.length := by
                rw [hrightLength, hleftLength]
                omega
              have hcodeEq :
                  encodeBalancedList values = code := by
                dsimp only [values, leftLength, left, right]
                rw [encodeBalancedList.eq_def]
              have hbranchPayloadLe : branchPayload ≤ code := by
                exact Nat.right_le_pair 2 branchPayload
              have hleftCodeLe : leftCode ≤ code :=
                (Nat.left_le_pair leftCode rightCode).trans hbranchPayloadLe
              have hrightCodeLe : rightCode ≤ code :=
                (Nat.right_le_pair leftCode rightCode).trans hbranchPayloadLe
              have hcodeBits' : natBitLength code ≤ maximumBits := by
                rw [← hcodeEq]
                exact hcodeBitsValues
              have hleftCodeBits :
                  natBitLength leftCode ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono hleftCodeLe).trans
                  hcodeBits'
              have hrightCodeBits :
                  natBitLength rightCode ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono hrightCodeLe).trans
                  hcodeBits'
              have hbranchPayloadBits :
                  natBitLength branchPayload ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono hbranchPayloadLe).trans
                  hcodeBits'
              have hleftLengthBits :
                  natBitLength left.length ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono <|
                  (by rw [hleftLength]; exact hleftLeValues)).trans
                    hcountBitsValues
              have hrightLengthBits :
                  natBitLength right.length ≤ maximumBits :=
                (PolynomialClock.natBitLength_mono <|
                    hrightLeLeft.trans (by
                    rw [hleftLength]
                    exact hleftLeValues)).trans hcountBitsValues
              have hcountPredBits :
                  natBitLength values.length.pred ≤ maximumBits :=
                (decrement_bits_le values.length).trans hcountBitsValues
              have hcountPredNonzero : values.length.pred ≠ 0 := by
                simp only [Nat.pred_eq_sub_one]
                omega
              have hrightLeValues : right.length ≤ values.length :=
                hrightLeLeft.trans (by
                  rw [hleftLength]
                  exact hleftLeValues)
              let state1 := state.jump 6
              let state2 :=
                (state1.write 5 values.length).jump 7
              let state3 :=
                (state2.write 5 values.length.pred).jump 8
              let state4 := state3.jump 9
              let state5 :=
                (state4.write 7 right.length).jump 10
              let state6 :=
                (state5.write 6 values.length).jump 11
              let state7 :=
                (state6.write 9 right.length).jump 12
              let state8 :=
                (((state7.write 9 0).write 6 left.length).jump 16)
              let state9 := (state8.write 8 index).jump 17
              let state10 :=
                (state9.write 9 left.length).jump 18
              change
                runNPOracleProgram canonicalBalancedLookupProgram maximumBits
                    (balancedLookupLoopFuel values index) state =
                  some values[index]
              by_cases hleftSide : index < left.length
              · let recursiveFuel := balancedLookupLoopFuel left index
                let state11 :=
                  (((state10.write 9 (left.length - index)).write 8 0).jump 26)
                let state12 :=
                  (state11.write 3 branchPayload).jump 27
                let state13 := (state12.write 0 leftCode).jump 28
                let state14 :=
                  (state13.write 2 left.length).jump 5
                have hfuel :
                    balancedLookupLoopFuel values index =
                      15 + 3 * right.length + 4 * index +
                        recursiveFuel := by
                  rw [balancedLookupLoopFuel.eq_def]
                  simp only [values, leftLength, right]
                  rw [if_pos (by simpa only [hleftLength] using hleftSide)]
                rw [hfuel]
                rw [show
                  15 + 3 * right.length + 4 * index + recursiveFuel =
                    (14 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_branchZero_instruction (by rfl) hpc]
                rw [hcountValues, if_neg (by omega)]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (14 + 3 * right.length + 4 * index +
                        recursiveFuel) state1 =
                    some values[index]
                rw [show
                  14 + 3 * right.length + 4 * index + recursiveFuel =
                    (13 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := values.length) (by rfl) rfl
                  (by simpa [state1] using hcountValues) hcountBitsValues]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (13 + 3 * right.length + 4 * index +
                        recursiveFuel) state2 =
                    some values[index]
                rw [show
                  13 + 3 * right.length + 4 * index + recursiveFuel =
                    (12 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_decrement_instruction
                  (value := values.length.pred) (by rfl) rfl
                  (by simp [state2]) hcountPredBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (12 + 3 * right.length + 4 * index +
                        recursiveFuel) state3 =
                    some values[index]
                rw [show
                  12 + 3 * right.length + 4 * index + recursiveFuel =
                    (11 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_branchZero_instruction (by rfl) rfl]
                rw [show state3.registers 5 = values.length.pred by
                  simp [state3], if_neg hcountPredNonzero]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (11 + 3 * right.length + 4 * index +
                        recursiveFuel) state4 =
                    some values[index]
                rw [show
                  11 + 3 * right.length + 4 * index + recursiveFuel =
                    (10 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_shiftRight_instruction
                  (value := right.length) (by rfl) rfl
                  (by
                    have hstate4Count :
                        state4.registers 2 = values.length := by
                      simpa [state4, state3, state2, state1] using
                        hcountValues
                    exact hstate4Count ▸ hrightHalf)
                  hrightLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (10 + 3 * right.length + 4 * index +
                        recursiveFuel) state5 =
                    some values[index]
                rw [show
                  10 + 3 * right.length + 4 * index + recursiveFuel =
                    (9 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := values.length) (by rfl) rfl
                  (by simp [state5, state4, state3, state2, state1,
                    hcountValues]) hcountBitsValues]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (9 + 3 * right.length + 4 * index +
                        recursiveFuel) state6 =
                    some values[index]
                rw [show
                  9 + 3 * right.length + 4 * index + recursiveFuel =
                    (8 + 3 * right.length + 4 * index +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := right.length) (by rfl) rfl
                  (by rfl) hrightLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (8 + 3 * right.length + 4 * index +
                        recursiveFuel) state7 =
                    some values[index]
                rw [show
                  8 + 3 * right.length + 4 * index + recursiveFuel =
                    (7 + 4 * index + recursiveFuel) +
                      (3 * right.length + 1) by omega]
                rw [run_subtractRight values.length right.length
                  maximumBits (7 + 4 * index + recursiveFuel) state7
                  hrightLeValues rfl (by rfl) (by rfl)
                  hcountBitsValues hrightLengthBits]
                have hstate8 :
                    (((state7.write 9 0).write 6
                      (values.length - right.length)).jump 16) = state8 := by
                  simp only [state8]
                  rw [hleftFromRight]
                rw [hstate8]
                rw [show
                  7 + 4 * index + recursiveFuel =
                    (6 + 4 * index + recursiveFuel) + 1 by omega]
                rw [run_copy_instruction (value := index) (by rfl) rfl
                  (by simp [state8, state7, state6, state5, state4,
                    state3, state2, state1, hindexRegister]) hindexBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (6 + 4 * index + recursiveFuel) state9 =
                    some values[index]
                rw [show
                  6 + 4 * index + recursiveFuel =
                    (5 + 4 * index + recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := left.length) (by rfl) rfl
                  (by simp [state9, state8]) hleftLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (5 + 4 * index + recursiveFuel) state10 =
                    some values[index]
                rw [show
                  5 + 4 * index + recursiveFuel =
                    (3 + recursiveFuel) + (4 * index + 2) by omega]
                rw [run_compareLeft left.length index maximumBits
                  (3 + recursiveFuel) state10 hleftSide rfl
                  (by rfl) (by rfl)
                  hleftLengthBits hindexBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (3 + recursiveFuel) state11 =
                    some values[index]
                rw [show 3 + recursiveFuel =
                  (2 + recursiveFuel) + 1 by omega]
                rw [run_unpairRight_instruction
                  (value := branchPayload) (by rfl) rfl
                  (by simp [state11, state10, state9, state8, state7,
                    state6, state5, state4, state3, state2, state1,
                    hcodeValues, hcodeEq, code])
                  hbranchPayloadBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (2 + recursiveFuel) state12 =
                    some values[index]
                rw [show 2 + recursiveFuel =
                  (1 + recursiveFuel) + 1 by omega]
                rw [run_unpairLeft_instruction
                  (value := leftCode) (by rfl) rfl
                  (by simp [state12, branchPayload]) hleftCodeBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (1 + recursiveFuel) state13 =
                    some values[index]
                rw [show 1 + recursiveFuel = recursiveFuel + 1 by omega]
                have hstate9Left :
                    state9.registers 6 = left.length := by
                  rfl
                rw [run_copy_instruction
                  (value := left.length) (by rfl) rfl
                  (by
                    simpa [state13, state12, state11, state10] using
                      hstate9Left)
                  hleftLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits recursiveFuel state14 =
                    some values[index]
                rw [inductionHypothesis left.length hleftLt left
                  index state14 hleftSide rfl
                  (by rfl) (by rfl)
                  (by simp [state14, state13, state12, state11, state10,
                    state9, state8, state7, state6, state5, state4,
                    state3, state2, state1, hindexRegister])
                  hleftCodeBits hleftLengthBits hindexBits rfl]
                rw [← List.getElem?_eq_getElem hleftSide,
                  ← List.getElem?_eq_getElem hindexValues, ← hsplit,
                  List.getElem?_append_left hleftSide]
              · have hrightSide :
                    index - left.length < right.length := by
                  have hindexValues : index < values.length := by
                    simpa only [values] using hindex
                  rw [← hsplit] at hindexValues
                  simp only [List.length_append] at hindexValues
                  omega
                let recursiveFuel :=
                  balancedLookupLoopFuel right (index - left.length)
                let state11 :=
                  (((state10.write 9 0).write 8
                    (index - left.length)).jump 22)
                let state12 :=
                  (state11.write 3 branchPayload).jump 23
                let state13 :=
                  (state12.write 0 rightCode).jump 24
                let state14 :=
                  (state13.write 2 right.length).jump 25
                let state15 :=
                  (state14.write 4 (index - left.length)).jump 5
                have hrelativeIndexBits :
                    natBitLength (index - left.length) ≤ maximumBits :=
                  (PolynomialClock.natBitLength_mono
                    (Nat.sub_le index left.length)).trans hindexBits
                have hfuel :
                    balancedLookupLoopFuel values index =
                      15 + 3 * right.length + 4 * left.length +
                        recursiveFuel := by
                  rw [balancedLookupLoopFuel.eq_def]
                  simp only [values, leftLength, left, right]
                  rw [if_neg (by
                    simpa only [hleftLength] using hleftSide)]
                  simp only [recursiveFuel, hleftLength]
                  rfl
                rw [hfuel]
                rw [show
                  15 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (14 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_branchZero_instruction (by rfl) hpc]
                rw [hcountValues, if_neg (by omega)]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (14 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state1 =
                    some values[index]
                rw [show
                  14 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (13 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := values.length) (by rfl) rfl
                  (by simpa [state1] using hcountValues) hcountBitsValues]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (13 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state2 =
                    some values[index]
                rw [show
                  13 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (12 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_decrement_instruction
                  (value := values.length.pred) (by rfl) rfl
                  (by simp [state2]) hcountPredBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (12 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state3 =
                    some values[index]
                rw [show
                  12 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (11 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_branchZero_instruction (by rfl) rfl]
                rw [show state3.registers 5 = values.length.pred by
                  simp [state3], if_neg hcountPredNonzero]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (11 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state4 =
                    some values[index]
                rw [show
                  11 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (10 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_shiftRight_instruction
                  (value := right.length) (by rfl) rfl
                  (by
                    have hstate4Count :
                        state4.registers 2 = values.length := by
                      simpa [state4, state3, state2, state1] using
                        hcountValues
                    exact hstate4Count ▸ hrightHalf)
                  hrightLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (10 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state5 =
                    some values[index]
                rw [show
                  10 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (9 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := values.length) (by rfl) rfl
                  (by simp [state5, state4, state3, state2, state1,
                    hcountValues]) hcountBitsValues]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (9 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state6 =
                    some values[index]
                rw [show
                  9 + 3 * right.length + 4 * left.length +
                      recursiveFuel =
                    (8 + 3 * right.length + 4 * left.length +
                      recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := right.length) (by rfl) rfl
                  (by rfl) hrightLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (8 + 3 * right.length + 4 * left.length +
                        recursiveFuel) state7 =
                    some values[index]
                rw [show
                  8 + 3 * right.length + 4 * left.length + recursiveFuel =
                    (7 + 4 * left.length + recursiveFuel) +
                      (3 * right.length + 1) by omega]
                rw [run_subtractRight values.length right.length
                  maximumBits
                  (7 + 4 * left.length + recursiveFuel) state7
                  hrightLeValues rfl (by rfl) (by rfl)
                  hcountBitsValues hrightLengthBits]
                have hstate8 :
                    (((state7.write 9 0).write 6
                      (values.length - right.length)).jump 16) = state8 := by
                  simp only [state8]
                  rw [hleftFromRight]
                rw [hstate8]
                rw [show
                  7 + 4 * left.length + recursiveFuel =
                    (6 + 4 * left.length + recursiveFuel) + 1 by omega]
                rw [run_copy_instruction (value := index) (by rfl) rfl
                  (by simp [state8, state7, state6, state5, state4,
                    state3, state2, state1, hindexRegister]) hindexBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (6 + 4 * left.length + recursiveFuel) state9 =
                    some values[index]
                rw [show
                  6 + 4 * left.length + recursiveFuel =
                    (5 + 4 * left.length + recursiveFuel) + 1 by omega]
                rw [run_copy_instruction
                  (value := left.length) (by rfl) rfl
                  (by simp [state9, state8]) hleftLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits
                      (5 + 4 * left.length + recursiveFuel) state10 =
                    some values[index]
                rw [show
                  5 + 4 * left.length + recursiveFuel =
                    (4 + recursiveFuel) + (4 * left.length + 1) by omega]
                rw [run_compareRight left.length index maximumBits
                  (4 + recursiveFuel) state10 (Nat.le_of_not_gt hleftSide)
                  rfl (by rfl) (by rfl)
                  hleftLengthBits hindexBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (4 + recursiveFuel) state11 =
                    some values[index]
                rw [show 4 + recursiveFuel =
                  (3 + recursiveFuel) + 1 by omega]
                rw [run_unpairRight_instruction
                  (value := branchPayload) (by rfl) rfl
                  (by simp [state11, state10, state9, state8, state7,
                    state6, state5, state4, state3, state2, state1,
                    hcodeValues, hcodeEq, code])
                  hbranchPayloadBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (3 + recursiveFuel) state12 =
                    some values[index]
                rw [show 3 + recursiveFuel =
                  (2 + recursiveFuel) + 1 by omega]
                rw [run_unpairRight_instruction
                  (value := rightCode) (by rfl) rfl
                  (by simp [state12, branchPayload]) hrightCodeBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (2 + recursiveFuel) state13 =
                    some values[index]
                rw [show 2 + recursiveFuel =
                  (1 + recursiveFuel) + 1 by omega]
                have hstate9Right :
                    state9.registers 7 = right.length := by
                  rfl
                rw [run_copy_instruction
                  (value := right.length) (by rfl) rfl
                  (by
                    simpa [state13, state12, state11, state10] using
                      hstate9Right)
                  hrightLengthBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits (1 + recursiveFuel) state14 =
                    some values[index]
                rw [show 1 + recursiveFuel = recursiveFuel + 1 by omega]
                rw [run_copy_instruction
                  (value := index - left.length) (by rfl) rfl
                  (by simp [state14, state13, state12, state11])
                  hrelativeIndexBits]
                change
                  runNPOracleProgram canonicalBalancedLookupProgram
                      maximumBits recursiveFuel state15 =
                    some values[index]
                rw [inductionHypothesis right.length hrightLt right
                  (index - left.length) state15 hrightSide rfl
                  (by rfl) (by rfl) (by rfl)
                  hrightCodeBits hrightLengthBits hrelativeIndexBits rfl]
                rw [← List.getElem?_eq_getElem hrightSide,
                  ← List.getElem?_eq_getElem hindexValues, ← hsplit,
                  List.getElem?_append_right
                  (Nat.le_of_not_gt hleftSide)]

/-- Exact execution under any width budget covering the packed request. -/
theorem run_canonicalBalancedLookupProgram_of_fits
    (values : List ℕ) (index inputLength maximumBits : ℕ)
    (hindex : index < values.length)
    (hrequest :
      natBitLength (balancedLookupInput values index) ≤ maximumBits) :
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (balancedLookupFuel values index)
        (initialNPOracleState inputLength
          (balancedLookupInput values index)) =
      some values[index] := by
  let request := balancedLookupInput values index
  let code := encodeBalancedList values
  let payload := Nat.pair index code
  let state0 := initialNPOracleState inputLength request
  let state1 := (state0.write 10 1).jump 1
  let state2 := (state1.write 2 values.length).jump 2
  let state3 := (state2.write 3 payload).jump 3
  let state4 := (state3.write 4 index).jump 4
  let state5 := (state4.write 0 code).jump 5
  have hlengthLe : values.length ≤ request := by
    simpa only [request, balancedLookupInput] using
      Nat.left_le_pair values.length payload
  have hpayloadLe : payload ≤ request := by
    simpa only [request, balancedLookupInput, payload, code] using
      Nat.right_le_pair values.length payload
  have hindexLe : index ≤ request :=
    (Nat.left_le_pair index code).trans hpayloadLe
  have hcodeLe : code ≤ request :=
    (Nat.right_le_pair index code).trans hpayloadLe
  have honeLe : 1 ≤ request :=
    (by omega : 1 ≤ values.length).trans hlengthLe
  have fits :
      ∀ candidate ≤ request, natBitLength candidate ≤ maximumBits := by
    intro candidate hcandidate
    exact
      (PolynomialClock.natBitLength_mono hcandidate).trans
        (by simpa only [request] using hrequest)
  have honeBits := fits 1 honeLe
  have hlengthBits := fits values.length hlengthLe
  have hpayloadBits := fits payload hpayloadLe
  have hindexBits := fits index hindexLe
  have hcodeBits := fits code hcodeLe
  rw [show balancedLookupFuel values index =
    (4 + balancedLookupLoopFuel values index) + 1 by
      simp only [balancedLookupFuel]
      omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (4 + balancedLookupLoopFuel values index) state1 =
      some values[index]
  rw [show 4 + balancedLookupLoopFuel values index =
    (3 + balancedLookupLoopFuel values index) + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := values.length) (by rfl) rfl
    (by simp [state1, state0, request, balancedLookupInput,
      initialNPOracleState]) hlengthBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (3 + balancedLookupLoopFuel values index) state2 =
      some values[index]
  rw [show 3 + balancedLookupLoopFuel values index =
    (2 + balancedLookupLoopFuel values index) + 1 by omega]
  rw [run_unpairRight_instruction (value := payload) (by rfl) rfl
    (by simp [state2, state1, state0, request, payload, code,
      balancedLookupInput, initialNPOracleState]) hpayloadBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (2 + balancedLookupLoopFuel values index) state3 =
      some values[index]
  rw [show 2 + balancedLookupLoopFuel values index =
    (1 + balancedLookupLoopFuel values index) + 1 by omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [state3, payload]) hindexBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (1 + balancedLookupLoopFuel values index) state4 =
      some values[index]
  rw [show 1 + balancedLookupLoopFuel values index =
    balancedLookupLoopFuel values index + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [state4, state3, payload]) hcodeBits]
  change
    runNPOracleProgram canonicalBalancedLookupProgram maximumBits
        (balancedLookupLoopFuel values index) state5 =
      some values[index]
  exact
    run_balancedLookupLoop values index maximumBits state5 hindex rfl
      (by rfl) (by rfl) (by rfl) hcodeBits hlengthBits hindexBits

/-- The canonical request bit length is a sufficient exact width budget. -/
theorem run_canonicalBalancedLookupProgram
    (values : List ℕ) (index inputLength : ℕ)
    (hindex : index < values.length) :
    runNPOracleProgram canonicalBalancedLookupProgram
        (balancedLookupMaximumBits values index)
        (balancedLookupFuel values index)
        (initialNPOracleState inputLength
          (balancedLookupInput values index)) =
      some values[index] :=
  run_canonicalBalancedLookupProgram_of_fits values index inputLength
    (balancedLookupMaximumBits values index) hindex (by rfl)

/-! ## Source-independent resource closure -/

/-- Lookup takes linear time in the public table length.  In particular, its
clock degree is fixed independently of the source machine or table contents. -/
theorem balancedLookupLoopFuel_le
    (values : List ℕ) (index : ℕ)
    (hindex : index < values.length) :
    balancedLookupLoopFuel values index ≤ 22 * values.length := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values index with
  | h length inductionHypothesis =>
      cases values with
      | nil =>
          simp at hindex
      | cons first rest =>
          cases rest with
          | nil =>
              simp_all [balancedLookupLoopFuel]
              omega
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hindexValues : index < values.length := by
                simpa only [values] using hindex
              have hlengthValues : values.length = length := by
                simpa only [values] using hlength
              have htwo : 2 ≤ values.length := by
                simp [values]
              have hleftLe : leftLength ≤ values.length := by
                dsimp only [leftLength]
                omega
              have hleftLength : left.length = leftLength := by
                simp [left, hleftLe]
              have hrightLength :
                  right.length = values.length - leftLength := by
                simp [right]
              have hsplitLength :
                  left.length + right.length = values.length := by
                rw [hleftLength, hrightLength]
                omega
              have hleftPositive : 0 < left.length := by
                rw [hleftLength]
                dsimp only [leftLength]
                omega
              have hrightPositive : 0 < right.length := by
                rw [hrightLength]
                dsimp only [leftLength]
                omega
              have hrightLeLeft : right.length ≤ left.length := by
                rw [hrightLength, hleftLength]
                dsimp only [leftLength]
                omega
              have hleftLeRightSucc :
                  left.length ≤ right.length + 1 := by
                rw [hrightLength, hleftLength]
                dsimp only [leftLength]
                omega
              have hleftLt : left.length < length := by
                rw [← hlengthValues]
                omega
              have hrightLt : right.length < length := by
                rw [← hlengthValues]
                omega
              rw [← hlengthValues]
              change
                balancedLookupLoopFuel values index ≤
                  22 * values.length
              by_cases hleftSide : index < leftLength
              · have hfuel :
                    balancedLookupLoopFuel values index =
                      15 + 3 * right.length + 4 * index +
                        balancedLookupLoopFuel left index := by
                  rw [balancedLookupLoopFuel.eq_def]
                  simp only [values, leftLength, left, right]
                  rw [if_pos hleftSide]
                rw [hfuel]
                have hleftIndex : index < left.length := by
                  simpa only [hleftLength] using hleftSide
                have hrecursive :=
                  inductionHypothesis left.length hleftLt left index
                    hleftIndex rfl
                omega
              · have hfuel :
                    balancedLookupLoopFuel values index =
                      15 + 3 * right.length + 4 * left.length +
                        balancedLookupLoopFuel right
                          (index - left.length) := by
                  rw [balancedLookupLoopFuel.eq_def]
                  simp only [values, leftLength, left, right]
                  rw [if_neg hleftSide]
                  rw [hleftLength]
                rw [hfuel]
                have hrightIndex :
                    index - left.length < right.length := by
                  rw [hleftLength]
                  omega
                have hrecursive :=
                  inductionHypothesis right.length hrightLt right
                    (index - left.length) hrightIndex rfl
                omega

/-- Public lookup fuel is bounded by one fixed linear polynomial. -/
theorem balancedLookupFuel_le
    (values : List ℕ) (index : ℕ)
    (hindex : index < values.length) :
    balancedLookupFuel values index ≤ 27 * (values.length + 1) := by
  unfold balancedLookupFuel
  have := balancedLookupLoopFuel_le values index hindex
  omega

/-- Any numeric subterm of the packed request fits the canonical width
budget.  Composed stages can reuse this lemma instead of restating pairing
arithmetic for every register. -/
theorem balancedLookupMaximumBits_covers
    (values : List ℕ) (index candidate : ℕ)
    (hcandidate : candidate ≤ balancedLookupInput values index) :
    natBitLength candidate ≤ balancedLookupMaximumBits values index :=
  PolynomialClock.natBitLength_mono hcandidate

end NearCubicWires.CanonicalBalancedLookupProgram
