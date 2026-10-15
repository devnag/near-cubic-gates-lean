import Proof.Foundations.CanonicalBinary
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.PolynomialClock
import Proof.Foundations.VerifiedLinker

/-!
# Fixed register-machine primitives for canonical binary syntax

This module contains the interpreter lemmas shared by executable codecs and the
fixed exact test for constructor tag one.  Variable-length public data is the
balanced syntax from `CanonicalBalanced`; the former linked-list validator was
removed rather than retained as a second wire format.
-/

namespace NearCubicWires.CanonicalBinaryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Exact constructor-tag primitive -/

/-- Fixed implementation of `IsOneCode`.  The program uses the finite pairing
signature proved in `CanonicalBinary.isOneCode_iff`; it never approximates
equality with a bounded traversal. -/
def oneCodeProgram : NPOracleProgram :=
  [ .branchZero 0 6 1
  , .unpairLeft 0 2 2
  , .branchZero 2 3 6
  , .increment 0 4
  , .unpairRight 0 2 5
  , .branchZero 2 7 6
  , .set 0 0 8
  , .set 0 1 8
  , .halt 0
  ]

@[simp] theorem oneCodeProgram_oracleFree :
    OracleFree oneCodeProgram := by
  rfl

def oneCodeOutput (code : ℕ) : ℕ :=
  if code = 1 then 1 else 0

theorem oneCodeOutput_le_one (code : ℕ) :
    oneCodeOutput code ≤ 1 := by
  unfold oneCodeOutput
  split <;> omega

private theorem boundedWrite_eq
    {state : NPOracleState} {maximumBits register value : ℕ}
    (hbits : natBitLength value ≤ maximumBits) :
    state.boundedWrite maximumBits register value =
      some (state.write register value) := by
  simp [NPOracleState.boundedWrite, hbits]

/-! ## Reusable exact interpreter steps -/

theorem run_branchZero_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc register zeroTarget nonzeroTarget : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? =
      some (.branchZero register zeroTarget nonzeroTarget))
    (hpc : state.pc = pc) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        (state.jump (if state.registers register = 0 then
          zeroTarget else nonzeroTarget)) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]

theorem run_sat_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc queryRegister destination next query : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? =
      some (.sat queryRegister destination next))
    (hpc : state.pc = pc)
    (hquery : state.registers queryRegister = query)
    (hqueryBits : natBitLength query ≤ maximumBits)
    (hresultBits :
      natBitLength (encodedSat query).toNat ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination (encodedSat query).toNat).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hquery, if_pos hqueryBits, boundedWrite_eq hresultBits]

theorem run_set_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc register value next : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.set register value next))
    (hpc : state.pc = pc)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write register value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [boundedWrite_eq hbits]

theorem run_copy_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.copy source destination next))
    (hpc : state.pc = pc)
    (hvalue : state.registers source = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_increment_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc register next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.increment register next))
    (hpc : state.pc = pc)
    (hvalue : state.registers register + 1 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write register value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem decrement_bits_le (value : ℕ) :
    natBitLength value.pred ≤ natBitLength value :=
  natBitLength_mono value.pred_le

theorem run_decrement_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc register next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.decrement register next))
    (hpc : state.pc = pc)
    (hvalue : Nat.pred (state.registers register) = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write register value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem add_bits_le (left right : ℕ) :
    natBitLength (left + right) ≤
      max (natBitLength left) (natBitLength right) + 1 := by
  let width := max (natBitLength left) (natBitLength right)
  have hleft :
      left < 2 ^ width := by
    apply lt_of_lt_of_le
    · simpa [natBitLength] using
        (Nat.lt_pow_succ_log_self (b := 2) (by omega) left)
    · exact Nat.pow_le_pow_right (by omega)
        (show natBitLength left ≤ width by
          exact le_max_left _ _)
  have hright :
      right < 2 ^ width := by
    apply lt_of_lt_of_le
    · simpa [natBitLength] using
        (Nat.lt_pow_succ_log_self (b := 2) (by omega) right)
    · exact Nat.pow_le_pow_right (by omega)
        (show natBitLength right ≤ width by
          exact le_max_right _ _)
  have hsum :
      left + right < 2 ^ (width + 1) := by
    calc
      left + right < 2 ^ width + 2 ^ width :=
        Nat.add_lt_add hleft hright
      _ = 2 ^ (width + 1) := by
        rw [Nat.pow_succ]
        omega
  by_cases hzero : left + right = 0
  · simp [hzero, natBitLength]
  · have hlog :
        Nat.log 2 (left + right) < width + 1 :=
      Nat.log_lt_of_lt_pow hzero hsum
    change Nat.log 2 (left + right) + 1 ≤ width + 1
    omega

theorem subtract_bits_le (left right : ℕ) :
    natBitLength (left - right) ≤ natBitLength left :=
  natBitLength_mono (Nat.sub_le left right)

theorem shiftLeft_bits_le_add (value amount : ℕ) :
    natBitLength (Nat.shiftLeft value amount) ≤
      natBitLength value + amount := by
  by_cases hzero : value = 0
  · subst value
    simp [natBitLength]
  · have hvalue :
        value < 2 ^ natBitLength value := by
      simpa [natBitLength] using
        (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)
    have hshift :
        Nat.shiftLeft value amount <
          2 ^ (natBitLength value + amount) := by
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hvalue (pow_pos (by omega) amount)
    have hshiftNonzero : Nat.shiftLeft value amount ≠ 0 := by
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
      exact Nat.mul_ne_zero hzero (pow_ne_zero amount (by omega))
    have hlog :
      Nat.log 2 (Nat.shiftLeft value amount) <
          natBitLength value + amount :=
      Nat.log_lt_of_lt_pow hshiftNonzero hshift
    change
      Nat.log 2 (Nat.shiftLeft value amount) + 1 ≤
        natBitLength value + amount
    omega

theorem run_add_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc left right destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.add left right destination next))
    (hpc : state.pc = pc)
    (hvalue : state.registers left + state.registers right = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_subtract_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc left right destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.subtract left right destination next))
    (hpc : state.pc = pc)
    (hvalue : state.registers left - state.registers right = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_pair_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc left right destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? =
      some (.pair left right destination next))
    (hpc : state.pc = pc)
    (hvalue :
      Nat.pair (state.registers left) (state.registers right) = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_unpairLeft_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.unpairLeft source destination next))
    (hpc : state.pc = pc)
    (hvalue : (Nat.unpair (state.registers source)).1 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_unpairRight_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.unpairRight source destination next))
    (hpc : state.pc = pc)
    (hvalue : (Nat.unpair (state.registers source)).2 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_encodeNat_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source destination next value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.encodeNat source destination next))
    (hpc : state.pc = pc)
    (hvalue : state.registers source = value)
    (hbits :
      natBitLength (CanonicalBinary.encodeNat value) ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination (CanonicalBinary.encodeNat value)).jump
          next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem shiftRight_bits_le (value amount : ℕ) :
    natBitLength (Nat.shiftRight value amount) ≤ natBitLength value := by
  apply natBitLength_mono
  simpa only [Nat.shiftRight_eq'] using Nat.shiftRight_le value amount

theorem run_shiftRight_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source amount destination next value : ℕ}
    {state : NPOracleState}
    (hat :
      program[pc]? = some (.shiftRight source amount destination next))
    (hpc : state.pc = pc)
    (hvalue : Nat.shiftRight (state.registers source) amount = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_shiftLeft_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source amount destination next value : ℕ}
    {state : NPOracleState}
    (hat :
      program[pc]? = some (.shiftLeft source amount destination next))
    (hpc : state.pc = pc)
    (hvalue : Nat.shiftLeft (state.registers source) amount = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_testBit_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc source index destination next value : ℕ}
    {state : NPOracleState}
    (hat :
      program[pc]? = some (.testBit source index destination next))
    (hpc : state.pc = pc)
    (hvalue :
      ((state.registers source).testBit
        (state.registers index)).toNat = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      runNPOracleProgram program maximumBits fuel
        ((state.write destination value).jump next) := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

theorem run_halt_instruction
    {program : NPOracleProgram}
    {maximumBits fuel pc outputRegister value : ℕ}
    {state : NPOracleState}
    (hat : program[pc]? = some (.halt outputRegister))
    (hpc : state.pc = pc)
    (hvalue : state.registers outputRegister = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram program maximumBits (fuel + 1) state =
      some value := by
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue]
  simp [hbits]

/-! ## Shared balanced-tree transducer ABI -/

/-- A shape-preserving transducer visits the right subtree after completing
the left subtree, then rebuilds their shared canonical branch.  These frames
are internal machine control, not an alternate public sequence encoding. -/
inductive BalancedTraversalFrame where
  | visitRight (rightCode : ℕ)
  | combineLeft (leftOutput : ℕ)
  deriving DecidableEq, Repr

/-- A frame is a fixed pair, so its constructor tag is directly branchable by
the weak machine.  The surrounding stack has logarithmic depth on a canonical
balanced input, so the linked control stack remains polynomial width even
though public variable-length data must not use linked lists. -/
def encodeBalancedTraversalFrame : BalancedTraversalFrame → ℕ
  | .visitRight rightCode =>
      Nat.pair 0 rightCode
  | .combineLeft leftOutput =>
      Nat.pair 1 leftOutput

def decodeBalancedTraversalFrame (code : ℕ) :
    Option BalancedTraversalFrame :=
  let fields := Nat.unpair code
  if fields.1 = 0 then
    some (.visitRight fields.2)
  else if fields.1 = 1 then
    some (.combineLeft fields.2)
  else
    none

@[simp] theorem decode_encodeBalancedTraversalFrame
    (frame : BalancedTraversalFrame) :
    decodeBalancedTraversalFrame (encodeBalancedTraversalFrame frame) =
      some frame := by
  cases frame <;> simp [encodeBalancedTraversalFrame,
    decodeBalancedTraversalFrame]

/-- Control stacks are bounded by tree height, not by leaf count.  Keeping the
encoding private to machine state avoids a second externally accepted codec. -/
def encodeBalancedTraversalStack
    (frames : List BalancedTraversalFrame) : ℕ :=
  encodeTaggedList (frames.map encodeBalancedTraversalFrame)

def decodeBalancedTraversalFrames :
    List ℕ → Option (List BalancedTraversalFrame)
  | [] => some []
  | code :: codes => do
      let frame ← decodeBalancedTraversalFrame code
      let frames ← decodeBalancedTraversalFrames codes
      pure (frame :: frames)

def decodeBalancedTraversalStack (code : ℕ) :
    Option (List BalancedTraversalFrame) := do
  let codes ← decodeTaggedList code
  decodeBalancedTraversalFrames codes

@[simp] theorem decodeBalancedTraversalFrames_map
    (frames : List BalancedTraversalFrame) :
    decodeBalancedTraversalFrames
        (frames.map encodeBalancedTraversalFrame) =
      some frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp [decodeBalancedTraversalFrames, ih]

@[simp] theorem decode_encodeBalancedTraversalStack
    (frames : List BalancedTraversalFrame) :
    decodeBalancedTraversalStack (encodeBalancedTraversalStack frames) =
      some frames := by
  simp [decodeBalancedTraversalStack, encodeBalancedTraversalStack]

def balancedVisitRightFrameCode (rightCode : ℕ) : ℕ :=
  encodeBalancedTraversalFrame (.visitRight rightCode)

def balancedCombineLeftFrameCode (leftOutput : ℕ) : ℕ :=
  encodeBalancedTraversalFrame (.combineLeft leftOutput)

theorem encodeBalancedTraversalStack_cons
    (frame : BalancedTraversalFrame)
    (frames : List BalancedTraversalFrame) :
    encodeBalancedTraversalStack (frame :: frames) =
      Nat.pair 1
        (Nat.pair (encodeBalancedTraversalFrame frame)
          (encodeBalancedTraversalStack frames)) := by
  rfl

/-- Width ledger for the internal control stack.  The exponential factor is
in continuation depth, which is logarithmic for midpoint-balanced public
trees; it is never charged in the number of public leaves. -/
def taggedControlAtomBits (values : List ℕ) : ℕ :=
  (values.map natBitLength).sum + 1

theorem taggedControlStackBits_le (values : List ℕ) :
    natBitLength (encodeTaggedList values) ≤
      4 ^ values.length * taggedControlAtomBits values := by
  induction values with
  | nil =>
      norm_num [encodeTaggedList, taggedControlAtomBits, natBitLength]
  | cons value values ih =>
      have hinner := pairCodeBits_le value (encodeTaggedList values)
      have houter := pairCodeBits_le 1
        (Nat.pair value (encodeTaggedList values))
      simp only [encodeTaggedList, List.length_cons, pow_succ]
      unfold taggedControlAtomBits at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      calc
        natBitLength
            (Nat.pair 1 (Nat.pair value (encodeTaggedList values))) ≤
            2 * max (natBitLength 1)
              (natBitLength
                (Nat.pair value (encodeTaggedList values))) := houter
        _ ≤ 4 * max (natBitLength value)
              (natBitLength (encodeTaggedList values)) := by
            have hone : natBitLength 1 ≤
                max (natBitLength value)
                  (natBitLength (encodeTaggedList values)) := by
              have hpositive : 1 ≤ natBitLength value := by
                unfold natBitLength
                omega
              norm_num [natBitLength]
            have hinner' :
                natBitLength
                    (Nat.pair value (encodeTaggedList values)) ≤
                  2 * max (natBitLength value)
                    (natBitLength (encodeTaggedList values)) := hinner
            omega
        _ ≤ 4 *
              (4 ^ values.length *
                ((values.map natBitLength).sum + 1) +
                natBitLength value) := by
            apply Nat.mul_le_mul_left
            apply max_le
            · omega
            · omega
        _ ≤ 4 * 4 ^ values.length *
              (natBitLength value +
                (values.map natBitLength).sum + 1) := by
            have hp : 1 ≤ 4 ^ values.length :=
              Nat.one_le_pow values.length 4 (by omega)
            nlinarith
        _ = 4 ^ values.length * 4 *
              (natBitLength value +
                (values.map natBitLength).sum + 1) := by
            ring

def balancedTraversalStackAtomBits
    (frames : List BalancedTraversalFrame) : ℕ :=
  taggedControlAtomBits (frames.map encodeBalancedTraversalFrame)

theorem balancedTraversalStackBits_le
    (frames : List BalancedTraversalFrame) :
    natBitLength (encodeBalancedTraversalStack frames) ≤
      4 ^ frames.length * balancedTraversalStackAtomBits frames := by
  simpa [encodeBalancedTraversalStack, balancedTraversalStackAtomBits] using
    taggedControlStackBits_le
      (frames.map encodeBalancedTraversalFrame)

private theorem two_pow_clog_le (length : ℕ) :
    2 ^ Nat.clog 2 length ≤ 2 * (length + 1) := by
  by_cases hsmall : length ≤ 1
  · have hclog : Nat.clog 2 length = 0 :=
      Nat.clog_of_right_le_one hsmall 2
    simp [hclog]
    omega
  · have hlarge : 1 < length := by omega
    have hpred :=
      Nat.pow_pred_clog_lt_self (b := 2) (by omega) hlarge
    have hpositive : 0 < Nat.clog 2 length :=
      Nat.clog_pos (by omega) hlarge
    have heq :
        (Nat.clog 2 length).pred + 1 = Nat.clog 2 length := by
      exact Nat.succ_pred_eq_of_pos hpositive
    rw [← heq, pow_succ]
    nlinarith

private theorem four_pow_clog_succ_le (length : ℕ) :
    4 ^ (Nat.clog 2 length + 1) ≤ 16 * (length + 1) ^ 2 := by
  have htwo := two_pow_clog_le length
  have hidentity :
      4 ^ Nat.clog 2 length =
        (2 ^ Nat.clog 2 length) ^ 2 := by
    calc
      4 ^ Nat.clog 2 length =
          (2 ^ 2) ^ Nat.clog 2 length := by norm_num
      _ = 2 ^ (2 * Nat.clog 2 length) := by rw [pow_mul]
      _ = 2 ^ (Nat.clog 2 length * 2) := by rw [mul_comm]
      _ = (2 ^ Nat.clog 2 length) ^ 2 := by rw [pow_mul]
  calc
    4 ^ (Nat.clog 2 length + 1) =
        4 ^ Nat.clog 2 length * 4 := by rw [pow_succ]
    _ = (2 ^ Nat.clog 2 length) ^ 2 * 4 := by rw [hidentity]
    _ ≤ (2 * (length + 1)) ^ 2 * 4 :=
      Nat.mul_le_mul_right 4 (Nat.pow_le_pow_left htwo 2)
    _ = 16 * (length + 1) ^ 2 := by ring

/-- Reusable controller resource invariant.  Any concrete handler only needs
to show that its live continuation count is bounded by the source tree height;
the actual stack register is then quadratic in leaf count, times the explicit
sum of frame widths. -/
theorem balancedTraversalStackBits_polynomial
    (frames : List BalancedTraversalFrame) (values : List ℕ)
    (hdepth : frames.length ≤ balancedListHeight values) :
    natBitLength (encodeBalancedTraversalStack frames) ≤
      16 * (values.length + 1) ^ 2 *
        balancedTraversalStackAtomBits frames := by
  have hheight := balancedListHeight_le_clog values
  have hstack := balancedTraversalStackBits_le frames
  have hpow :
      4 ^ frames.length ≤ 4 ^ (Nat.clog 2 values.length + 1) :=
    Nat.pow_le_pow_right (by omega) (hdepth.trans hheight)
  have hclog := four_pow_clog_succ_le values.length
  nlinarith [Nat.mul_le_mul_right
    (balancedTraversalStackAtomBits frames) hpow]

/-- The sole public sequence constructor used when a consumer finishes a
shape-preserving branch. -/
def balancedBranchCode (left right : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair left right)

@[simp] theorem balancedBranchCode_unpair (left right : ℕ) :
    Nat.unpair (balancedBranchCode left right) =
      (2, Nat.pair left right) := by
  simp [balancedBranchCode]

/-! ## Fixed shape-preserving controller -/

/-- Register convention shared by every balanced leaf transducer.

* `r0`: current subtree while descending, completed subtree while resuming;
* `r2`: internal continuation stack;
* `r3`: leaf atom passed to and returned by the concrete leaf handler;
* `r4`–`r8`: controller scratch;
* `r9+`: persistent consumer state.

The leaf handler is concrete code beginning at `leafPc`.  It must leave its
mapped atom in `r3` and jump to `balancedTraversalLeafReturnPc`.  When the root
has been rebuilt, the controller jumps to `donePc` with its canonical code in
`r0`.  Thus there is one structural controller but no runtime callback or
second public wire format. -/
def balancedTraversalLeafReturnPc : ℕ := 32

def balancedTraversalController
    (leafPc donePc : ℕ) : NPOracleProgram :=
  [ .branchZero 0 1 2
  , .set 0 0 15
  , .unpairLeft 0 4 3
  , .unpairLeft 4 5 4
  , .branchZero 5 5 7
  , .unpairRight 0 3 6
  , .copy 3 3 leafPc
  , .unpairRight 0 4 8
  , .unpairLeft 4 0 9
  , .unpairRight 4 5 10
  , .set 6 0 11
  , .pair 6 5 7 12
  , .pair 7 2 8 13
  , .set 6 1 14
  , .pair 6 8 2 0
  , .branchZero 2 donePc 16
  , .unpairRight 2 8 17
  , .unpairLeft 8 7 18
  , .unpairRight 8 2 19
  , .unpairLeft 7 6 20
  , .branchZero 6 21 28
  , .unpairRight 7 5 22
  , .set 6 1 23
  , .pair 6 0 7 24
  , .pair 7 2 8 25
  , .set 6 1 26
  , .pair 6 8 2 27
  , .copy 5 0 0
  , .unpairRight 7 5 29
  , .pair 5 0 4 30
  , .set 6 2 31
  , .pair 6 4 0 15
  , .set 6 1 33
  , .pair 6 3 0 15
  ]

@[simp] theorem balancedTraversalController_length
    (leafPc donePc : ℕ) :
    (balancedTraversalController leafPc donePc).length = 34 := by
  rfl

@[simp] theorem balancedTraversalController_oracleFree
    (leafPc donePc : ℕ) :
    OracleFree (balancedTraversalController leafPc donePc) := by
  rfl

theorem balancedTraversalController_leafEntry
    (leafPc donePc : ℕ) :
    (balancedTraversalController leafPc donePc)[6]? =
      some (.copy 3 3 leafPc) := by
  rfl

theorem balancedTraversalController_doneBranch
    (leafPc donePc : ℕ) :
    (balancedTraversalController leafPc donePc)[15]? =
      some (.branchZero 2 donePc 16) := by
  rfl

theorem balancedTraversalController_leafReturn :
    (balancedTraversalController 34 35)[balancedTraversalLeafReturnPc]? =
      some (.set 6 1 33) := by
  rfl

end NearCubicWires.CanonicalBinaryProgram
