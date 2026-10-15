import Proof.MachineModel.CanonicalTaggedNatListValidationProgram
import Proof.Circuits.RegisterBounds

/-!
# Canonical Boolean-node validation

Boolean nodes are the first nested witness object whose fields have semantic
relationships.  This module deliberately consumes the one shared tagged-Nat
validation pipeline: no second decoder is allowed to reinterpret public Nat
codes.  The fixed postprocessor below sees only presence-tagged native values
and emits one presence-tagged native node descriptor.
-/

namespace NearCubicWires.CanonicalBooleanNodeValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-- Internal value carried by the shared Nat validator.  This is not a public
decoder: callers can only reach it through `taggedNatListValidationProgram`. -/
private def validatedNatValue (output : ℕ) : Option ℕ :=
  if output = 0 then none else some (Nat.unpair output).2

/-- Native descriptor ABI:

* unary nodes are `pair tag payload` for tags `0`, `1`, and `2`;
* binary nodes are `pair tag (pair left right)` for tags `3` and `4`;
* the outer `pair 1 descriptor` records structural success, while zero rejects.

Input-index and child-topology bounds are intentionally checked by the single
circuit traversal, where the public arity and current node index are available.
-/
def booleanNodeStructuralDescriptor : List ℕ → ℕ
  | [tagOutput, payloadOutput] =>
      match validatedNatValue tagOutput, validatedNatValue payloadOutput with
      | some 0, some payload =>
          if payload = 0 ∨ payload = 1 then
            Nat.pair 1 (Nat.pair 0 payload)
          else
            0
      | some 1, some payload => Nat.pair 1 (Nat.pair 1 payload)
      | some 2, some payload => Nat.pair 1 (Nat.pair 2 payload)
      | _, _ => 0
  | [tagOutput, leftOutput, rightOutput] =>
      match validatedNatValue tagOutput, validatedNatValue leftOutput,
          validatedNatValue rightOutput with
      | some 3, some left, some right =>
          Nat.pair 1 (Nat.pair 3 (Nat.pair left right))
      | some 4, some left, some right =>
          Nat.pair 1 (Nat.pair 4 (Nat.pair left right))
      | _, _, _ => 0
  | _ => 0

def booleanNodeStructuralOutput (raw : ℕ) : ℕ :=
  booleanNodeStructuralDescriptor (taggedNatFieldOutputs raw)

@[simp] private theorem encodeTaggedList_cons_ne_zero
    (value : ℕ) (rest : List ℕ) :
    encodeTaggedList (value :: rest) ≠ 0 := by
  have hpositive :
      1 ≤ Nat.pair 1
        (Nat.pair value (encodeTaggedList rest)) :=
    Nat.left_le_pair 1 _
  simp only [encodeTaggedList]
  omega

@[simp] private theorem pair_one_ne_zero (value : ℕ) :
    Nat.pair 1 value ≠ 0 := by
  have hpositive : 1 ≤ Nat.pair 1 value :=
    Nat.left_le_pair 1 value
  omega

/-!
The postprocessor is private because its input is an internal, trusted ABI.  It
still has a total semantics for every canonical tagged list.  Registers:

* `r0`: tagged cursor, then output;
* `r2`: current presence-tagged field;
* `r3`, `r4`, `r5`: native tag/payload/right values;
* `r6`: tagged-cell payload and pair-construction scratch;
* `r7`: constructor dispatch scratch and the success bit.
-/
private def booleanNodeStructuralDescriptorProgram : NPOracleProgram :=
  [ .branchZero 0 43 1
  , .unpairRight 0 6 2
  , .unpairLeft 6 2 3
  , .unpairRight 6 0 4
  , .branchZero 2 43 5
  , .unpairRight 2 3 6
  , .branchZero 0 43 7
  , .unpairRight 0 6 8
  , .unpairLeft 6 2 9
  , .unpairRight 6 0 10
  , .branchZero 2 43 11
  , .unpairRight 2 4 12
  , .copy 3 7 13
  , .branchZero 7 22 14
  , .decrement 7 15
  , .branchZero 7 27 16
  , .decrement 7 17
  , .branchZero 7 27 18
  , .decrement 7 19
  , .branchZero 7 28 20
  , .decrement 7 21
  , .branchZero 7 28 43
  , .branchZero 0 23 43
  , .copy 4 7 24
  , .branchZero 7 35 25
  , .decrement 7 26
  , .branchZero 7 35 43
  , .branchZero 0 35 43
  , .branchZero 0 43 29
  , .unpairRight 0 6 30
  , .unpairLeft 6 2 31
  , .unpairRight 6 0 32
  , .branchZero 2 43 33
  , .unpairRight 2 5 34
  , .branchZero 0 39 43
  , .pair 3 4 6 36
  , .set 7 1 37
  , .pair 7 6 0 38
  , .halt 0
  , .pair 4 5 6 40
  , .pair 3 6 6 41
  , .set 7 1 42
  , .pair 7 6 0 38
  , .set 0 0 38
  ]

private theorem booleanNodeStructuralDescriptorProgram_oracleFree :
    OracleFree booleanNodeStructuralDescriptorProgram := by
  rfl

private def booleanNodeStructuralDescriptorFuel : ℕ := 44

private def booleanNodeStructuralDescriptorBits
    (inputLength input : ℕ) : ℕ :=
  natBitLength <|
    pairIter 3 (max 1 (max inputLength input))

private theorem run_booleanNodeStructuralReject
    (maximumBits fuel : ℕ) (state : NPOracleState)
    (hpc : state.pc = 43)
    (hzeroBits : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
        (fuel + 2) state =
      some 0 := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_set_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 1)
    (pc := 43) (register := 0) (value := 0) (next := 38)
    (by rfl) hpc hzeroBits]
  exact run_halt_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel)
    (pc := 38) (outputRegister := 0) (value := 0)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    hzeroBits

private theorem run_booleanNodeStructuralUnary
    (maximumBits fuel tag payload : ℕ) (state : NPOracleState)
    (hpc : state.pc = 35)
    (htag : state.registers 3 = tag)
    (hpayload : state.registers 4 = payload)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hdescriptorBits :
      natBitLength (Nat.pair tag payload) ≤ maximumBits)
    (houtputBits :
      natBitLength (Nat.pair 1 (Nat.pair tag payload)) ≤
        maximumBits) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
        (fuel + 4) state =
      some (Nat.pair 1 (Nat.pair tag payload)) := by
  let descriptor := Nat.pair tag payload
  let output := Nat.pair 1 descriptor
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [run_pair_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 3)
    (pc := 35) (left := 3) (right := 4)
    (destination := 6) (next := 36) (value := descriptor)
    (by rfl) hpc
    (by simp [descriptor, htag, hpayload]) hdescriptorBits]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [run_set_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 2)
    (pc := 36) (register := 7) (value := 1) (next := 37)
    (by rfl) (by rfl) honeBits]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 1)
    (pc := 37) (left := 7) (right := 6)
    (destination := 0) (next := 38) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      descriptor])
    houtputBits]
  exact run_halt_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel)
    (pc := 38) (outputRegister := 0) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private theorem run_booleanNodeStructuralBinary
    (maximumBits fuel tag left right : ℕ) (state : NPOracleState)
    (hpc : state.pc = 39)
    (htag : state.registers 3 = tag)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hchildrenBits :
      natBitLength (Nat.pair left right) ≤ maximumBits)
    (hdescriptorBits :
      natBitLength (Nat.pair tag (Nat.pair left right)) ≤
        maximumBits)
    (houtputBits :
      natBitLength
          (Nat.pair 1 (Nat.pair tag (Nat.pair left right))) ≤
        maximumBits) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
        (fuel + 5) state =
      some (Nat.pair 1 (Nat.pair tag (Nat.pair left right))) := by
  let children := Nat.pair left right
  let descriptor := Nat.pair tag children
  let output := Nat.pair 1 descriptor
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [run_pair_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 4)
    (pc := 39) (left := 4) (right := 5)
    (destination := 6) (next := 40) (value := children)
    (by rfl) hpc
    (by simp [children, hleft, hright]) hchildrenBits]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [run_pair_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 3)
    (pc := 40) (left := 3) (right := 6)
    (destination := 6) (next := 41) (value := descriptor)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptor, children, htag])
    hdescriptorBits]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [run_set_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 2)
    (pc := 41) (register := 7) (value := 1) (next := 42)
    (by rfl) (by rfl) honeBits]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 1)
    (pc := 42) (left := 7) (right := 6)
    (destination := 0) (next := 38) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      descriptor])
    houtputBits]
  exact run_halt_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel)
    (pc := 38) (outputRegister := 0) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private def booleanNodeBinaryTailOutput
    (tag left third : ℕ) (tail : List ℕ) : ℕ :=
  if third = 0 then
    0
  else if tail = [] then
    Nat.pair 1 (Nat.pair tag (Nat.pair left (Nat.unpair third).2))
  else
    0

private theorem run_booleanNodeStructuralBinaryTail
    (maximumBits fuel tag left third : ℕ) (tail : List ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 28)
    (hcursor :
      state.registers 0 = encodeTaggedList (third :: tail))
    (htag : state.registers 3 = tag)
    (hleft : state.registers 4 = left)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hcellPayloadBits :
      natBitLength (Nat.pair third (encodeTaggedList tail)) ≤
        maximumBits)
    (hthirdBits : natBitLength third ≤ maximumBits)
    (htailBits :
      natBitLength (encodeTaggedList tail) ≤ maximumBits)
    (hrightBits :
      natBitLength (Nat.unpair third).2 ≤ maximumBits)
    (hchildrenBits :
      natBitLength (Nat.pair left (Nat.unpair third).2) ≤
        maximumBits)
    (hdescriptorBits :
      natBitLength
          (Nat.pair tag (Nat.pair left (Nat.unpair third).2)) ≤
        maximumBits)
    (houtputBits :
      natBitLength
          (Nat.pair 1
            (Nat.pair tag (Nat.pair left (Nat.unpair third).2))) ≤
        maximumBits) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
        (fuel + 12) state =
      some (booleanNodeBinaryTailOutput tag left third tail) := by
  rw [show fuel + 12 = (fuel + 11) + 1 by omega]
  rw [run_branchZero_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 11)
    (pc := 28) (register := 0) (zeroTarget := 43)
    (nonzeroTarget := 29) (by rfl) hpc]
  rw [if_neg (by
    rw [hcursor]
    simp [encodeTaggedList])]
  rw [show fuel + 11 = (fuel + 10) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 10)
    (pc := 29) (source := 0) (destination := 6) (next := 30)
    (value := Nat.pair third (encodeTaggedList tail))
    (by rfl) (by rfl)
    (by simp [NPOracleState.jump, hcursor, encodeTaggedList])
    hcellPayloadBits]
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 9)
    (pc := 30) (source := 6) (destination := 2) (next := 31)
    (value := third) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    hthirdBits]
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 8)
    (pc := 31) (source := 6) (destination := 0) (next := 32)
    (value := encodeTaggedList tail) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [run_branchZero_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := fuel + 7)
    (pc := 32) (register := 2) (zeroTarget := 43)
    (nonzeroTarget := 33) (by rfl) (by rfl)]
  by_cases hthird : third = 0
  · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump,
      hthird])]
    rw [show booleanNodeBinaryTailOutput tag left third tail = 0 by
      simp [booleanNodeBinaryTailOutput, hthird]]
    exact run_booleanNodeStructuralReject maximumBits (fuel + 5) _
      (by rfl) hzeroBits
  · rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump,
      hthird])]
    rw [show fuel + 7 = (fuel + 6) + 1 by omega]
    rw [run_unpairRight_instruction
      (program := booleanNodeStructuralDescriptorProgram)
      (maximumBits := maximumBits) (fuel := fuel + 6)
      (pc := 33) (source := 2) (destination := 5) (next := 34)
      (value := (Nat.unpair third).2) (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump])
      hrightBits]
    rw [show fuel + 6 = (fuel + 5) + 1 by omega]
    rw [run_branchZero_instruction
      (program := booleanNodeStructuralDescriptorProgram)
      (maximumBits := maximumBits) (fuel := fuel + 5)
      (pc := 34) (register := 0) (zeroTarget := 39)
      (nonzeroTarget := 43) (by rfl) (by rfl)]
    cases tail with
    | nil =>
        rw [if_pos (by
          simp [NPOracleState.write, NPOracleState.jump,
            encodeTaggedList])]
        rw [show
          booleanNodeBinaryTailOutput tag left third [] =
              Nat.pair 1
                (Nat.pair tag (Nat.pair left (Nat.unpair third).2)) by
          simp [booleanNodeBinaryTailOutput, hthird]]
        apply run_booleanNodeStructuralBinary maximumBits fuel tag left
          (Nat.unpair third).2
        · rfl
        · simp [NPOracleState.write, NPOracleState.jump, htag]
        · simp [NPOracleState.write, NPOracleState.jump, hleft]
        · simp [NPOracleState.write, NPOracleState.jump]
        · exact honeBits
        · exact hchildrenBits
        · exact hdescriptorBits
        · exact houtputBits
    | cons next tail =>
        rw [if_neg (by
          simp [NPOracleState.write, NPOracleState.jump,
            encodeTaggedList])]
        rw [show
          booleanNodeBinaryTailOutput tag left third (next :: tail) = 0 by
          simp [booleanNodeBinaryTailOutput, hthird]]
        exact run_booleanNodeStructuralReject maximumBits (fuel + 3) _
          (by rfl) hzeroBits

private theorem run_booleanNodeStructuralSuffix
    (maximumBits base first second : ℕ) (rest : List ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 12)
    (hcursor : state.registers 0 = encodeTaggedList rest)
    (htag :
      state.registers 3 = (Nat.unpair first).2)
    (hpayload :
      state.registers 4 = (Nat.unpair second).2)
    (hfirst : first ≠ 0)
    (hsecond : second ≠ 0)
    (hbase : 1 ≤ base)
    (hfirstBound : first ≤ base)
    (hsecondBound : second ≤ base)
    (hrestBound : encodeTaggedList rest ≤ base)
    (hbits :
      natBitLength (pairIter 3 base) ≤ maximumBits) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
        32 state =
      some
        (booleanNodeStructuralDescriptor (first :: second :: rest)) := by
  generalize htagValue : (Nat.unpair first).2 = tag
  generalize hpayloadValue : (Nat.unpair second).2 = payload
  have hsmallBits :
      ∀ value, value ≤ base → natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact (natBitLength_mono
      (hvalue.trans (value_le_pairIter 3 base))).trans hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    hsmallBits 0 (Nat.zero_le _)
  have honeBits : natBitLength 1 ≤ maximumBits :=
    hsmallBits 1 hbase
  have htagBound : tag ≤ base := by
    rw [← htagValue]
    exact (Nat.unpair_right_le first).trans hfirstBound
  have hpayloadBound : payload ≤ base := by
    rw [← hpayloadValue]
    exact (Nat.unpair_right_le second).trans hsecondBound
  have htagBits := hsmallBits tag htagBound
  have hpayloadBits := hsmallBits payload hpayloadBound
  have hunaryDescriptorBits (constructor value : ℕ)
      (hconstructor : constructor ≤ base) (hvalue : value ≤ base) :
      natBitLength (Nat.pair constructor value) ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hbits
    exact (pair_mono hconstructor hvalue).trans
      (value_le_pairIter 2 (Nat.pair base base))
  have hunaryOutputBits (constructor value : ℕ)
      (hconstructor : constructor ≤ base) (hvalue : value ≤ base) :
      natBitLength (Nat.pair 1 (Nat.pair constructor value)) ≤
        maximumBits := by
    apply (natBitLength_mono ?_).trans hbits
    have hdescriptor :
        Nat.pair constructor value ≤ Nat.pair base base :=
      pair_mono hconstructor hvalue
    calc
      Nat.pair 1 (Nat.pair constructor value) ≤
          Nat.pair (Nat.pair base base) (Nat.pair base base) :=
        pair_mono
          (hbase.trans (Nat.left_le_pair base base))
          hdescriptor
      _ ≤ pairIter 3 base := by
        exact value_le_pairIter 1 _
  have hbinaryDescriptorBits (constructor left right : ℕ)
      (hconstructor : constructor ≤ base)
      (hleft : left ≤ base) (hright : right ≤ base) :
      natBitLength (Nat.pair constructor (Nat.pair left right)) ≤
        maximumBits := by
    apply (natBitLength_mono ?_).trans hbits
    have hchildren :
        Nat.pair left right ≤ Nat.pair base base :=
      pair_mono hleft hright
    calc
      Nat.pair constructor (Nat.pair left right) ≤
          Nat.pair (Nat.pair base base) (Nat.pair base base) :=
        pair_mono
          (hconstructor.trans (Nat.left_le_pair base base))
          hchildren
      _ ≤ pairIter 3 base := value_le_pairIter 1 _
  have hbinaryOutputBits (constructor left right : ℕ)
      (hconstructor : constructor ≤ base)
      (hleft : left ≤ base) (hright : right ≤ base) :
      natBitLength
          (Nat.pair 1 (Nat.pair constructor (Nat.pair left right))) ≤
        maximumBits := by
    apply (natBitLength_mono ?_).trans hbits
    have hchildren :
        Nat.pair left right ≤ Nat.pair base base :=
      pair_mono hleft hright
    have hdescriptor :
        Nat.pair constructor (Nat.pair left right) ≤
          Nat.pair (Nat.pair base base) (Nat.pair base base) :=
      pair_mono
        (hconstructor.trans (Nat.left_le_pair base base))
        hchildren
    exact pair_mono
      (hbase.trans <| Nat.left_le_pair base base |>.trans <|
        Nat.left_le_pair (Nat.pair base base) (Nat.pair base base))
      hdescriptor
  rw [show (32 : ℕ) = 31 + 1 by omega]
  rw [run_copy_instruction
    (program := booleanNodeStructuralDescriptorProgram)
    (maximumBits := maximumBits) (fuel := 31)
    (pc := 12) (source := 3) (destination := 7) (next := 13)
    (value := tag) (by rfl) hpc
    (by simpa [htagValue] using htag) htagBits]
  cases tag with
  | zero =>
      rw [show (31 : ℕ) = 30 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeStructuralDescriptorProgram)
        (maximumBits := maximumBits) (fuel := 30)
        (pc := 13) (register := 7) (zeroTarget := 22)
        (nonzeroTarget := 14) (by rfl) (by rfl)]
      rw [if_pos (by simp)]
      cases rest with
      | nil =>
          rw [show (30 : ℕ) = 29 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 29)
            (pc := 22) (register := 0) (zeroTarget := 23)
            (nonzeroTarget := 43) (by rfl) (by rfl)]
          rw [if_pos (by simp [NPOracleState.write,
            NPOracleState.jump, hcursor, encodeTaggedList])]
          rw [show (29 : ℕ) = 28 + 1 by omega]
          rw [run_copy_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 28)
            (pc := 23) (source := 4) (destination := 7) (next := 24)
            (value := payload) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump,
              hpayload, hpayloadValue])
            hpayloadBits]
          rw [show (28 : ℕ) = 27 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 27)
            (pc := 24) (register := 7) (zeroTarget := 35)
            (nonzeroTarget := 25) (by rfl) (by rfl)]
          cases payload with
          | zero =>
              rw [if_pos (by simp)]
              rw [show
                booleanNodeStructuralDescriptor [first, second] =
                    Nat.pair 1 (Nat.pair 0 0) by
                simp [booleanNodeStructuralDescriptor,
                  validatedNatValue, hfirst, hsecond,
                  htagValue, hpayloadValue]]
              apply run_booleanNodeStructuralUnary maximumBits 23 0 0
              · rfl
              · simp [NPOracleState.write, NPOracleState.jump,
                  htag, htagValue]
              · simp [NPOracleState.write, NPOracleState.jump,
                  hpayload, hpayloadValue]
              · exact honeBits
              · exact hunaryDescriptorBits 0 0
                  (Nat.zero_le _) (Nat.zero_le _)
              · exact hunaryOutputBits 0 0
                  (Nat.zero_le _) (Nat.zero_le _)
          | succ payload =>
              rw [if_neg (by simp)]
              rw [show (27 : ℕ) = 26 + 1 by omega]
              rw [run_decrement_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 26)
                (pc := 25) (register := 7) (next := 26)
                (value := payload) (by rfl) (by rfl)
                (by simp [NPOracleState.write, NPOracleState.jump])
                (hsmallBits payload (by omega))]
              rw [show (26 : ℕ) = 25 + 1 by omega]
              rw [run_branchZero_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 25)
                (pc := 26) (register := 7) (zeroTarget := 35)
                (nonzeroTarget := 43) (by rfl) (by rfl)]
              cases payload with
              | zero =>
                  rw [if_pos (by simp)]
                  rw [show
                    booleanNodeStructuralDescriptor [first, second] =
                        Nat.pair 1 (Nat.pair 0 1) by
                    simp [booleanNodeStructuralDescriptor,
                      validatedNatValue, hfirst, hsecond,
                      htagValue, hpayloadValue]]
                  apply run_booleanNodeStructuralUnary maximumBits 21 0 1
                  · rfl
                  · simp [NPOracleState.write, NPOracleState.jump,
                      htag, htagValue]
                  · simp [NPOracleState.write, NPOracleState.jump,
                      hpayload, hpayloadValue]
                  · exact honeBits
                  · exact hunaryDescriptorBits 0 1
                      (Nat.zero_le _) hbase
                  · exact hunaryOutputBits 0 1
                      (Nat.zero_le _) hbase
              | succ payload =>
                  rw [if_neg (by simp)]
                  rw [show
                    booleanNodeStructuralDescriptor [first, second] = 0 by
                    simp [booleanNodeStructuralDescriptor,
                      validatedNatValue, hfirst, hsecond,
                      htagValue, hpayloadValue]]
                  apply run_booleanNodeStructuralReject maximumBits 23
                  · rfl
                  · exact hzeroBits
      | cons third tail =>
          rw [show (30 : ℕ) = 29 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 29)
            (pc := 22) (register := 0) (zeroTarget := 23)
            (nonzeroTarget := 43) (by rfl) (by rfl)]
          rw [if_neg (by
            simp [NPOracleState.write, NPOracleState.jump, hcursor,
              encodeTaggedList])]
          have houtput :
              booleanNodeStructuralDescriptor
                  (first :: second :: third :: tail) = 0 := by
            cases tail <;>
              simp [booleanNodeStructuralDescriptor,
                validatedNatValue, hfirst, hsecond,
                htagValue, hpayloadValue]
          rw [houtput]
          apply run_booleanNodeStructuralReject maximumBits 27
          · rfl
          · exact hzeroBits
  | succ tag =>
      rw [show (31 : ℕ) = 30 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeStructuralDescriptorProgram)
        (maximumBits := maximumBits) (fuel := 30)
        (pc := 13) (register := 7) (zeroTarget := 22)
        (nonzeroTarget := 14) (by rfl) (by rfl)]
      rw [if_neg (by simp)]
      rw [show (30 : ℕ) = 29 + 1 by omega]
      rw [run_decrement_instruction
        (program := booleanNodeStructuralDescriptorProgram)
        (maximumBits := maximumBits) (fuel := 29)
        (pc := 14) (register := 7) (next := 15)
        (value := tag) (by rfl) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump])
        (hsmallBits tag (by omega))]
      rw [show (29 : ℕ) = 28 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeStructuralDescriptorProgram)
        (maximumBits := maximumBits) (fuel := 28)
        (pc := 15) (register := 7) (zeroTarget := 27)
        (nonzeroTarget := 16) (by rfl) (by rfl)]
      cases tag with
      | zero =>
          rw [if_pos (by simp)]
          cases rest with
          | nil =>
              rw [show (28 : ℕ) = 27 + 1 by omega]
              rw [run_branchZero_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 27)
                (pc := 27) (register := 0) (zeroTarget := 35)
                (nonzeroTarget := 43) (by rfl) (by rfl)]
              rw [if_pos (by
                simp [NPOracleState.write, NPOracleState.jump, hcursor,
                  encodeTaggedList])]
              rw [show
                booleanNodeStructuralDescriptor [first, second] =
                    Nat.pair 1 (Nat.pair 1 payload) by
                simp [booleanNodeStructuralDescriptor,
                  validatedNatValue, hfirst, hsecond,
                  htagValue, hpayloadValue]]
              apply run_booleanNodeStructuralUnary
                maximumBits 23 1 payload
              · rfl
              · simp [NPOracleState.write, NPOracleState.jump,
                  htag, htagValue]
              · simp [NPOracleState.write, NPOracleState.jump,
                  hpayload, hpayloadValue]
              · exact honeBits
              · exact hunaryDescriptorBits 1 payload hbase hpayloadBound
              · exact hunaryOutputBits 1 payload hbase hpayloadBound
          | cons third tail =>
              rw [show (28 : ℕ) = 27 + 1 by omega]
              rw [run_branchZero_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 27)
                (pc := 27) (register := 0) (zeroTarget := 35)
                (nonzeroTarget := 43) (by rfl) (by rfl)]
              rw [if_neg (by
                simp [NPOracleState.write, NPOracleState.jump, hcursor,
                  encodeTaggedList])]
              have houtput :
                  booleanNodeStructuralDescriptor
                      (first :: second :: third :: tail) = 0 := by
                cases tail <;>
                  simp [booleanNodeStructuralDescriptor,
                    validatedNatValue, hfirst, hsecond,
                    htagValue, hpayloadValue]
              rw [houtput]
              apply run_booleanNodeStructuralReject maximumBits 25
              · rfl
              · exact hzeroBits
      | succ tag =>
          rw [if_neg (by simp)]
          rw [show (28 : ℕ) = 27 + 1 by omega]
          rw [run_decrement_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 27)
            (pc := 16) (register := 7) (next := 17)
            (value := tag) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            (hsmallBits tag (by omega))]
          rw [show (27 : ℕ) = 26 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 26)
            (pc := 17) (register := 7) (zeroTarget := 27)
            (nonzeroTarget := 18) (by rfl) (by rfl)]
          cases tag with
          | zero =>
              rw [if_pos (by simp)]
              cases rest with
              | nil =>
                  rw [show (26 : ℕ) = 25 + 1 by omega]
                  rw [run_branchZero_instruction
                    (program := booleanNodeStructuralDescriptorProgram)
                    (maximumBits := maximumBits) (fuel := 25)
                    (pc := 27) (register := 0) (zeroTarget := 35)
                    (nonzeroTarget := 43) (by rfl) (by rfl)]
                  rw [if_pos (by
                    simp [NPOracleState.write, NPOracleState.jump,
                      hcursor, encodeTaggedList])]
                  rw [show
                    booleanNodeStructuralDescriptor [first, second] =
                        Nat.pair 1 (Nat.pair 2 payload) by
                    simp [booleanNodeStructuralDescriptor,
                      validatedNatValue, hfirst, hsecond,
                      htagValue, hpayloadValue]]
                  apply run_booleanNodeStructuralUnary
                    maximumBits 21 2 payload
                  · rfl
                  · simp [NPOracleState.write, NPOracleState.jump,
                      htag, htagValue]
                  · simp [NPOracleState.write, NPOracleState.jump,
                      hpayload, hpayloadValue]
                  · exact honeBits
                  · exact hunaryDescriptorBits 2 payload
                      (by omega) hpayloadBound
                  · exact hunaryOutputBits 2 payload
                      (by omega) hpayloadBound
              | cons third tail =>
                  rw [show (26 : ℕ) = 25 + 1 by omega]
                  rw [run_branchZero_instruction
                    (program := booleanNodeStructuralDescriptorProgram)
                    (maximumBits := maximumBits) (fuel := 25)
                    (pc := 27) (register := 0) (zeroTarget := 35)
                    (nonzeroTarget := 43) (by rfl) (by rfl)]
                  rw [if_neg (by
                    simp [NPOracleState.write, NPOracleState.jump,
                      hcursor, encodeTaggedList])]
                  have houtput :
                      booleanNodeStructuralDescriptor
                          (first :: second :: third :: tail) = 0 := by
                    cases tail <;>
                      simp [booleanNodeStructuralDescriptor,
                        validatedNatValue, hfirst, hsecond,
                        htagValue, hpayloadValue]
                  rw [houtput]
                  apply run_booleanNodeStructuralReject maximumBits 23
                  · rfl
                  · exact hzeroBits
          | succ tag =>
              rw [if_neg (by simp)]
              rw [show (26 : ℕ) = 25 + 1 by omega]
              rw [run_decrement_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 25)
                (pc := 18) (register := 7) (next := 19)
                (value := tag) (by rfl) (by rfl)
                (by simp [NPOracleState.write, NPOracleState.jump])
                (hsmallBits tag (by omega))]
              rw [show (25 : ℕ) = 24 + 1 by omega]
              rw [run_branchZero_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 24)
                (pc := 19) (register := 7) (zeroTarget := 28)
                (nonzeroTarget := 20) (by rfl) (by rfl)]
              cases tag with
              | zero =>
                  rw [if_pos (by simp)]
                  -- Tags three and four share the exact third-field parser.
                  cases rest with
                  | nil =>
                      rw [show (24 : ℕ) = 23 + 1 by omega]
                      rw [run_branchZero_instruction
                        (program := booleanNodeStructuralDescriptorProgram)
                        (maximumBits := maximumBits) (fuel := 23)
                        (pc := 28) (register := 0) (zeroTarget := 43)
                        (nonzeroTarget := 29) (by rfl) (by rfl)]
                      rw [if_pos (by
                        simp [NPOracleState.write, NPOracleState.jump,
                          hcursor, encodeTaggedList])]
                      rw [show
                        booleanNodeStructuralDescriptor [first, second] =
                            0 by
                        simp [booleanNodeStructuralDescriptor,
                          validatedNatValue, hfirst, hsecond,
                          htagValue, hpayloadValue]]
                      apply run_booleanNodeStructuralReject maximumBits 21
                      · rfl
                      · exact hzeroBits
                  | cons third tail =>
                      have hcellPayloadBound :
                          Nat.pair third (encodeTaggedList tail) ≤ base :=
                        (Nat.right_le_pair 1 _).trans hrestBound
                      have hthirdBound : third ≤ base :=
                        (Nat.left_le_pair third
                          (encodeTaggedList tail)).trans hcellPayloadBound
                      have htailBound : encodeTaggedList tail ≤ base :=
                        (Nat.right_le_pair third
                          (encodeTaggedList tail)).trans hcellPayloadBound
                      have hrightBound : (Nat.unpair third).2 ≤ base :=
                        (Nat.unpair_right_le third).trans hthirdBound
                      rw [show
                        booleanNodeStructuralDescriptor
                            (first :: second :: third :: tail) =
                          booleanNodeBinaryTailOutput 3 payload third tail by
                        cases tail <;>
                          by_cases hthird : third = 0 <;>
                          simp [booleanNodeStructuralDescriptor,
                            booleanNodeBinaryTailOutput,
                            validatedNatValue, hfirst, hsecond,
                            htagValue, hpayloadValue, hthird]]
                      apply run_booleanNodeStructuralBinaryTail
                        maximumBits 12 3 payload third tail
                      · rfl
                      · simp [NPOracleState.write, NPOracleState.jump,
                          hcursor]
                      · simp [NPOracleState.write, NPOracleState.jump,
                          htag, htagValue]
                      · simp [NPOracleState.write, NPOracleState.jump,
                          hpayload, hpayloadValue]
                      · exact hzeroBits
                      · exact honeBits
                      · exact hsmallBits _ hcellPayloadBound
                      · exact hsmallBits _ hthirdBound
                      · exact hsmallBits _ htailBound
                      · exact hsmallBits _ hrightBound
                      · exact hunaryDescriptorBits payload
                          (Nat.unpair third).2
                          hpayloadBound hrightBound
                      · exact hbinaryDescriptorBits 3 payload
                          (Nat.unpair third).2
                          (by omega) hpayloadBound hrightBound
                      · exact hbinaryOutputBits 3 payload
                          (Nat.unpair third).2
                          (by omega) hpayloadBound hrightBound
              | succ tag =>
                  rw [if_neg (by simp)]
                  rw [show (24 : ℕ) = 23 + 1 by omega]
                  rw [run_decrement_instruction
                    (program := booleanNodeStructuralDescriptorProgram)
                    (maximumBits := maximumBits) (fuel := 23)
                    (pc := 20) (register := 7) (next := 21)
                    (value := tag) (by rfl) (by rfl)
                    (by simp [NPOracleState.write, NPOracleState.jump])
                    (hsmallBits tag (by omega))]
                  rw [show (23 : ℕ) = 22 + 1 by omega]
                  rw [run_branchZero_instruction
                    (program := booleanNodeStructuralDescriptorProgram)
                    (maximumBits := maximumBits) (fuel := 22)
                    (pc := 21) (register := 7) (zeroTarget := 28)
                    (nonzeroTarget := 43) (by rfl) (by rfl)]
                  cases tag with
                  | zero =>
                      rw [if_pos (by simp)]
                      cases rest with
                      | nil =>
                          rw [show (22 : ℕ) = 21 + 1 by omega]
                          rw [run_branchZero_instruction
                            (program :=
                              booleanNodeStructuralDescriptorProgram)
                            (maximumBits := maximumBits) (fuel := 21)
                            (pc := 28) (register := 0)
                            (zeroTarget := 43) (nonzeroTarget := 29)
                            (by rfl) (by rfl)]
                          rw [if_pos (by
                            simp [NPOracleState.write,
                              NPOracleState.jump, hcursor,
                              encodeTaggedList])]
                          rw [show
                            booleanNodeStructuralDescriptor
                                [first, second] = 0 by
                            simp [booleanNodeStructuralDescriptor,
                              validatedNatValue, hfirst, hsecond,
                              htagValue, hpayloadValue]]
                          apply run_booleanNodeStructuralReject
                            maximumBits 19
                          · rfl
                          · exact hzeroBits
                      | cons third tail =>
                          have hcellPayloadBound :
                              Nat.pair third (encodeTaggedList tail) ≤ base :=
                            (Nat.right_le_pair 1 _).trans hrestBound
                          have hthirdBound : third ≤ base :=
                            (Nat.left_le_pair third
                              (encodeTaggedList tail)).trans
                                hcellPayloadBound
                          have htailBound :
                              encodeTaggedList tail ≤ base :=
                            (Nat.right_le_pair third
                              (encodeTaggedList tail)).trans
                                hcellPayloadBound
                          have hrightBound :
                              (Nat.unpair third).2 ≤ base :=
                            (Nat.unpair_right_le third).trans hthirdBound
                          rw [show
                            booleanNodeStructuralDescriptor
                                (first :: second :: third :: tail) =
                              booleanNodeBinaryTailOutput
                                4 payload third tail by
                            cases tail <;>
                              by_cases hthird : third = 0 <;>
                              simp [booleanNodeStructuralDescriptor,
                                booleanNodeBinaryTailOutput,
                                validatedNatValue, hfirst, hsecond,
                                htagValue, hpayloadValue, hthird]]
                          apply run_booleanNodeStructuralBinaryTail
                            maximumBits 10 4 payload third tail
                          · rfl
                          · simp [NPOracleState.write,
                              NPOracleState.jump, hcursor]
                          · simp [NPOracleState.write,
                              NPOracleState.jump, htag, htagValue]
                          · simp [NPOracleState.write,
                              NPOracleState.jump, hpayload,
                              hpayloadValue]
                          · exact hzeroBits
                          · exact honeBits
                          · exact hsmallBits _ hcellPayloadBound
                          · exact hsmallBits _ hthirdBound
                          · exact hsmallBits _ htailBound
                          · exact hsmallBits _ hrightBound
                          · exact hunaryDescriptorBits payload
                              (Nat.unpair third).2
                              hpayloadBound hrightBound
                          · exact hbinaryDescriptorBits 4 payload
                              (Nat.unpair third).2
                              (by omega) hpayloadBound hrightBound
                          · exact hbinaryOutputBits 4 payload
                              (Nat.unpair third).2
                              (by omega) hpayloadBound hrightBound
                  | succ tag =>
                      rw [if_neg (by simp)]
                      have houtput :
                          booleanNodeStructuralDescriptor
                              (first :: second :: rest) = 0 := by
                        cases rest with
                        | nil =>
                            simp [booleanNodeStructuralDescriptor,
                              validatedNatValue, hfirst, hsecond,
                              htagValue, hpayloadValue]
                        | cons third tail =>
                            cases tail <;>
                              simp [booleanNodeStructuralDescriptor,
                                validatedNatValue, hfirst, hsecond,
                                htagValue, hpayloadValue]
                      rw [houtput]
                      apply run_booleanNodeStructuralReject maximumBits 20
                      · rfl
                      · exact hzeroBits

private theorem run_booleanNodeStructuralDescriptorProgram
    (inputLength : ℕ) (outputs : List ℕ) :
    runNPOracleProgram booleanNodeStructuralDescriptorProgram
        (booleanNodeStructuralDescriptorBits inputLength
          (encodeTaggedList outputs))
        booleanNodeStructuralDescriptorFuel
        (initialNPOracleState inputLength (encodeTaggedList outputs)) =
      some (booleanNodeStructuralDescriptor outputs) := by
  cases outputs with
  | nil =>
      let maximumBits :=
        booleanNodeStructuralDescriptorBits inputLength
          (encodeTaggedList [])
      have hzeroBits : natBitLength 0 ≤ maximumBits := by
        unfold maximumBits booleanNodeStructuralDescriptorBits
        apply natBitLength_mono
        exact Nat.zero_le _
      change
        runNPOracleProgram booleanNodeStructuralDescriptorProgram
            maximumBits 44
            (initialNPOracleState inputLength 0) =
          some 0
      rw [show (44 : ℕ) = 43 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeStructuralDescriptorProgram)
        (maximumBits := maximumBits) (fuel := 43)
        (pc := 0) (register := 0) (zeroTarget := 43)
        (nonzeroTarget := 1) (by rfl) (by rfl)]
      rw [if_pos (by simp [initialNPOracleState])]
      exact run_booleanNodeStructuralReject maximumBits 41 _ (by rfl)
        hzeroBits
  | cons first rest =>
      cases rest with
      | nil =>
          let input := encodeTaggedList [first]
          let base := max 1 (max inputLength input)
          let maximumBits :=
            booleanNodeStructuralDescriptorBits inputLength input
          have hbase : 1 ≤ base := Nat.le_max_left _ _
          have hinputBound : input ≤ base :=
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
          have hbits :
              natBitLength (pairIter 3 base) ≤ maximumBits := by
            rfl
          have hsmallBits :
              ∀ value, value ≤ base →
                natBitLength value ≤ maximumBits := by
            intro value hvalue
            exact (natBitLength_mono
              (hvalue.trans (value_le_pairIter 3 base))).trans hbits
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            hsmallBits 0 (Nat.zero_le _)
          have hcellPayloadBound :
              Nat.pair first 0 ≤ base := by
            exact (Nat.right_le_pair 1 _).trans hinputBound
          have hfirstBound : first ≤ base :=
            (Nat.left_le_pair first 0).trans hcellPayloadBound
          have hcellPayloadBits :=
            hsmallBits (Nat.pair first 0) hcellPayloadBound
          have hfirstBits := hsmallBits first hfirstBound
          have htagBits :
              natBitLength (Nat.unpair first).2 ≤ maximumBits :=
            hsmallBits _ <|
              (Nat.unpair_right_le first).trans hfirstBound
          change
            runNPOracleProgram booleanNodeStructuralDescriptorProgram
                maximumBits 44
                (initialNPOracleState inputLength input) =
              some 0
          rw [show (44 : ℕ) = 43 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 43)
            (pc := 0) (register := 0) (zeroTarget := 43)
            (nonzeroTarget := 1) (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, input, encodeTaggedList])]
          rw [show (43 : ℕ) = 42 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 42)
            (pc := 1) (source := 0) (destination := 6) (next := 2)
            (value := Nat.pair first 0) (by rfl) (by rfl)
            (by simp [initialNPOracleState, input, encodeTaggedList])
            hcellPayloadBits]
          rw [show (42 : ℕ) = 41 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 41)
            (pc := 2) (source := 6) (destination := 2) (next := 3)
            (value := first) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            hfirstBits]
          rw [show (41 : ℕ) = 40 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 40)
            (pc := 3) (source := 6) (destination := 0) (next := 4)
            (value := 0) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            hzeroBits]
          rw [show (40 : ℕ) = 39 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 39)
            (pc := 4) (register := 2) (zeroTarget := 43)
            (nonzeroTarget := 5) (by rfl) (by rfl)]
          by_cases hfirst : first = 0
          · rw [if_pos (by
              simp [NPOracleState.write, NPOracleState.jump, hfirst])]
            exact run_booleanNodeStructuralReject maximumBits 37 _
              (by rfl) hzeroBits
          · rw [if_neg (by
              simp [NPOracleState.write, NPOracleState.jump, hfirst])]
            rw [show (39 : ℕ) = 38 + 1 by omega]
            rw [run_unpairRight_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 38)
              (pc := 5) (source := 2) (destination := 3) (next := 6)
              (value := (Nat.unpair first).2)
              (by rfl) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump])
              htagBits]
            rw [show (38 : ℕ) = 37 + 1 by omega]
            rw [run_branchZero_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 37)
              (pc := 6) (register := 0) (zeroTarget := 43)
              (nonzeroTarget := 7) (by rfl) (by rfl)]
            rw [if_pos (by
              simp [NPOracleState.write, NPOracleState.jump])]
            exact run_booleanNodeStructuralReject maximumBits 35 _
              (by rfl) hzeroBits
      | cons second rest =>
          let input := encodeTaggedList (first :: second :: rest)
          let tailInput := encodeTaggedList (second :: rest)
          let restInput := encodeTaggedList rest
          let firstPayload := Nat.pair first tailInput
          let secondPayload := Nat.pair second restInput
          let base := max 1 (max inputLength input)
          let maximumBits :=
            booleanNodeStructuralDescriptorBits inputLength input
          have hbase : 1 ≤ base := Nat.le_max_left _ _
          have hinputBound : input ≤ base :=
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
          have hbits :
              natBitLength (pairIter 3 base) ≤ maximumBits := by
            rfl
          have hsmallBits :
              ∀ value, value ≤ base →
                natBitLength value ≤ maximumBits := by
            intro value hvalue
            exact (natBitLength_mono
              (hvalue.trans (value_le_pairIter 3 base))).trans hbits
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            hsmallBits 0 (Nat.zero_le _)
          have hfirstPayloadBound : firstPayload ≤ base := by
            exact (Nat.right_le_pair 1 _).trans hinputBound
          have hfirstBound : first ≤ base :=
            (Nat.left_le_pair first tailInput).trans hfirstPayloadBound
          have htailInputBound : tailInput ≤ base :=
            (Nat.right_le_pair first tailInput).trans hfirstPayloadBound
          have hsecondPayloadBound : secondPayload ≤ base := by
            exact (Nat.right_le_pair 1 _).trans htailInputBound
          have hsecondBound : second ≤ base :=
            (Nat.left_le_pair second restInput).trans
              hsecondPayloadBound
          have hrestInputBound : restInput ≤ base :=
            (Nat.right_le_pair second restInput).trans
              hsecondPayloadBound
          have hfirstPayloadBits :=
            hsmallBits firstPayload hfirstPayloadBound
          have hfirstBits := hsmallBits first hfirstBound
          have htailInputBits := hsmallBits tailInput htailInputBound
          have hsecondPayloadBits :=
            hsmallBits secondPayload hsecondPayloadBound
          have hsecondBits := hsmallBits second hsecondBound
          have hrestInputBits := hsmallBits restInput hrestInputBound
          have htagBits :
              natBitLength (Nat.unpair first).2 ≤ maximumBits :=
            hsmallBits _ <|
              (Nat.unpair_right_le first).trans hfirstBound
          have hpayloadBits :
              natBitLength (Nat.unpair second).2 ≤ maximumBits :=
            hsmallBits _ <|
              (Nat.unpair_right_le second).trans hsecondBound
          change
            runNPOracleProgram booleanNodeStructuralDescriptorProgram
                maximumBits 44
                (initialNPOracleState inputLength input) =
              some
                (booleanNodeStructuralDescriptor
                  (first :: second :: rest))
          rw [show (44 : ℕ) = 43 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 43)
            (pc := 0) (register := 0) (zeroTarget := 43)
            (nonzeroTarget := 1) (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, input, encodeTaggedList])]
          rw [show (43 : ℕ) = 42 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 42)
            (pc := 1) (source := 0) (destination := 6) (next := 2)
            (value := firstPayload) (by rfl) (by rfl)
            (by simp [initialNPOracleState, input, firstPayload,
              tailInput, encodeTaggedList])
            hfirstPayloadBits]
          rw [show (42 : ℕ) = 41 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 41)
            (pc := 2) (source := 6) (destination := 2) (next := 3)
            (value := first) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump,
              firstPayload])
            hfirstBits]
          rw [show (41 : ℕ) = 40 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 40)
            (pc := 3) (source := 6) (destination := 0) (next := 4)
            (value := tailInput) (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump,
              firstPayload])
            htailInputBits]
          rw [show (40 : ℕ) = 39 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanNodeStructuralDescriptorProgram)
            (maximumBits := maximumBits) (fuel := 39)
            (pc := 4) (register := 2) (zeroTarget := 43)
            (nonzeroTarget := 5) (by rfl) (by rfl)]
          by_cases hfirst : first = 0
          · rw [if_pos (by
              simp [NPOracleState.write, NPOracleState.jump, hfirst])]
            rw [show
              booleanNodeStructuralDescriptor
                  (first :: second :: rest) = 0 by
              subst first
              cases rest with
              | nil =>
                  simp [booleanNodeStructuralDescriptor,
                    validatedNatValue]
              | cons third tail =>
                  cases tail <;>
                    simp [booleanNodeStructuralDescriptor,
                      validatedNatValue]]
            exact run_booleanNodeStructuralReject maximumBits 37 _
              (by rfl) hzeroBits
          · rw [if_neg (by
              simp [NPOracleState.write, NPOracleState.jump, hfirst])]
            rw [show (39 : ℕ) = 38 + 1 by omega]
            rw [run_unpairRight_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 38)
              (pc := 5) (source := 2) (destination := 3) (next := 6)
              (value := (Nat.unpair first).2)
              (by rfl) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump])
              htagBits]
            rw [show (38 : ℕ) = 37 + 1 by omega]
            rw [run_branchZero_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 37)
              (pc := 6) (register := 0) (zeroTarget := 43)
              (nonzeroTarget := 7) (by rfl) (by rfl)]
            rw [if_neg (by
              simp [NPOracleState.write, NPOracleState.jump,
                tailInput, encodeTaggedList])]
            rw [show (37 : ℕ) = 36 + 1 by omega]
            rw [run_unpairRight_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 36)
              (pc := 7) (source := 0) (destination := 6) (next := 8)
              (value := secondPayload) (by rfl) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump,
                tailInput, secondPayload, restInput, encodeTaggedList])
              hsecondPayloadBits]
            rw [show (36 : ℕ) = 35 + 1 by omega]
            rw [run_unpairLeft_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 35)
              (pc := 8) (source := 6) (destination := 2) (next := 9)
              (value := second) (by rfl) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump,
                secondPayload])
              hsecondBits]
            rw [show (35 : ℕ) = 34 + 1 by omega]
            rw [run_unpairRight_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 34)
              (pc := 9) (source := 6) (destination := 0) (next := 10)
              (value := restInput) (by rfl) (by rfl)
              (by simp [NPOracleState.write, NPOracleState.jump,
                secondPayload])
              hrestInputBits]
            rw [show (34 : ℕ) = 33 + 1 by omega]
            rw [run_branchZero_instruction
              (program := booleanNodeStructuralDescriptorProgram)
              (maximumBits := maximumBits) (fuel := 33)
              (pc := 10) (register := 2) (zeroTarget := 43)
              (nonzeroTarget := 11) (by rfl) (by rfl)]
            by_cases hsecond : second = 0
            · rw [if_pos (by
                simp [NPOracleState.write, NPOracleState.jump,
                  hsecond])]
              rw [show
                booleanNodeStructuralDescriptor
                    (first :: second :: rest) = 0 by
                subst second
                cases rest with
                | nil =>
                    simp [booleanNodeStructuralDescriptor,
                      validatedNatValue, hfirst]
                | cons third tail =>
                    cases tail <;>
                      simp [booleanNodeStructuralDescriptor,
                        validatedNatValue, hfirst]]
              exact run_booleanNodeStructuralReject maximumBits 31 _
                (by rfl) hzeroBits
            · rw [if_neg (by
                simp [NPOracleState.write, NPOracleState.jump,
                  hsecond])]
              rw [show (33 : ℕ) = 32 + 1 by omega]
              rw [run_unpairRight_instruction
                (program := booleanNodeStructuralDescriptorProgram)
                (maximumBits := maximumBits) (fuel := 32)
                (pc := 11) (source := 2) (destination := 4)
                (next := 12) (value := (Nat.unpair second).2)
                (by rfl) (by rfl)
                (by simp [NPOracleState.write, NPOracleState.jump])
                hpayloadBits]
              apply run_booleanNodeStructuralSuffix
                maximumBits base first second rest
              · rfl
              · simp [NPOracleState.write, NPOracleState.jump,
                  restInput]
              · simp [NPOracleState.write, NPOracleState.jump]
              · simp [NPOracleState.write, NPOracleState.jump]
              · exact hfirst
              · exact hsecond
              · exact hbase
              · exact hfirstBound
              · exact hsecondBound
              · exact hrestInputBound
              · exact hbits

/-- The complete structural validator.  The only public input is the raw node
word; every Nat field flows through the shared canonical mapper exactly once. -/
def booleanNodeValidationProgram : NPOracleProgram :=
  linkPrograms taggedNatListValidationProgram
    booleanNodeStructuralDescriptorProgram

@[simp] theorem booleanNodeValidationProgram_oracleFree :
    OracleFree booleanNodeValidationProgram := by
  exact oracleFree_linkPrograms
    taggedNatListValidationProgram_oracleFree
    booleanNodeStructuralDescriptorProgram_oracleFree

def booleanNodeValidationFuel (inputLength raw : ℕ) : ℕ :=
  linkFuel booleanNodeStructuralDescriptorProgram
    (taggedNatListValidationFuel inputLength raw)
    booleanNodeStructuralDescriptorFuel

def booleanNodeValidationBits (inputLength raw : ℕ) : ℕ :=
  max (taggedNatListValidationBits inputLength raw)
    (booleanNodeStructuralDescriptorBits inputLength
      (taggedNatListValidationOutput raw))

theorem run_booleanNodeValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeValidationProgram
        (booleanNodeValidationBits inputLength raw)
        (booleanNodeValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanNodeStructuralOutput raw) := by
  let maximumBits := booleanNodeValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    apply (show 1 ≤ taggedNatListValidationBits inputLength raw from ?_).trans
      (Nat.le_max_left _ _)
    simp [taggedNatListValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply (show natBitLength inputLength ≤
      taggedNatListValidationBits inputLength raw from ?_).trans
        (Nat.le_max_left _ _)
    simp [taggedNatListValidationBits]
  have hmapper :
      runNPOracleProgram taggedNatListValidationProgram maximumBits
          (taggedNatListValidationFuel inputLength raw)
          (initialNPOracleState inputLength raw) =
        some (taggedNatListValidationOutput raw) := by
    exact run_bits_mono
      (run_taggedNatListValidationProgram inputLength raw)
      (Nat.le_max_left _ _)
  have hdescriptor :
      runNPOracleProgram booleanNodeStructuralDescriptorProgram maximumBits
          booleanNodeStructuralDescriptorFuel
          (initialNPOracleState inputLength
            (taggedNatListValidationOutput raw)) =
        some (booleanNodeStructuralOutput raw) := by
    apply run_bits_mono
      (run_booleanNodeStructuralDescriptorProgram inputLength
        (taggedNatFieldOutputs raw))
      (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlength hmapper hdescriptor

@[simp] theorem booleanNodeStructuralOutput_encodeBooleanNode
    {inputLength : ℕ} (node : BooleanNode inputLength) :
    booleanNodeStructuralOutput (encodeBooleanNode node) =
      match node with
      | .const value => Nat.pair 1 (Nat.pair 0 value.toNat)
      | .input input => Nat.pair 1 (Nat.pair 1 input.val)
      | .not child => Nat.pair 1 (Nat.pair 2 child)
      | .and left right =>
          Nat.pair 1 (Nat.pair 3 (Nat.pair left right))
      | .or left right =>
          Nat.pair 1 (Nat.pair 4 (Nat.pair left right)) := by
  cases node with
  | const value =>
      cases value <;>
        simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
          taggedNatFieldOutputs, taggedNatFieldCodes, encodeBooleanNode,
          validatedNatValue]
  | input input =>
      simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
        taggedNatFieldOutputs, taggedNatFieldCodes, encodeBooleanNode,
        validatedNatValue]
  | not child =>
      simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
        taggedNatFieldOutputs, taggedNatFieldCodes, encodeBooleanNode,
        validatedNatValue]
  | and left right =>
      simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
        taggedNatFieldOutputs, taggedNatFieldCodes, encodeBooleanNode,
        validatedNatValue]
  | or left right =>
      simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
        taggedNatFieldOutputs, taggedNatFieldCodes, encodeBooleanNode,
        validatedNatValue]

/-! ## Structural acceptance characterization -/

/-- A nonzero structural result has exactly one public node encoding.  The
input-index and child-index inequalities remain deliberately outside this
theorem; the indexed topology pass is their sole executable checker. -/
theorem booleanNodeStructuralOutput_ne_zero_iff (raw : ℕ) :
    booleanNodeStructuralOutput raw ≠ 0 ↔
      (raw =
          encodeTaggedList [encodeNat 0, encodeNat 0] ∨
        raw =
          encodeTaggedList [encodeNat 0, encodeNat 1]) ∨
      (∃ input,
        raw = encodeTaggedList [encodeNat 1, encodeNat input]) ∨
      (∃ child,
        raw = encodeTaggedList [encodeNat 2, encodeNat child]) ∨
      (∃ left right,
        raw =
          encodeTaggedList
            [encodeNat 3, encodeNat left, encodeNat right]) ∨
      ∃ left right,
        raw =
          encodeTaggedList
            [encodeNat 4, encodeNat left, encodeNat right] := by
  constructor
  · intro hnonzero
    cases hfields : decodeTaggedList raw with
    | none =>
        simp [booleanNodeStructuralOutput, booleanNodeStructuralDescriptor,
          taggedNatFieldOutputs, taggedNatFieldCodes, hfields] at hnonzero
    | some fields =>
        have hraw : encodeTaggedList fields = raw :=
          encodeTaggedList_of_decode hfields
        cases fields with
        | nil =>
            simp [booleanNodeStructuralOutput,
              booleanNodeStructuralDescriptor, taggedNatFieldOutputs,
              taggedNatFieldCodes, hfields] at hnonzero
        | cons first rest =>
            cases rest with
            | nil =>
                simp [booleanNodeStructuralOutput,
                  booleanNodeStructuralDescriptor,
                  taggedNatFieldOutputs, taggedNatFieldCodes,
                  hfields] at hnonzero
            | cons second rest =>
                cases rest with
                | nil =>
                    cases hfirst : decodeNat first with
                    | none =>
                        have hfirstOutput :
                            canonicalNatValidationOutput first = 0 :=
                          (canonicalNatValidationOutput_eq_zero_iff first).2
                            hfirst
                        simp [booleanNodeStructuralOutput,
                          booleanNodeStructuralDescriptor,
                          taggedNatFieldOutputs, taggedNatFieldCodes,
                          hfields, hfirstOutput,
                          validatedNatValue] at hnonzero
                    | some tag =>
                        have hfirstOutput :
                            canonicalNatValidationOutput first =
                              Nat.pair 1 tag :=
                          canonicalNatValidationOutput_of_decode hfirst
                        have hfirstCode : encodeNat tag = first :=
                          encodeNat_of_decode hfirst
                        cases hsecond : decodeNat second with
                        | none =>
                            have hsecondOutput :
                                canonicalNatValidationOutput second = 0 :=
                              (canonicalNatValidationOutput_eq_zero_iff
                                second).2 hsecond
                            simp [booleanNodeStructuralOutput,
                              booleanNodeStructuralDescriptor,
                              taggedNatFieldOutputs, taggedNatFieldCodes,
                              hfields, hfirstOutput, hsecondOutput,
                              validatedNatValue] at hnonzero
                        | some payload =>
                            have hsecondOutput :
                                canonicalNatValidationOutput second =
                                  Nat.pair 1 payload :=
                              canonicalNatValidationOutput_of_decode hsecond
                            have hsecondCode :
                                encodeNat payload = second :=
                              encodeNat_of_decode hsecond
                            have hcode :
                                raw =
                                  encodeTaggedList
                                    [encodeNat tag, encodeNat payload] := by
                              rw [hfirstCode, hsecondCode]
                              exact hraw.symm
                            rcases tag with _ | tag
                            · have hpayload :
                                  payload = 0 ∨ payload = 1 := by
                                by_cases hzero : payload = 0
                                · exact Or.inl hzero
                                · right
                                  simpa [booleanNodeStructuralOutput,
                                    booleanNodeStructuralDescriptor,
                                    taggedNatFieldOutputs,
                                    taggedNatFieldCodes, hfields,
                                    hfirstOutput, hsecondOutput,
                                    validatedNatValue, hzero] using
                                    hnonzero
                              rcases hpayload with rfl | rfl
                              · exact Or.inl (Or.inl hcode)
                              · exact Or.inl (Or.inr hcode)
                            · rcases tag with _ | tag
                              · exact Or.inr <| Or.inl ⟨payload, hcode⟩
                              · rcases tag with _ | tag
                                · exact Or.inr <| Or.inr <|
                                    Or.inl ⟨payload, hcode⟩
                                · simp [booleanNodeStructuralOutput,
                                    booleanNodeStructuralDescriptor,
                                    taggedNatFieldOutputs,
                                    taggedNatFieldCodes, hfields,
                                    hfirstOutput, hsecondOutput,
                                    validatedNatValue] at hnonzero
                | cons third rest =>
                    cases rest with
                    | nil =>
                        cases hfirst : decodeNat first with
                        | none =>
                            have hfirstOutput :
                                canonicalNatValidationOutput first = 0 :=
                              (canonicalNatValidationOutput_eq_zero_iff
                                first).2 hfirst
                            simp [booleanNodeStructuralOutput,
                              booleanNodeStructuralDescriptor,
                              taggedNatFieldOutputs, taggedNatFieldCodes,
                              hfields, hfirstOutput,
                              validatedNatValue] at hnonzero
                        | some tag =>
                            have hfirstOutput :
                                canonicalNatValidationOutput first =
                                  Nat.pair 1 tag :=
                              canonicalNatValidationOutput_of_decode hfirst
                            have hfirstCode : encodeNat tag = first :=
                              encodeNat_of_decode hfirst
                            cases hsecond : decodeNat second with
                            | none =>
                                have hsecondOutput :
                                    canonicalNatValidationOutput second =
                                      0 :=
                                  (canonicalNatValidationOutput_eq_zero_iff
                                    second).2 hsecond
                                simp [booleanNodeStructuralOutput,
                                  booleanNodeStructuralDescriptor,
                                  taggedNatFieldOutputs,
                                  taggedNatFieldCodes, hfields,
                                  hfirstOutput, hsecondOutput,
                                  validatedNatValue] at hnonzero
                            | some left =>
                                have hsecondOutput :
                                    canonicalNatValidationOutput second =
                                      Nat.pair 1 left :=
                                  canonicalNatValidationOutput_of_decode
                                    hsecond
                                have hsecondCode :
                                    encodeNat left = second :=
                                  encodeNat_of_decode hsecond
                                cases hthird : decodeNat third with
                                | none =>
                                    have hthirdOutput :
                                        canonicalNatValidationOutput third =
                                          0 :=
                                      (canonicalNatValidationOutput_eq_zero_iff
                                        third).2 hthird
                                    simp [booleanNodeStructuralOutput,
                                      booleanNodeStructuralDescriptor,
                                      taggedNatFieldOutputs,
                                      taggedNatFieldCodes, hfields,
                                      hfirstOutput, hsecondOutput,
                                      hthirdOutput,
                                      validatedNatValue] at hnonzero
                                | some right =>
                                    have hthirdOutput :
                                        canonicalNatValidationOutput third =
                                          Nat.pair 1 right :=
                                      canonicalNatValidationOutput_of_decode
                                        hthird
                                    have hthirdCode :
                                        encodeNat right = third :=
                                      encodeNat_of_decode hthird
                                    have hcode :
                                        raw =
                                          encodeTaggedList
                                            [encodeNat tag, encodeNat left,
                                              encodeNat right] := by
                                      rw [hfirstCode, hsecondCode,
                                        hthirdCode]
                                      exact hraw.symm
                                    rcases tag with _ | tag
                                    · simp [booleanNodeStructuralOutput,
                                        booleanNodeStructuralDescriptor,
                                        taggedNatFieldOutputs,
                                        taggedNatFieldCodes, hfields,
                                        hfirstOutput, hsecondOutput,
                                        hthirdOutput,
                                        validatedNatValue] at hnonzero
                                    · rcases tag with _ | tag
                                      · simp [booleanNodeStructuralOutput,
                                          booleanNodeStructuralDescriptor,
                                          taggedNatFieldOutputs,
                                          taggedNatFieldCodes, hfields,
                                          hfirstOutput, hsecondOutput,
                                          hthirdOutput,
                                          validatedNatValue] at hnonzero
                                      · rcases tag with _ | tag
                                        · simp [booleanNodeStructuralOutput,
                                            booleanNodeStructuralDescriptor,
                                            taggedNatFieldOutputs,
                                            taggedNatFieldCodes, hfields,
                                            hfirstOutput, hsecondOutput,
                                            hthirdOutput,
                                            validatedNatValue] at hnonzero
                                        · rcases tag with _ | tag
                                          · exact Or.inr <| Or.inr <|
                                              Or.inr <| Or.inl
                                                ⟨left, right, hcode⟩
                                          · rcases tag with _ | tag
                                            · exact Or.inr <| Or.inr <|
                                                Or.inr <| Or.inr
                                                  ⟨left, right, hcode⟩
                                            · simp [
                                                booleanNodeStructuralOutput,
                                                booleanNodeStructuralDescriptor,
                                                taggedNatFieldOutputs,
                                                taggedNatFieldCodes, hfields,
                                                hfirstOutput, hsecondOutput,
                                                hthirdOutput,
                                                validatedNatValue] at hnonzero
                    | cons fourth tail =>
                        simp [booleanNodeStructuralOutput,
                          booleanNodeStructuralDescriptor,
                          taggedNatFieldOutputs, taggedNatFieldCodes,
                          hfields] at hnonzero
  · rintro ((hfalse | htrue) | ⟨input, hinput⟩ |
      ⟨child, hchild⟩ | ⟨left, right, hand⟩ |
      ⟨left, right, hor⟩)
    · subst raw
      rw [show
        encodeTaggedList [encodeNat 0, encodeNat 0] =
          encodeBooleanNode (BooleanNode.const false : BooleanNode 0) by
        rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _
    · subst raw
      rw [show
        encodeTaggedList [encodeNat 0, encodeNat 1] =
          encodeBooleanNode (BooleanNode.const true : BooleanNode 0) by
        rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _
    · subst raw
      let node : BooleanNode (input + 1) :=
        BooleanNode.input ⟨input, by omega⟩
      rw [show
        encodeTaggedList [encodeNat 1, encodeNat input] =
          encodeBooleanNode node by rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _
    · subst raw
      rw [show
        encodeTaggedList [encodeNat 2, encodeNat child] =
          encodeBooleanNode (BooleanNode.not child : BooleanNode 0) by
        rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _
    · subst raw
      rw [show
        encodeTaggedList [encodeNat 3, encodeNat left, encodeNat right] =
          encodeBooleanNode
            (BooleanNode.and left right : BooleanNode 0) by rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _
    · subst raw
      rw [show
        encodeTaggedList [encodeNat 4, encodeNat left, encodeNat right] =
          encodeBooleanNode
            (BooleanNode.or left right : BooleanNode 0) by rfl]
      rw [booleanNodeStructuralOutput_encodeBooleanNode]
      exact pair_one_ne_zero _

end NearCubicWires.CanonicalBooleanNodeValidationProgram
