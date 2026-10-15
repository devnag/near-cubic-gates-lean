import Proof.MachineModel.CanonicalNatDecodeProgram

/-!
# Canonical parity of a balanced bit stream

Case 2 evaluates one fixed seed program on each consecutive input block and
XORs the resulting bits.  The balanced caller already produces the canonical
balanced output tree.  This module reuses its sole balanced-to-tagged adapter
and adds the smallest possible tagged fold: nonzero entries toggle one Boolean
accumulator.  No decoded list, host parity callback, or second tree traversal
crosses the executable boundary.
-/

namespace NearCubicWires.CanonicalTaggedParityProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

def parityStep (bit accumulator : ℕ) : ℕ :=
  if bit = 0 then accumulator else if accumulator = 0 then 1 else 0

def taggedParityFrom : List ℕ → ℕ → ℕ
  | [], accumulator => accumulator
  | bit :: bits, accumulator =>
      taggedParityFrom bits (parityStep bit accumulator)

def taggedParity (bits : List ℕ) : ℕ :=
  taggedParityFrom bits 0

@[simp] theorem parityStep_zero (accumulator : ℕ) :
    parityStep 0 accumulator = accumulator := by
  simp [parityStep]

theorem parityStep_nonzero {bit : ℕ} (hbit : bit ≠ 0)
    (accumulator : ℕ) :
    parityStep bit accumulator =
      if accumulator = 0 then 1 else 0 := by
  simp [parityStep, hbit]

private theorem parityStep_le_one
    (bit accumulator : ℕ) (haccumulator : accumulator ≤ 1) :
    parityStep bit accumulator ≤ 1 := by
  unfold parityStep
  split
  · exact haccumulator
  · split <;> omega

theorem taggedParityFrom_le_one
    (bits : List ℕ) (accumulator : ℕ)
    (haccumulator : accumulator ≤ 1) :
    taggedParityFrom bits accumulator ≤ 1 := by
  induction bits generalizing accumulator with
  | nil =>
      simpa [taggedParityFrom] using haccumulator
  | cons bit bits inductionHypothesis =>
      simp only [taggedParityFrom]
      exact inductionHypothesis
        (parityStep bit accumulator)
        (parityStep_le_one bit accumulator haccumulator)

@[simp] theorem taggedParity_le_one (bits : List ℕ) :
    taggedParity bits ≤ 1 :=
  taggedParityFrom_le_one bits 0 (by omega)

private theorem parityStep_toNat
    (bit : ℕ) (accumulator : Bool) :
    parityStep bit accumulator.toNat =
      (xor accumulator (decide (bit ≠ 0))).toNat := by
  cases accumulator <;> by_cases hbit : bit = 0 <;>
    simp [parityStep, hbit]

theorem taggedParityFrom_eq_foldl
    (bits : List ℕ) (accumulator : Bool) :
    taggedParityFrom bits accumulator.toNat =
      (bits.foldl
        (fun parity bit => xor parity (decide (bit ≠ 0)))
        accumulator).toNat := by
  induction bits generalizing accumulator with
  | nil =>
      rfl
  | cons bit bits inductionHypothesis =>
      rw [taggedParityFrom, List.foldl_cons, parityStep_toNat]
      exact inductionHypothesis
        (xor accumulator (decide (bit ≠ 0)))

theorem taggedParity_eq_foldl (bits : List ℕ) :
    taggedParity bits =
      (bits.foldl
        (fun parity bit => xor parity (decide (bit ≠ 0)))
        false).toNat := by
  exact taggedParityFrom_eq_foldl bits false

private theorem foldl_map_boolToNat
    (bits : List Bool) (accumulator : Bool) :
    (bits.map Bool.toNat).foldl
        (fun parity bit => xor parity (decide (bit ≠ 0)))
        accumulator =
      bits.foldl xor accumulator := by
  induction bits generalizing accumulator with
  | nil =>
      rfl
  | cons bit bits inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      have hbit :
          decide (bit.toNat ≠ 0) = bit := by
        cases bit <;> simp
      rw [hbit]
      exact inductionHypothesis (xor accumulator bit)

@[simp] theorem taggedParity_boolToNat (bits : List Bool) :
    taggedParity (bits.map Bool.toNat) =
      (bits.foldl xor false).toNat := by
  rw [taggedParity_eq_foldl]
  rw [foldl_map_boolToNat]

/-!
Register ABI:

* `r0`: tagged cursor, then output;
* `r2`: Boolean parity accumulator;
* `r4`: current bit;
* `r5`: current tagged-cell payload.

Malformed nonzero bit values intentionally count as `true`, matching every
other Boolean-output boundary in the executable layer.
-/
def taggedParityProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .branchZero 0 9 2
  , .unpairRight 0 5 3
  , .unpairLeft 5 4 4
  , .unpairRight 5 0 5
  , .branchZero 4 1 6
  , .branchZero 2 8 7
  , .set 2 0 1
  , .set 2 1 1
  , .copy 2 0 10
  , .halt 0
  ]

@[simp] theorem taggedParityProgram_oracleFree :
    OracleFree taggedParityProgram := by
  rfl

def taggedParityLoopFuel : List ℕ → ℕ
  | [] => 3
  | bit :: bits =>
      (if bit = 0 then 5 else 7) + taggedParityLoopFuel bits

def taggedParityFuel (bits : List ℕ) : ℕ :=
  1 + taggedParityLoopFuel bits

def taggedParityBits (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  natBitLength (max inputLength (encodeTaggedList bits))

private theorem run_taggedParityLoop
    (bits : List ℕ) (accumulator maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 1)
    (hcursor :
      state.registers 0 = encodeTaggedList bits)
    (haccumulator : state.registers 2 = accumulator)
    (haccumulatorLe : accumulator ≤ 1)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hcursorBits :
      natBitLength (encodeTaggedList bits) ≤ maximumBits) :
    runNPOracleProgram taggedParityProgram maximumBits
        (taggedParityLoopFuel bits) state =
      some (taggedParityFrom bits accumulator) := by
  induction bits generalizing accumulator state with
  | nil =>
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits := by
        exact (natBitLength_mono haccumulatorLe).trans honeBits
      rw [taggedParityLoopFuel, taggedParityFrom]
      rw [show 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcursor, encodeTaggedList, if_pos rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (value := accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.jump, haccumulator])
        haccumulatorBits]
      exact run_halt_instruction (fuel := 0)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        haccumulatorBits
  | cons bit bits inductionHypothesis =>
      let tailCode := encodeTaggedList bits
      let payload := Nat.pair bit tailCode
      let state1 := ((state.jump 2).write 5 payload).jump 3
      let state2 := (state1.write 4 bit).jump 4
      let state3 := (state2.write 0 tailCode).jump 5
      have hpayloadBits :
          natBitLength payload ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hcursorBits
        simpa only [encodeTaggedList, payload] using
          Nat.right_le_pair 1 payload
      have hbitBits :
          natBitLength bit ≤ maximumBits := by
        exact
          (natBitLength_mono
            (Nat.left_le_pair bit tailCode)).trans hpayloadBits
      have htailBits :
          natBitLength tailCode ≤ maximumBits := by
        exact
          (natBitLength_mono
            (Nat.right_le_pair bit tailCode)).trans hpayloadBits
      have hcellNonzero : Nat.pair 1 payload ≠ 0 := by
        have hpositive : 1 ≤ Nat.pair 1 payload :=
          Nat.left_le_pair 1 payload
        omega
      rw [taggedParityLoopFuel, taggedParityFrom]
      rw [show
        (if bit = 0 then 5 else 7) +
            taggedParityLoopFuel bits =
          ((if bit = 0 then 4 else 6) +
            taggedParityLoopFuel bits) + 1 by
        split <;> omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [show
        (if state.registers 0 = 0 then 9 else 2) = 2 by
          rw [hcursor, encodeTaggedList]
          exact if_neg (by
            simpa only [payload] using hcellNonzero)]
      rw [show
        (if bit = 0 then 4 else 6) +
            taggedParityLoopFuel bits =
          ((if bit = 0 then 3 else 5) +
            taggedParityLoopFuel bits) + 1 by
        split <;> omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by simp [hcursor, encodeTaggedList, payload, tailCode])
        hpayloadBits]
      change
        runNPOracleProgram taggedParityProgram maximumBits
            ((if bit = 0 then 3 else 5) +
              taggedParityLoopFuel bits) state1 =
          some (taggedParityFrom bits (parityStep bit accumulator))
      rw [show
        (if bit = 0 then 3 else 5) +
            taggedParityLoopFuel bits =
          ((if bit = 0 then 2 else 4) +
            taggedParityLoopFuel bits) + 1 by
        split <;> omega]
      rw [run_unpairLeft_instruction (value := bit)
        (by rfl) rfl
        (by simp [state1, payload])
        hbitBits]
      change
        runNPOracleProgram taggedParityProgram maximumBits
            ((if bit = 0 then 2 else 4) +
              taggedParityLoopFuel bits) state2 =
          some (taggedParityFrom bits (parityStep bit accumulator))
      rw [show
        (if bit = 0 then 2 else 4) +
            taggedParityLoopFuel bits =
          ((if bit = 0 then 1 else 3) +
            taggedParityLoopFuel bits) + 1 by
        split <;> omega]
      rw [run_unpairRight_instruction (value := tailCode)
        (by rfl) rfl
        (by simp [state2, state1, payload])
        htailBits]
      change
        runNPOracleProgram taggedParityProgram maximumBits
            ((if bit = 0 then 1 else 3) +
              taggedParityLoopFuel bits) state3 =
          some (taggedParityFrom bits (parityStep bit accumulator))
      by_cases hbit : bit = 0
      · subst bit
        simp only [if_true, parityStep_zero]
        rw [show
          1 + taggedParityLoopFuel bits =
            taggedParityLoopFuel bits + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state3.registers 4 = 0 by
          simp [state3, state2]]
        rw [if_pos rfl]
        apply inductionHypothesis accumulator (state3.jump 1)
        · rfl
        · simp [state3, state2, tailCode]
        · simp [state3, state2, state1, haccumulator]
        · exact haccumulatorLe
        · exact htailBits
      · simp only [if_neg hbit, parityStep_nonzero hbit]
        rw [show
          3 + taggedParityLoopFuel bits =
            (2 + taggedParityLoopFuel bits) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state3.registers 4 = bit by
          simp [state3, state2]]
        rw [if_neg hbit]
        by_cases haccumulatorZero : accumulator = 0
        · rw [show
            2 + taggedParityLoopFuel bits =
              (1 + taggedParityLoopFuel bits) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          rw [show (state3.jump 6).registers 2 = 0 by
            simp [state3, state2, state1, haccumulator,
              haccumulatorZero]]
          rw [if_pos rfl]
          rw [show
            1 + taggedParityLoopFuel bits =
              taggedParityLoopFuel bits + 1 by omega]
          rw [run_set_instruction (value := 1)
            (by rfl) rfl honeBits]
          simp only [if_pos haccumulatorZero]
          apply inductionHypothesis 1
            ((((state3.jump 6).jump 8).write 2 1).jump 1)
          · rfl
          · simp [state3, state2, tailCode]
          · simp
          · omega
          · exact htailBits
        · rw [show
            2 + taggedParityLoopFuel bits =
              (1 + taggedParityLoopFuel bits) + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          rw [show
            (state3.jump 6).registers 2 = accumulator by
              simp [state3, state2, state1, haccumulator]]
          rw [if_neg haccumulatorZero]
          rw [show
            1 + taggedParityLoopFuel bits =
              taggedParityLoopFuel bits + 1 by omega]
          have hzeroBits :
              natBitLength 0 ≤ maximumBits := by
            apply (natBitLength_mono ?_).trans hcursorBits
            exact Nat.zero_le _
          rw [run_set_instruction (value := 0)
            (by rfl) rfl hzeroBits]
          simp only [if_neg haccumulatorZero]
          apply inductionHypothesis 0
            ((((state3.jump 6).jump 7).write 2 0).jump 1)
          · rfl
          · simp [state3, state2, tailCode]
          · simp
          · omega
          · exact htailBits

theorem run_taggedParityProgram
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram taggedParityProgram
        (taggedParityBits inputLength bits)
        (taggedParityFuel bits)
        (initialNPOracleState inputLength
          (encodeTaggedList bits)) =
      some (taggedParity bits) := by
  let maximumBits := taggedParityBits inputLength bits
  have hcursorBits :
      natBitLength (encodeTaggedList bits) ≤ maximumBits := by
    unfold maximumBits taggedParityBits
    exact natBitLength_mono (Nat.le_max_right _ _)
  have hzeroBits :
      natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le _)).trans hcursorBits
  have honeBits :
      natBitLength 1 ≤ maximumBits := by
    have hpositive : 1 ≤ maximumBits := by
      unfold maximumBits taggedParityBits natBitLength
      omega
    norm_num [natBitLength]
    exact hpositive
  rw [show taggedParityFuel bits =
      taggedParityLoopFuel bits + 1 by
    unfold taggedParityFuel
    omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  exact run_taggedParityLoop bits 0 maximumBits
    (((initialNPOracleState inputLength
      (encodeTaggedList bits)).write 2 0).jump 1)
    rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (by simp)
    (by omega)
    honeBits
    hcursorBits

/-! ## Canonical balanced entry point -/

def balancedBitParityProgram : NPOracleProgram :=
  linkPrograms balancedBitsToTaggedProgram taggedParityProgram

def balancedBitParityFuel (bits : List ℕ) : ℕ :=
  linkFuel taggedParityProgram
    (balancedBitsToTaggedFuel bits)
    (taggedParityFuel bits)

def balancedBitParityBits
    (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (balancedBitsToTaggedBits inputLength bits)
      (taggedParityBits inputLength bits)

@[simp] theorem balancedBitParityProgram_oracleFree :
    OracleFree balancedBitParityProgram := by
  exact oracleFree_linkPrograms
    balancedBitsToTaggedProgram_oracleFree
    taggedParityProgram_oracleFree

theorem run_balancedBitParityProgram
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram balancedBitParityProgram
        (balancedBitParityBits inputLength bits)
        (balancedBitParityFuel bits)
        (initialNPOracleState inputLength
          (encodeBalancedList bits)) =
      some (taggedParity bits) := by
  let maximumBits := balancedBitParityBits inputLength bits
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hfirstBits :
      balancedBitsToTaggedBits inputLength bits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondBits :
      taggedParityBits inputLength bits ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  apply run_linkPrograms hpositive hlengthBits
  · exact run_bits_mono
      (run_balancedBitsToTaggedProgram inputLength bits)
      hfirstBits
  · exact run_bits_mono
      (run_taggedParityProgram inputLength bits)
      hsecondBits

end NearCubicWires.CanonicalTaggedParityProgram
