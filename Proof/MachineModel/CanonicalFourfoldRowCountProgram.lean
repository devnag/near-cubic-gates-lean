import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalFourfoldRowTailProgram

/-!
# The row-major atom counter of a fourfold range request

`CanonicalFourfoldRowTailProgram` reduces the composed aggregation program to
two link-time parameters.  This module discharges the *product* half of the
second one.

The envelope front end needs the row-major atom count

```text
fourfoldRangeAtomCount rows request = rows.rowCount request * 2 ^ request.q
```

as a machine value computed from the typed envelope alone.  The arity `q` is
already present in the interpreter's public length register, so the second
factor never has to be parsed: this module supplies the fixed doubling loop
that materializes `2 ^ q` from that register, pairs it with a link-time row
count, and multiplies with the existing bit-serial multiplier.

Consequently the residual on the counting side is exactly one program: an
`NPOracleProgram` computing `rows.rowCount request` from the typed envelope.
Nothing here assumes a semantic evaluator, a callback, or a fuel argument.
-/

namespace NearCubicWires.CanonicalFourfoldRowCountProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 Materializing `2 ^ q` beside the row count

The interpreter's register `r1` holds the public input length on entry to
every linked stage, so the arity is available without decoding the envelope a
second time.  Registers `r2` and `r3` are the loop cursor and accumulator. -/

/-- Multiplier ABI of the atom count: the row count on the left, the size of
the Boolean cube on the right. -/
def fourfoldAtomCountPairOutput (rowCount inputLength : ℕ) : ℕ :=
  Nat.pair rowCount (2 ^ inputLength)

/-- Fixed doubling loop.  `r2` counts down from the public arity while `r3`
doubles from one; the halting pair is the bit-serial multiplier's request. -/
def fourfoldAtomCountPairProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .set 3 1 2
  , .branchZero 2 5 3
  , .decrement 2 4
  , .add 3 3 3 2
  , .pair 0 3 0 6
  , .halt 0
  ]

@[simp] theorem fourfoldAtomCountPairProgram_oracleFree :
    OracleFree fourfoldAtomCountPairProgram := by
  rfl

def fourfoldAtomCountPairBits (rowCount inputLength : ℕ) : ℕ :=
  natBitLength (fourfoldAtomCountPairOutput rowCount inputLength)

def fourfoldAtomCountPairFuel (inputLength : ℕ) : ℕ :=
  3 * inputLength + 5

private theorem run_fourfoldAtomCountLoop (maximumBits rowCount : ℕ) :
    ∀ (remaining accumulator : ℕ) (state : NPOracleState),
      state.pc = 2 →
      state.registers 0 = rowCount →
      state.registers 2 = remaining →
      state.registers 3 = accumulator →
      natBitLength remaining ≤ maximumBits →
      (∀ step, step ≤ remaining →
        natBitLength (accumulator * 2 ^ step) ≤ maximumBits) →
      natBitLength (Nat.pair rowCount (accumulator * 2 ^ remaining)) ≤
        maximumBits →
      runNPOracleProgram fourfoldAtomCountPairProgram maximumBits
          (3 * remaining + 3) state =
        some (Nat.pair rowCount (accumulator * 2 ^ remaining)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro accumulator state hpc hrowCount hremaining haccumulator
        _hremainingBits _hstepBits houtputBits
      rw [pow_zero, mul_one] at houtputBits ⊢
      have hjump :
          (state.jump
            (if state.registers 2 = 0 then 5 else 3)).pc = 5 := by
        simp [NPOracleState.jump, hremaining]
      rw [show 3 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction
        (program := fourfoldAtomCountPairProgram) (register := 2)
        (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) hpc]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (value := Nat.pair rowCount accumulator)
        (by rfl) hjump
        (by simp [NPOracleState.jump, hrowCount, haccumulator])
        houtputBits]
      exact run_halt_instruction (fuel := 0)
        (value := Nat.pair rowCount accumulator) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        houtputBits
  | succ predecessor inductionHypothesis =>
      intro accumulator state hpc hrowCount hremaining haccumulator
        hremainingBits hstepBits houtputBits
      have hdouble : ∀ step : ℕ,
          (accumulator + accumulator) * 2 ^ step =
            accumulator * 2 ^ (step + 1) := by
        intro step
        ring
      have hjump :
          (state.jump
            (if state.registers 2 = 0 then 5 else 3)).pc = 3 := by
        simp [NPOracleState.jump, hremaining]
      have hpredecessorBits : natBitLength predecessor ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ predecessor)).trans hremainingBits
      have hdoubleBits :
          natBitLength (accumulator + accumulator) ≤ maximumBits := by
        have hstep := hstepBits 1 (by omega)
        rwa [pow_one, Nat.mul_two] at hstep
      rw [show 3 * (predecessor + 1) + 3 = 3 * predecessor + 3 + 1 + 1 + 1 by
        omega]
      rw [run_branchZero_instruction
        (program := fourfoldAtomCountPairProgram) (register := 2)
        (zeroTarget := 5) (nonzeroTarget := 3) (by rfl) hpc]
      rw [run_decrement_instruction (value := predecessor) (by rfl) hjump
        (by simp [NPOracleState.jump, hremaining]) hpredecessorBits]
      rw [run_add_instruction (value := accumulator + accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, haccumulator])
        hdoubleBits]
      rw [show accumulator * 2 ^ (predecessor + 1) =
        (accumulator + accumulator) * 2 ^ predecessor from
          (hdouble predecessor).symm]
      refine inductionHypothesis (accumulator + accumulator) _ rfl ?_ ?_ ?_
        hpredecessorBits ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hrowCount]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro step hstep
        rw [hdouble step]
        exact hstepBits (step + 1) (by omega)
      · rw [hdouble predecessor]
        exact houtputBits

/-- **The atom multiplier's request, executed.**  From the row count in
register zero and the public arity in register one, the fixed loop emits the
canonical `(rowCount, 2 ^ q)` multiplication request. -/
theorem run_fourfoldAtomCountPairProgram
    (inputLength rowCount maximumBits : ℕ)
    (hbits : fourfoldAtomCountPairBits rowCount inputLength ≤ maximumBits) :
    runNPOracleProgram fourfoldAtomCountPairProgram maximumBits
        (fourfoldAtomCountPairFuel inputLength)
        (initialNPOracleState inputLength rowCount) =
      some (fourfoldAtomCountPairOutput rowCount inputLength) := by
  have houtputBits :
      natBitLength (Nat.pair rowCount (2 ^ inputLength)) ≤ maximumBits :=
    hbits
  have hcubeBits : natBitLength (2 ^ inputLength) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair rowCount (2 ^ inputLength))).trans houtputBits
  have harityBits : natBitLength inputLength ≤ maximumBits :=
    (natBitLength_mono (Nat.lt_two_pow_self).le).trans hcubeBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (Nat.one_le_two_pow)).trans hcubeBits
  have hstepBits : ∀ step, step ≤ inputLength →
      natBitLength (1 * 2 ^ step) ≤ maximumBits := by
    intro step hstep
    rw [one_mul]
    exact (natBitLength_mono (Nat.pow_le_pow_right (by omega) hstep)).trans
      hcubeBits
  have hloopOutputBits :
      natBitLength (Nat.pair rowCount (1 * 2 ^ inputLength)) ≤ maximumBits := by
    rw [one_mul]
    exact houtputBits
  unfold fourfoldAtomCountPairOutput fourfoldAtomCountPairFuel
  rw [show 3 * inputLength + 5 = 3 * inputLength + 3 + 1 + 1 by omega]
  rw [run_copy_instruction (value := inputLength) (by rfl) rfl
    (by simp [initialNPOracleState]) harityBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [show (2 : ℕ) ^ inputLength = 1 * 2 ^ inputLength from (one_mul _).symm]
  refine run_fourfoldAtomCountLoop maximumBits rowCount inputLength 1 _ rfl ?_
    ?_ ?_ harityBits hstepBits hloopOutputBits
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]

/-! ## §2 The linked atom counter -/

/-- **The atom counter.**  One link-time row counter on the typed envelope,
followed by the fixed cube loop and the existing bit-serial multiplier. -/
def fourfoldRangeAtomCountProgram (rowCountProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms rowCountProgram
    (linkPrograms fourfoldAtomCountPairProgram bitSerialMulProgram)

theorem fourfoldRangeAtomCountProgram_oracleFree
    (rowCountProgram : NPOracleProgram)
    (hrowCount : OracleFree rowCountProgram) :
    OracleFree (fourfoldRangeAtomCountProgram rowCountProgram) :=
  oracleFree_linkPrograms hrowCount
    (oracleFree_linkPrograms fourfoldAtomCountPairProgram_oracleFree
      bitSerialMulProgram_oracleFree)

def fourfoldRangeAtomCountBits
    (rowCountBits inputLength rowCount : ℕ) : ℕ :=
  max rowCountBits
    (max (fourfoldAtomCountPairBits rowCount inputLength)
      (bitSerialMulBits inputLength rowCount (2 ^ inputLength)))

def fourfoldRangeAtomCountFuel (inputLength rowCountFuel : ℕ) : ℕ :=
  linkFuel (linkPrograms fourfoldAtomCountPairProgram bitSerialMulProgram)
    rowCountFuel
    (linkFuel bitSerialMulProgram (fourfoldAtomCountPairFuel inputLength)
      (bitSerialMulFuel (2 ^ inputLength)))

/-- **The atom counter, executed.**  Given one exact interpreter run of the
row counter on the typed envelope, the linked program returns exactly the
row-major atom count of that request. -/
theorem run_fourfoldRangeAtomCountProgram
    (rowCountProgram : NPOracleProgram)
    (inputLength envelopeCode rowCount rowCountBits rowCountFuel
      maximumBits : ℕ)
    (hbits :
      fourfoldRangeAtomCountBits rowCountBits inputLength rowCount ≤
        maximumBits)
    (hrowCount :
      runNPOracleProgram rowCountProgram rowCountBits rowCountFuel
          (initialNPOracleState inputLength envelopeCode) =
        some rowCount) :
    runNPOracleProgram (fourfoldRangeAtomCountProgram rowCountProgram)
        maximumBits (fourfoldRangeAtomCountFuel inputLength rowCountFuel)
        (initialNPOracleState inputLength envelopeCode) =
      some (rowCount * 2 ^ inputLength) := by
  have hrowCountBits : rowCountBits ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hpairBits :
      fourfoldAtomCountPairBits rowCount inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hmulBits :
      bitSerialMulBits inputLength rowCount (2 ^ inputLength) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hcubeBits : natBitLength (2 ^ inputLength) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair rowCount (2 ^ inputLength))).trans hpairBits
  have harityBits : natBitLength inputLength ≤ maximumBits :=
    (natBitLength_mono (Nat.lt_two_pow_self).le).trans hcubeBits
  have hpositive : 1 ≤ maximumBits :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans harityBits
  have hpair :
      runNPOracleProgram fourfoldAtomCountPairProgram maximumBits
          (fourfoldAtomCountPairFuel inputLength)
          (initialNPOracleState inputLength rowCount) =
        some (bitSerialMulInput rowCount (2 ^ inputLength)) :=
    run_fourfoldAtomCountPairProgram inputLength rowCount maximumBits hpairBits
  have hmul :
      runNPOracleProgram bitSerialMulProgram maximumBits
          (bitSerialMulFuel (2 ^ inputLength))
          (initialNPOracleState inputLength
            (bitSerialMulInput rowCount (2 ^ inputLength))) =
        some (rowCount * 2 ^ inputLength) :=
    run_bits_mono
      (run_bitSerialMulProgram inputLength rowCount (2 ^ inputLength))
      hmulBits
  exact run_linkPrograms hpositive harityBits
    (run_bits_mono hrowCount hrowCountBits)
    (run_linkPrograms hpositive harityBits hpair hmul)

/-! ## §3 The two published specializations

These are exactly the `hcount` premises of
`run_sharedFourfoldAggregationProgram_symmetric` and
`…_threshold`, with the remaining obligation reduced to the row count of one
published family. -/

/-- **The discharged `hcount` premise, symmetric case.** -/
theorem run_symmetricFourfoldRangeAtomCountProgram_of_rowCount
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowCountProgram : NPOracleProgram)
    (rowCountBits rowCountFuel maximumBits : ℕ)
    (hbits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        maximumBits)
    (hrowCount :
      runNPOracleProgram rowCountProgram rowCountBits rowCountFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request)) :
    runNPOracleProgram (fourfoldRangeAtomCountProgram rowCountProgram)
        maximumBits (fourfoldRangeAtomCountFuel request.q rowCountFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_fourfoldRangeAtomCountProgram rowCountProgram request.q
    (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
      encodeNormalizedSymmetricThresholdCircuit request)
    ((publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
      request)
    rowCountBits rowCountFuel maximumBits hbits hrowCount

/-- **The discharged `hcount` premise, threshold case.** -/
theorem run_thresholdFourfoldRangeAtomCountProgram_of_rowCount
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowCountProgram : NPOracleProgram)
    (rowCountBits rowCountFuel maximumBits : ℕ)
    (hbits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedThresholdRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        maximumBits)
    (hrowCount :
      runNPOracleProgram rowCountProgram rowCountBits rowCountFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request)) =
        some
          ((publishedThresholdRows contracts liveScale
            accuracyExponent).rowCount request)) :
    runNPOracleProgram (fourfoldRangeAtomCountProgram rowCountProgram)
        maximumBits (fourfoldRangeAtomCountFuel request.q rowCountFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) =
      some
        (fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :=
  run_fourfoldRangeAtomCountProgram rowCountProgram request.q
    (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
      encodeNormalizedThresholdThresholdCircuit request)
    ((publishedThresholdRows contracts liveScale accuracyExponent).rowCount
      request)
    rowCountBits rowCountFuel maximumBits hbits hrowCount

end NearCubicWires.CanonicalFourfoldRowCountProgram
