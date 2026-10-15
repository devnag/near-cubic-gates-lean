import Proof.Supplier.SelectiveClauseLeafEntry

/-!
# Level 12 of the nested structural compiler: the projected address evaluator

`structuralAddressProgram` is the `276`-instruction stream that evaluates one
complete projected query address.  Its `28`-instruction controller carries no
selective compiler state at all: it walks a row-major table cursor once per
address bit, imports the projection code stored at that cursor with the private
tagged lookup, interprets it with the published projected-bit program, and
accumulates the results little-endian against a doubling place value.

`SelectiveClauseRun` §5 already identifies that accumulation with the source
compiler's `projectionTableAddress`
(`structuralAddressFold_eq_projectionTableAddress`), and `SelectiveClauseRun` §6
runs the tagged lookup from an arbitrary entry state.  The only remaining
obligation was the published projected-bit evaluator on a relocated frame, and
`SelectiveClauseLeafEntry` §2 discharges it outright.  This module therefore
closes level 12: `structuralAddressRunner` has no premise at all.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

open private structuralAddressProgram structuralAddressControllerProgram
  structuralAddressControllerProgram_length structuralAddressInput
  structuralTaggedLookupProgram structuralTaggedLookupInput
  structuralTaggedLookupFuel structuralTaggedLookupBits
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The imported projection code at one cursor -/

/-- The projection code the controller imports at one row-major cursor. -/
private def structuralAddressCode (outputs : List ℕ) (cursor : ℕ) : ℕ :=
  projectionRawOutput (outputs.getD cursor 0)

private theorem structuralAddressBit_eq_projectedRandomBitOutput
    (outputs : List ℕ) (width randomnessCode cursor : ℕ) :
    structuralAddressBit outputs width randomnessCode cursor =
      projectedRandomBitOutput width (structuralAddressCode outputs cursor)
        randomnessCode := rfl

/-! ## 2. The loop's register-width envelope and clock

The controller's per-bit block writes the lookup request, the imported code, the
projected-bit request, the returned bit, the doubled place value, the updated
accumulator and the advanced cursor.  Both envelopes below follow exactly the
recursion of `structuralAddressFold`. -/

/-- Register width of one address bit: the two relocated calls and every value
the controller writes around them. -/
private def structuralAddressStepBits
    (outputs : List ℕ) (width randomnessCode cursor : ℕ) : ℕ :=
  max (structuralTaggedLookupBits outputs cursor) <|
    max (natBitLength (Nat.pair 0 (outputs.getD cursor 0))) <|
      max
        (natBitLength
          (Nat.pair (structuralAddressCode outputs cursor) randomnessCode)) <|
        max
          (natBitLength
            (projectedRandomBitInput width
              (structuralAddressCode outputs cursor) randomnessCode)) <|
          max
            (projectedRandomBitBits 0 width
              (structuralAddressCode outputs cursor) randomnessCode)
            (natBitLength
              (Nat.pair 0
                (structuralAddressBit outputs width randomnessCode cursor)))

/-- Register width of the whole little-endian accumulation. -/
private def structuralAddressLoopBits
    (outputs : List ℕ) (width randomnessCode : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, place, accumulated, _cursor =>
      max (natBitLength place) (natBitLength accumulated)
  | count + 1, place, accumulated, cursor =>
      max (structuralAddressStepBits outputs width randomnessCode cursor) <|
        max (natBitLength place) <|
          max (natBitLength accumulated) <|
            max (natBitLength (cursor + 1)) <|
              structuralAddressLoopBits outputs width randomnessCode count
                (place + place)
                (accumulated +
                  (if structuralAddressBit outputs width randomnessCode cursor =
                      0 then 0 else place))
                (cursor + 1)

private theorem structuralAddressLoopBits_place (outputs : List ℕ)
    (width randomnessCode : ℕ) :
    ∀ (count place accumulated cursor : ℕ),
      natBitLength place ≤
        structuralAddressLoopBits outputs width randomnessCode count place
          accumulated cursor := by
  intro count place accumulated cursor
  cases count with
  | zero =>
      exact Nat.le_max_left _ _
  | succ count =>
      rw [structuralAddressLoopBits]
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

private theorem structuralAddressLoopBits_accumulated (outputs : List ℕ)
    (width randomnessCode : ℕ) :
    ∀ (count place accumulated cursor : ℕ),
      natBitLength accumulated ≤
        structuralAddressLoopBits outputs width randomnessCode count place
          accumulated cursor := by
  intro count place accumulated cursor
  cases count with
  | zero =>
      exact Nat.le_max_right _ _
  | succ count =>
      rw [structuralAddressLoopBits]
      exact ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
        (Nat.le_max_right _ _)

/-- Interpreter fuel of the whole little-endian accumulation: four controller
steps into the tagged lookup, six more into the projected-bit evaluator and
seven closing the bit. -/
private def structuralAddressLoopFuel
    (outputs : List ℕ) (width randomnessCode : ℕ) : ℕ → ℕ → ℕ
  | 0, _cursor => 3
  | count + 1, cursor =>
      4 +
        (structuralTaggedLookupFuel cursor +
          (6 +
            (projectedRandomBitFuel width (structuralAddressCode outputs cursor)
                randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))))

/-! ## 3. The accumulation loop -/

set_option maxHeartbeats 1600000 in
-- Two relocated calls per iteration, each with its own width ledger re-derived
-- at the callee's advertised envelope, exceed the default budget.
private theorem run_structuralAddressLoop (outputs : List ℕ)
    (width randomnessCode maximumBits : ℕ) :
    ∀ (count place accumulated cursor : ℕ) (machine : NPOracleState),
      machine.pc = 9 →
      natBitLength count ≤ maximumBits →
      structuralAddressLoopBits outputs width randomnessCode count place
          accumulated cursor ≤
        maximumBits →
      machine.registers 2 = encodeTaggedList outputs →
      machine.registers 4 = width →
      machine.registers 6 = randomnessCode →
      machine.registers 7 = cursor →
      machine.registers 8 = count →
      machine.registers 10 = place →
      machine.registers 11 = accumulated →
      runNPOracleProgram structuralAddressProgram maximumBits
          (structuralAddressLoopFuel outputs width randomnessCode count cursor)
          machine =
        some
          (structuralAddressFold outputs width randomnessCode count place
            accumulated cursor) := by
  intro count
  induction count with
  | zero =>
      intro place accumulated cursor machine hpc _hcountBits hbits _htable
        _hwidth _hrandomness _hcursor hcount _hplace haccumulated
      have haccumulatedBits : natBitLength accumulated ≤ maximumBits :=
        (structuralAddressLoopBits_accumulated outputs width randomnessCode 0
          place accumulated cursor).trans hbits
      have hfoldZero :
          structuralAddressFold outputs width randomnessCode 0 place accumulated
              cursor = accumulated := rfl
      rw [hfoldZero]
      rw [show structuralAddressLoopFuel outputs width randomnessCode 0 cursor =
        ((0 + 1) + 1) + 1 by rfl]
      rw [run_branchZero_instruction
        (structuralAddressProgram_controllerAt (pc := 9) rfl) hpc]
      rw [if_pos (by rw [hcount])]
      rw [run_copy_instruction (value := accumulated)
        (structuralAddressProgram_controllerAt (pc := 26) rfl) rfl
        (by simp [NPOracleState.jump, haccumulated]) haccumulatedBits]
      exact run_halt_instruction (fuel := 0)
        (structuralAddressProgram_controllerAt (pc := 27) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) haccumulatedBits
  | succ count inductionHypothesis =>
      intro place accumulated cursor machine hpc hcountBits hbits htable hwidth
        hrandomness hcursor hcount hplace haccumulated
      have hcountDownBits : natBitLength count ≤ maximumBits :=
        (decrement_bits_le (count + 1)).trans hcountBits
      rw [structuralAddressLoopBits] at hbits
      have hstepBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hplaceBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have haccumulatedBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
      have hcursorSuccBits := (Nat.le_max_left _ _).trans hbitsThree
      have hrecBits := (Nat.le_max_right _ _).trans hbitsThree
      rw [structuralAddressStepBits] at hstepBits
      have hlookupBits := (Nat.le_max_left _ _).trans hstepBits
      have hstepOne := (Nat.le_max_right _ _).trans hstepBits
      have hlookupPairBits := (Nat.le_max_left _ _).trans hstepOne
      have hstepTwo := (Nat.le_max_right _ _).trans hstepOne
      have hcodePairBits := (Nat.le_max_left _ _).trans hstepTwo
      have hstepThree := (Nat.le_max_right _ _).trans hstepTwo
      have hprojectedInputBits := (Nat.le_max_left _ _).trans hstepThree
      have hstepFour := (Nat.le_max_right _ _).trans hstepThree
      have hprojectedBits := (Nat.le_max_left _ _).trans hstepFour
      have hprojectedPairBits := (Nat.le_max_right _ _).trans hstepFour
      have hrequestBits :
          natBitLength
              (structuralTaggedLookupInput (encodeTaggedList outputs) cursor) ≤
            maximumBits := hlookupBits
      have hvalueBits : natBitLength (outputs.getD cursor 0) ≤ maximumBits :=
        natBitLength_pair_right hlookupPairBits
      have hcodeBits :
          natBitLength (structuralAddressCode outputs cursor) ≤ maximumBits :=
        (natBitLength_mono
          (Nat.unpair_left_le (outputs.getD cursor 0))).trans hvalueBits
      have hbitBits :
          natBitLength
              (structuralAddressBit outputs width randomnessCode cursor) ≤
            maximumBits :=
        natBitLength_pair_right hprojectedPairBits
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le _)).trans hcodeBits
      have hnextPlaceBits : natBitLength (place + place) ≤ maximumBits :=
        (structuralAddressLoopBits_place outputs width randomnessCode count
          (place + place) _ (cursor + 1)).trans hrecBits
      have hfold :
          structuralAddressFold outputs width randomnessCode (count + 1) place
              accumulated cursor =
            structuralAddressFold outputs width randomnessCode count
              (place + place)
              (accumulated +
                (if structuralAddressBit outputs width randomnessCode cursor = 0
                  then 0 else place))
              (cursor + 1) := rfl
      rw [hfold]
      rw [structuralAddressLoopFuel]
      rw [show 4 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1))))) =
        (3 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1)))))) + 1 by omega]
      rw [run_branchZero_instruction
        (structuralAddressProgram_controllerAt (pc := 9) rfl) hpc]
      rw [if_neg (by rw [hcount]; omega)]
      rw [show 3 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1))))) =
        (2 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1)))))) + 1 by omega]
      rw [run_pair_instruction
        (value := structuralTaggedLookupInput (encodeTaggedList outputs) cursor)
        (structuralAddressProgram_controllerAt (pc := 10) rfl) rfl
        (by
          simp [NPOracleState.jump, htable, hcursor, structuralTaggedLookupInput])
        hrequestBits]
      rw [show 2 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1))))) =
        (1 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1)))))) + 1 by omega]
      rw [run_set_instruction
        (structuralAddressProgram_controllerAt (pc := 11) rfl) rfl hzeroBits]
      rw [show 1 +
          (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1))))) =
        (structuralTaggedLookupFuel cursor +
            (6 +
              (projectedRandomBitFuel width
                  (structuralAddressCode outputs cursor) randomnessCode +
                (7 +
                  structuralAddressLoopFuel outputs width randomnessCode count
                    (cursor + 1))))) + 1 by omega]
      rw [run_branchZero_instruction
        (structuralAddressProgram_controllerAt (pc := 12) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveRelocatedCall
        (source := structuralTaggedLookupProgram)
        (calleeOutput := outputs.getD cursor 0)
        structuralAddressProgram_lookupCallable (by omega) rfl ?_ ?_
        hlookupPairBits ?_
      · intro frame hframePc hframeInput
        refine run_bits_mono
          (run_structuralTaggedLookupProgram_anyEntry outputs cursor frame
            hframePc ?_) hlookupBits
        rw [hframeInput]
        simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro lookupHalt
        rw [show 6 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (5 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))) + 1 by omega]
        rw [run_unpairRight_instruction (value := outputs.getD cursor 0)
          (structuralAddressProgram_controllerAt (pc := 13) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
        rw [show 5 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (4 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))) + 1 by omega]
        rw [run_unpairLeft_instruction
          (value := structuralAddressCode outputs cursor)
          (structuralAddressProgram_controllerAt (pc := 14) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump,
              structuralAddressCode, projectionRawOutput])
          hcodeBits]
        rw [show 4 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (3 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))) + 1 by omega]
        rw [run_pair_instruction
          (value :=
            Nat.pair (structuralAddressCode outputs cursor) randomnessCode)
          (structuralAddressProgram_controllerAt (pc := 15) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, relocateState,
              hrandomness])
          hcodePairBits]
        rw [show 3 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (2 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))) + 1 by omega]
        rw [run_pair_instruction
          (value :=
            projectedRandomBitInput width
              (structuralAddressCode outputs cursor) randomnessCode)
          (structuralAddressProgram_controllerAt (pc := 16) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, relocateState, hwidth,
              projectedRandomBitInput])
          hprojectedInputBits]
        rw [show 2 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (1 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)))) + 1 by omega]
        rw [run_set_instruction
          (structuralAddressProgram_controllerAt (pc := 17) rfl) rfl hzeroBits]
        rw [show 1 +
            (projectedRandomBitFuel width
                (structuralAddressCode outputs cursor) randomnessCode +
              (7 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1))) =
          (projectedRandomBitFuel width
              (structuralAddressCode outputs cursor) randomnessCode +
            (7 +
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1))) + 1 by omega]
        rw [run_set_instruction
          (structuralAddressProgram_controllerAt (pc := 18) rfl) rfl hzeroBits]
        refine run_selectiveRelocatedCall_frame
          (source := projectedRandomBitProgram)
          (calleeOutput :=
            structuralAddressBit outputs width randomnessCode cursor)
          structuralAddressProgram_projectedBitCallable (by omega) rfl ?_ ?_
          hprojectedPairBits ?_
        · intro entry hentryPc hentryInput hentryLength
          rw [structuralAddressBit_eq_projectedRandomBitOutput]
          refine run_bits_mono
            (run_projectedRandomBitProgram_anyEntry 0 width
              (structuralAddressCode outputs cursor) randomnessCode entry
              hentryPc ?_ ?_) hprojectedBits
          · rw [hentryInput]
            simp [NPOracleState.write, NPOracleState.jump]
          · have hzeroSlot : entry.registers 1 = 0 := by
              rw [hentryLength]
              simp [NPOracleState.write, NPOracleState.jump]
            rw [hzeroSlot]
            exact Nat.le_max_left _ _
        · simp [NPOracleState.write, NPOracleState.jump]
        · intro projectedHalt
          rw [show 7 +
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1) =
            (6 +
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1)) + 1 by omega]
          rw [run_unpairRight_instruction
            (value := structuralAddressBit outputs width randomnessCode cursor)
            (structuralAddressProgram_controllerAt (pc := 19) rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump]) hbitBits]
          rw [show 6 +
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1) =
            (5 +
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1)) + 1 by omega]
          rw [run_branchZero_instruction
            (structuralAddressProgram_controllerAt (pc := 20) rfl) rfl]
          by_cases hbit :
              structuralAddressBit outputs width randomnessCode cursor = 0
          · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump, hbit])]
            rw [if_pos hbit, Nat.add_zero]
            rw [show 5 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (4 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_add_instruction (value := place + place)
              (structuralAddressProgram_controllerAt (pc := 22) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hplace])
              hnextPlaceBits]
            rw [show 4 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (3 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_increment_instruction (value := cursor + 1)
              (structuralAddressProgram_controllerAt (pc := 23) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hcursor])
              hcursorSuccBits]
            rw [show 3 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (2 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_decrement_instruction (value := count)
              (structuralAddressProgram_controllerAt (pc := 24) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hcount])
              hcountDownBits]
            rw [show 2 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (1 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_branchZero_instruction
              (structuralAddressProgram_controllerAt (pc := 25) rfl) rfl]
            simp only [ite_self]
            rw [show 1 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1) + 1 by omega]
            refine run_fuel_add
              (inductionHypothesis (place + place) accumulated (cursor + 1) _ rfl
                hcountDownBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) 1
            · rw [if_pos hbit, Nat.add_zero] at hrecBits
              exact hrecBits
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using htable
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using hwidth
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using hrandomness
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using haccumulated
          · rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump, hbit])]
            rw [if_neg hbit]
            have hnextAccumulatedBits :
                natBitLength (accumulated + place) ≤ maximumBits := by
              refine (structuralAddressLoopBits_accumulated outputs width
                randomnessCode count (place + place) (accumulated + place)
                (cursor + 1)).trans ?_
              rw [if_neg hbit] at hrecBits
              exact hrecBits
            rw [show 5 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (4 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_add_instruction (value := accumulated + place)
              (structuralAddressProgram_controllerAt (pc := 21) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hplace, haccumulated])
              hnextAccumulatedBits]
            rw [show 4 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (3 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_add_instruction (value := place + place)
              (structuralAddressProgram_controllerAt (pc := 22) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hplace])
              hnextPlaceBits]
            rw [show 3 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (2 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_increment_instruction (value := cursor + 1)
              (structuralAddressProgram_controllerAt (pc := 23) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hcursor])
              hcursorSuccBits]
            rw [show 2 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              (1 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1)) + 1 by omega]
            rw [run_decrement_instruction (value := count)
              (structuralAddressProgram_controllerAt (pc := 24) rfl) rfl
              (by
                simp [NPOracleState.write, NPOracleState.jump, relocateState,
                  hcount])
              hcountDownBits]
            rw [show 1 +
                structuralAddressLoopFuel outputs width randomnessCode count
                  (cursor + 1) =
              structuralAddressLoopFuel outputs width randomnessCode count
                (cursor + 1) + 1 by omega]
            rw [run_branchZero_instruction
              (structuralAddressProgram_controllerAt (pc := 25) rfl) rfl]
            simp only [ite_self]
            refine inductionHypothesis (place + place) (accumulated + place)
              (cursor + 1) _ rfl hcountDownBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · rw [if_neg hbit] at hrecBits
              exact hrecBits
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using htable
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using hwidth
            · simpa [NPOracleState.write, NPOracleState.jump, relocateState]
                using hrandomness
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 4. The whole `276`-instruction stream -/

/-- Register width of one whole projected-address evaluation. -/
def structuralAddressRunBits (outputs : List ℕ)
    (width randomnessCode query : ℕ) : ℕ :=
  max
    (natBitLength
      (structuralAddressInput (encodeTaggedList outputs) width randomnessCode
        (projectionQueryOffset width query 0)))
    (structuralAddressLoopBits outputs width randomnessCode width 1 0
      (projectionQueryOffset width query 0))

/-- Interpreter fuel of one whole projected-address evaluation. -/
def structuralAddressRunFuel (outputs : List ℕ)
    (width randomnessCode query : ℕ) : ℕ :=
  9 +
    structuralAddressLoopFuel outputs width randomnessCode width
      (projectionQueryOffset width query 0)

set_option maxHeartbeats 1600000 in
-- The nine-step request parser re-derives the whole width ledger from the
-- request alone, so the ledger exceeds the default budget.
/-- **Level 12's run.**  The `276`-instruction address evaluator started on its
own ABI frame, at any entry registers, returns exactly the source compiler's
projected query address. -/
theorem run_structuralAddressProgram (outputs : List ℕ)
    (width query randomnessCode : ℕ) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        structuralAddressInput (encodeTaggedList outputs) width randomnessCode
          (projectionQueryOffset width query 0)) :
    runNPOracleProgram structuralAddressProgram
        (structuralAddressRunBits outputs width randomnessCode query)
        (structuralAddressRunFuel outputs width randomnessCode query) entry =
      some
        (encodeBitInput
          (projectionTableAddress outputs width query
            (tableRandomness width randomnessCode))) := by
  have hrequestBits :
      natBitLength
          (structuralAddressInput (encodeTaggedList outputs) width randomnessCode
            (projectionQueryOffset width query 0)) ≤
        structuralAddressRunBits outputs width randomnessCode query :=
    Nat.le_max_left _ _
  have hloopBits :
      structuralAddressLoopBits outputs width randomnessCode width 1 0
          (projectionQueryOffset width query 0) ≤
        structuralAddressRunBits outputs width randomnessCode query :=
    Nat.le_max_right _ _
  have hflat := hrequestBits
  simp only [structuralAddressInput] at hflat
  have htableBits := natBitLength_pair_left hflat
  have hfieldOne := natBitLength_pair_right hflat
  have hwidthBits := natBitLength_pair_left hfieldOne
  have hfieldTwo := natBitLength_pair_right hfieldOne
  have hrandomnessBits := natBitLength_pair_left hfieldTwo
  have hoffsetBits := natBitLength_pair_right hfieldTwo
  have honeBits :
      natBitLength 1 ≤ structuralAddressRunBits outputs width randomnessCode
        query :=
    (structuralAddressLoopBits_place outputs width randomnessCode width 1 0
      (projectionQueryOffset width query 0)).trans hloopBits
  have hzeroBits :
      natBitLength 0 ≤ structuralAddressRunBits outputs width randomnessCode
        query :=
    (structuralAddressLoopBits_accumulated outputs width randomnessCode width 1 0
      (projectionQueryOffset width query 0)).trans hloopBits
  rw [← structuralAddressFold_eq_projectionTableAddress outputs width query
    randomnessCode]
  rw [structuralAddressRunFuel]
  rw [show 9 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (8 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairLeft_instruction (value := encodeTaggedList outputs)
    (structuralAddressProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, structuralAddressInput]) htableBits]
  rw [show 8 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (7 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair width
        (Nat.pair randomnessCode (projectionQueryOffset width query 0)))
    (structuralAddressProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        structuralAddressInput])
    hfieldOne]
  rw [show 7 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (6 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (structuralAddressProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 6 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (5 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair randomnessCode (projectionQueryOffset width query 0))
    (structuralAddressProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldTwo]
  rw [show 5 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (4 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (structuralAddressProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrandomnessBits]
  rw [show 4 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (3 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := projectionQueryOffset width query 0)
    (structuralAddressProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hoffsetBits]
  rw [show 3 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (2 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_copy_instruction (value := width)
    (structuralAddressProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 2 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    (1 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0)) + 1 by omega]
  rw [run_set_instruction
    (structuralAddressProgram_controllerAt (pc := 7) rfl) rfl honeBits]
  rw [show 1 +
      structuralAddressLoopFuel outputs width randomnessCode width
        (projectionQueryOffset width query 0) =
    structuralAddressLoopFuel outputs width randomnessCode width
      (projectionQueryOffset width query 0) + 1 by omega]
  rw [run_set_instruction
    (structuralAddressProgram_controllerAt (pc := 8) rfl) rfl hzeroBits]
  refine run_structuralAddressLoop outputs width randomnessCode _ width 1 0
    (projectionQueryOffset width query 0) _ rfl hwidthBits hloopBits ?_ ?_ ?_ ?_
    ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump]

/-! ## 5. The level premise, discharged -/

/-- **`StructuralAddressRunner`, discharged.**  Level 12 owes nothing: the whole
address evaluator runs at its own ABI frame for every table, every row width and
every query, with no premise at all. -/
def structuralAddressRunner (outputs : List ℕ) (width : ℕ) :
    StructuralAddressRunner outputs width where
  bits := fun query randomnessCode =>
    structuralAddressRunBits outputs width randomnessCode query
  fuel := fun query randomnessCode =>
    structuralAddressRunFuel outputs width randomnessCode query
  executes := by
    intro query randomnessCode entry hentryPc hentryInput
    exact run_structuralAddressProgram outputs width query randomnessCode entry
      hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
