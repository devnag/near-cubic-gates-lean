import Proof.Supplier.SelectiveCountCasesRun
import Batteries.Tactic.OpenPrivate

/-!
# The tagged reverse pass at an arbitrary entry state

`structuralTaggedReverseProgram` is the `11`-instruction stream every scheduler
calls to turn its private reverse spine back into forward order.  It is
published only at `initialNPOracleState`, but a relocated call starts on
whatever registers the previous call left in the callee's frame, so callers one
level up need it at an arbitrary entry.

The controller reads register `7` once, at the loop's back edge, and that
instruction branches to the same target either way; the run is therefore entry
independent, and this module says so once and for all.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

open private structuralTaggedReverseProgram structuralTaggedReverseFuel
  structuralTaggedReverseBits encodeTaggedList_suffix_le from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

set_option maxHeartbeats 800000 in
-- Eight steps per retained entry; the back edge's branch register is read but
-- never decides, so no hypothesis about it is needed.
private theorem run_structuralTaggedReverseLoop_anyEntry
    (remaining processed : List ℕ) (maximumBits : ℕ) (machine : NPOracleState)
    (hpc : machine.pc = 1)
    (hremaining : machine.registers 0 = encodeTaggedList remaining)
    (hprocessed : machine.registers 2 = encodeTaggedList processed)
    (hremainingBits :
      natBitLength (encodeTaggedList remaining) ≤ maximumBits)
    (hfinalBits :
      natBitLength (encodeTaggedList (remaining.reverse ++ processed)) ≤
        maximumBits) :
    runNPOracleProgram structuralTaggedReverseProgram maximumBits
        (8 * remaining.length + 3) machine =
      some (encodeTaggedList (remaining.reverse ++ processed)) := by
  induction remaining generalizing processed machine with
  | nil =>
      rw [show 8 * ([] : List ℕ).length + 3 = 2 + 1 by rfl]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [show machine.registers 0 = 0 by
          simpa [encodeTaggedList] using hremaining, if_pos rfl]
      rw [run_copy_instruction (value := encodeTaggedList processed)
        (by rfl) rfl
        (by simpa [NPOracleState.jump] using hprocessed)
        (by simpa using hfinalBits)]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simpa using hfinalBits)
  | cons value rest inductionHypothesis =>
      have hpayloadBits :
          natBitLength (Nat.pair value (encodeTaggedList rest)) ≤
            maximumBits := by
        refine (natBitLength_mono
          (Nat.right_le_pair 1 (Nat.pair value (encodeTaggedList rest)))).trans ?_
        simpa [encodeTaggedList] using hremainingBits
      have hvalueBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono
          (Nat.left_le_pair value (encodeTaggedList rest))).trans hpayloadBits
      have hrestBits : natBitLength (encodeTaggedList rest) ≤ maximumBits :=
        (natBitLength_mono
          (Nat.right_le_pair value (encodeTaggedList rest))).trans hpayloadBits
      have hnextBits :
          natBitLength (encodeTaggedList (value :: processed)) ≤
            maximumBits := by
        refine (natBitLength_mono
          (encodeTaggedList_suffix_le rest.reverse (value :: processed))).trans ?_
        simpa using hfinalBits
      have hinnerBits :
          natBitLength (Nat.pair value (encodeTaggedList processed)) ≤
            maximumBits := by
        refine (natBitLength_mono
          (Nat.right_le_pair 1
            (Nat.pair value (encodeTaggedList processed)))).trans ?_
        simpa [encodeTaggedList] using hnextBits
      have honeBits : natBitLength 1 ≤ maximumBits := by
        refine (natBitLength_mono
          (Nat.left_le_pair 1
            (Nat.pair value (encodeTaggedList processed)))).trans ?_
        simpa [encodeTaggedList] using hnextBits
      rw [show 8 * (value :: rest).length + 3 = 8 * rest.length + 10 + 1 by
        simp
        omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [show machine.registers 0 =
          Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) by
            simpa [encodeTaggedList] using hremaining,
        if_neg (by
          have hleft :=
            Nat.left_le_pair 1 (Nat.pair value (encodeTaggedList rest))
          omega)]
      rw [show 8 * rest.length + 10 = 8 * rest.length + 9 + 1 by omega]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (encodeTaggedList rest))
        (by rfl) rfl
        (by simp [NPOracleState.jump, hremaining, encodeTaggedList])
        hpayloadBits]
      rw [show 8 * rest.length + 9 = 8 * rest.length + 8 + 1 by omega]
      rw [run_unpairLeft_instruction (value := value) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [show 8 * rest.length + 8 = 8 * rest.length + 7 + 1 by omega]
      rw [run_unpairRight_instruction (value := encodeTaggedList rest)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hrestBits]
      rw [show 8 * rest.length + 7 = 8 * rest.length + 6 + 1 by omega]
      rw [run_pair_instruction
        (value := Nat.pair value (encodeTaggedList processed))
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hprocessed])
        hinnerBits]
      rw [show 8 * rest.length + 6 = 8 * rest.length + 5 + 1 by omega]
      rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
      rw [show 8 * rest.length + 5 = 8 * rest.length + 4 + 1 by omega]
      rw [run_pair_instruction
        (value := encodeTaggedList (value :: processed))
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
        hnextBits]
      rw [show 8 * rest.length + 4 = 8 * rest.length + 3 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      simp only [ite_self]
      rw [show (value :: rest).reverse ++ processed =
        rest.reverse ++ (value :: processed) by simp]
      refine inductionHypothesis (value :: processed) _ rfl ?_ ?_ hrestBits ?_
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simpa using hfinalBits

/-- **The tagged reverse pass at an arbitrary entry state.**  The
`11`-instruction stream started anywhere with the encoded spine in register
zero returns the same list in forward order, with the published resources. -/
theorem run_structuralTaggedReverseProgram_anyEntry (values : List ℕ)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput : entry.registers 0 = encodeTaggedList values) :
    runNPOracleProgram structuralTaggedReverseProgram
        (structuralTaggedReverseBits values)
        (structuralTaggedReverseFuel values) entry =
      some (encodeTaggedList values.reverse) := by
  have hinputBits :
      natBitLength (encodeTaggedList values) ≤
        structuralTaggedReverseBits values :=
    natBitLength_mono
      (Nat.left_le_pair (encodeTaggedList values)
        (encodeTaggedList values.reverse))
  have houtputBits :
      natBitLength (encodeTaggedList values.reverse) ≤
        structuralTaggedReverseBits values :=
    natBitLength_mono
      (Nat.right_le_pair (encodeTaggedList values)
        (encodeTaggedList values.reverse))
  rw [show structuralTaggedReverseFuel values = 8 * values.length + 3 + 1 by
    simp [structuralTaggedReverseFuel]]
  rw [run_set_instruction (value := 0) (by rfl) hentryPc
    (by
      unfold structuralTaggedReverseBits
      exact natBitLength_mono (Nat.zero_le _))]
  simpa using
    run_structuralTaggedReverseLoop_anyEntry values []
      (structuralTaggedReverseBits values) ((entry.write 2 0).jump 1) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hentryInput])
      (by simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
      hinputBits (by simpa using houtputBits)

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
