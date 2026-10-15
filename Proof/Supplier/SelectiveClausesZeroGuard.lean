import Proof.Supplier.SelectiveClausesLevelRun

/-!
# The zero-arity clauses ABI branch

The published clauses stream is intentionally left untouched.  This module
certifies the one missing ABI case as a short same-register prefix followed by
an ordinary relocation of the already verified selective emitter.
-/

namespace NearCubicWires.TotalSelectiveClausesGuardedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveClausesInput
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-- The zero-arity branch ignores the decoded clause payload, recovers the
selective state code from the public request, and emits the structural `true`
node through the already verified append microkernel. -/
def selectiveClausesZeroProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .set 3 (Nat.pair 0 1) 2
  , .pair 2 3 0 3
  ] ++ selectiveEmitProgram.map (relocateInstruction 3 0)

private theorem selectiveClausesZeroProgram_emitAt :
    ProgramRelocatedAt selectiveClausesZeroProgram selectiveEmitProgram 3 0 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveEmitProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveClausesZeroProgram]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show 3 + pc - 3 = pc by omega, List.getElem?_map, hlookup]
  rfl

@[simp] theorem selectiveClausesZeroProgram_oracleFree :
    OracleFree selectiveClausesZeroProgram := by
  have hsource : containsSAT selectiveEmitProgram = false :=
    (oracleFree_iff_containsSAT_false selectiveEmitProgram).mp
      selectiveEmitProgram_oracleFree
  rw [oracleFree_iff_containsSAT_false]
  simpa [selectiveClausesZeroProgram, containsSAT, List.any_map,
    Function.comp_def] using hsource

def selectiveClausesZeroBits {n : ℕ}
    (state : SelectiveState n) : ℕ :=
  max (natBitLength (selectiveStateCode state)) <|
    max (natBitLength (Nat.pair 0 1)) <|
      max
        (natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected) (Nat.pair 0 1)))
        (selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (Nat.pair 0 1))

def selectiveClausesZeroFuel {n : ℕ}
    (state : SelectiveState n) : ℕ :=
  selectiveEmitFuel (state.target - state.next)
      (selectiveSelectedCode state.selected) + 3

theorem run_selectiveClausesZeroProgram {n : ℕ}
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveClausesInput (selectiveStateCode state) n
          (encodeTaggedList values) 0 decisionCode) :
    runNPOracleProgram selectiveClausesZeroProgram
        (selectiveClausesZeroBits state) (selectiveClausesZeroFuel state) entry =
      some (selectiveWireCode (selectiveConst state true)) := by
  let maximumBits := selectiveClausesZeroBits state
  let emitInput :=
    selectiveEmitInput (state.target - state.next) state.next
      (selectiveSelectedCode state.selected) (Nat.pair 0 1)
  have hstateBits : natBitLength (selectiveStateCode state) ≤ maximumBits :=
    Nat.le_max_left _ _
  have htailBits := (Nat.le_max_right _ _ :
    max (natBitLength (Nat.pair 0 1))
        (max (natBitLength emitInput)
          (selectiveEmitBits (state.target - state.next) state.next
            (selectiveSelectedCode state.selected) (Nat.pair 0 1))) ≤
      maximumBits)
  have hnodeBits : natBitLength (Nat.pair 0 1) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans htailBits
  have hmoreBits := (Nat.le_max_right _ _).trans htailBits
  have hinputBits : natBitLength emitInput ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hmoreBits
  have hemitBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (Nat.pair 0 1) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hmoreBits
  have hemit := run_bits_mono
    (run_selectiveEmitProgram_eq_emit state (.const true) hordered
      { pc := 0
        registers :=
          ((((entry.write 2 (selectiveStateCode state)).jump 1).write 3
              (Nat.pair 0 1)).jump 2).write 0 emitInput |>.registers }
      rfl
      (by
        simp only [emitInput, NPOracleState.write, NPOracleState.jump,
          if_pos, selectiveEmitInput, selectiveStateCode]
        congr 2))
    hemitBits
  rw [show selectiveClausesZeroFuel state =
      (selectiveEmitFuel (state.target - state.next)
        (selectiveSelectedCode state.selected) + 2) + 1 by
    simp [selectiveClausesZeroFuel]]
  rw [run_unpairLeft_instruction
    (program := selectiveClausesZeroProgram)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := selectiveStateCode state)
    (by simp [selectiveClausesZeroProgram]) hentryPc
    (by rw [hentryInput]; simp [selectiveClausesInput]) hstateBits]
  rw [show selectiveEmitFuel (state.target - state.next)
        (selectiveSelectedCode state.selected) + 2 =
      (selectiveEmitFuel (state.target - state.next)
        (selectiveSelectedCode state.selected) + 1) + 1 by omega]
  rw [run_set_instruction
    (program := selectiveClausesZeroProgram)
    (pc := 1) (register := 3) (value := Nat.pair 0 1) (next := 2)
    (by simp [selectiveClausesZeroProgram]) rfl hnodeBits]
  rw [show selectiveEmitFuel (state.target - state.next)
        (selectiveSelectedCode state.selected) + 1 =
      selectiveEmitFuel (state.target - state.next)
        (selectiveSelectedCode state.selected) + 1 by rfl]
  rw [run_pair_instruction
    (program := selectiveClausesZeroProgram)
    (pc := 2) (left := 2) (right := 3) (destination := 0) (next := 3)
    (value := emitInput)
    (by simp [selectiveClausesZeroProgram]) rfl
    (by simp [emitInput, selectiveEmitInput, selectiveStateCode,
      NPOracleState.write, NPOracleState.jump]) hinputBits]
  have hstate :
      ((((((entry.write 2 (selectiveStateCode state)).jump 1).write 3
          (Nat.pair 0 1)).jump 2).write 0 emitInput).jump 3) =
        relocateState 3 0 (fun _ => 0)
          { pc := 0
            registers :=
              ((((entry.write 2 (selectiveStateCode state)).jump 1).write 3
                  (Nat.pair 0 1)).jump 2).write 0 emitInput |>.registers } := by
    cases entry
    simp [NPOracleState.write, NPOracleState.jump, relocateState]
  rw [hstate]
  exact run_relocated (fun _ => 0)
    selectiveClausesZeroProgram_emitAt hemit

end NearCubicWires.TotalSelectiveClausesGuardedProgram
