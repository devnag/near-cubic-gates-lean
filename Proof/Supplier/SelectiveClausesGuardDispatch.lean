import Proof.Supplier.SelectiveClausesGuardRequest

/-!
# Same-register dispatch at the clauses ABI

The eight-instruction prefix saves the exact request, extracts only its
literal arity, and copies the request back before entering a relocated callee.
The generic branch trace below is shared by the zero and positive callees.
-/

namespace NearCubicWires.TotalSelectiveClausesGuardedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveClausesProgram
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

private def selectiveClausesGuardPrefix : NPOracleProgram :=
  [ .copy 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairRight 4 5 4
  , .unpairLeft 5 6 5
  , .branchZero 6 6 7
  , .copy 2 0 8
  , .copy 2 0 (8 + selectiveClausesZeroProgram.length)
  ]

def totalSelectiveClausesProgram : NPOracleProgram :=
  selectiveClausesGuardPrefix ++
    selectiveClausesZeroProgram.map (relocateInstruction 8 0) ++
    selectiveClausesProgram.map
      (relocateInstruction (8 + selectiveClausesZeroProgram.length) 0)

private theorem totalSelectiveClausesProgram_zeroAt :
    ProgramRelocatedAt totalSelectiveClausesProgram
      selectiveClausesZeroProgram 8 0 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveClausesZeroProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [totalSelectiveClausesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map]
    rw [show selectiveClausesGuardPrefix.length = 8 by rfl]
    omega)]
  rw [List.getElem?_append_right (by
    simp [selectiveClausesGuardPrefix])]
  simp only [selectiveClausesGuardPrefix, List.length_cons, List.length_nil]
  rw [show 8 + pc - 8 = pc by omega, List.getElem?_map, hlookup]
  rfl

private theorem totalSelectiveClausesProgram_positiveAt :
    ProgramRelocatedAt totalSelectiveClausesProgram selectiveClausesProgram
      (8 + selectiveClausesZeroProgram.length) 0 := by
  intro pc instruction hlookup
  simp only [totalSelectiveClausesProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map]
    rw [show selectiveClausesGuardPrefix.length = 8 by rfl]
    omega)]
  simp only [selectiveClausesGuardPrefix, List.length_cons, List.length_nil,
    List.length_append, List.length_map]
  rw [show 8 + selectiveClausesZeroProgram.length + pc -
      (8 + selectiveClausesZeroProgram.length) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

set_option maxRecDepth 30000 in
@[simp] theorem totalSelectiveClausesProgram_oracleFree :
    OracleFree totalSelectiveClausesProgram := by
  rfl

private def guardedBranchEntry (entry : NPOracleState)
    (stateCode inputArity valuesCode literalArity decisionCode : ℕ) :
    NPOracleState :=
  let request := totalSelectiveClausesRequest stateCode inputArity valuesCode
    literalArity decisionCode
  { pc := 0
    registers :=
      (((((entry.write 2 request).write 3
        (selectiveClausesGuardTailOne inputArity valuesCode literalArity
          decisionCode)).write 4
        (selectiveClausesGuardTailTwo valuesCode literalArity
          decisionCode)).write 5
        (selectiveClausesGuardTailThree literalArity decisionCode)).write 6
        literalArity).write 0 request |>.registers }

private theorem run_totalSelectiveClausesProgram_branch
    {source : NPOracleProgram}
    (stateCode inputArity valuesCode literalArity decisionCode
      sourceBits sourceFuel output branchPc offset : ℕ)
    (hbranch : (if literalArity = 0 then 6 else 7) = branchPc)
    (hcopy : totalSelectiveClausesProgram[branchPc]? =
      some (.copy 2 0 offset))
    (hat : ProgramRelocatedAt totalSelectiveClausesProgram source offset 0)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        totalSelectiveClausesRequest stateCode inputArity valuesCode
          literalArity decisionCode)
    (hsource : ∀ sourceEntry : NPOracleState, sourceEntry.pc = 0 →
      sourceEntry.registers 0 =
          totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode →
      runNPOracleProgram source sourceBits sourceFuel sourceEntry = some output) :
    runNPOracleProgram totalSelectiveClausesProgram
        (max
          (natBitLength
            (totalSelectiveClausesRequest stateCode inputArity valuesCode
              literalArity decisionCode)) sourceBits)
        (sourceFuel + 7) entry = some output := by
  let request := totalSelectiveClausesRequest stateCode inputArity valuesCode
    literalArity decisionCode
  let tailOne := selectiveClausesGuardTailOne inputArity valuesCode literalArity
    decisionCode
  let tailTwo := selectiveClausesGuardTailTwo valuesCode literalArity
    decisionCode
  let tailThree := selectiveClausesGuardTailThree literalArity decisionCode
  let maximumBits := max (natBitLength request) sourceBits
  have hrequestBits : natBitLength request ≤ maximumBits := Nat.le_max_left _ _
  have htailOneBits : natBitLength tailOne ≤ maximumBits :=
    selectiveClausesGuardTailOne_bits stateCode inputArity valuesCode
      literalArity decisionCode maximumBits hrequestBits
  have htailTwoBits : natBitLength tailTwo ≤ maximumBits :=
    selectiveClausesGuardTailTwo_bits stateCode inputArity valuesCode
      literalArity decisionCode maximumBits hrequestBits
  have htailThreeBits : natBitLength tailThree ≤ maximumBits :=
    selectiveClausesGuardTailThree_bits stateCode inputArity valuesCode
      literalArity decisionCode maximumBits hrequestBits
  have harityBits : natBitLength literalArity ≤ maximumBits :=
    selectiveClausesGuardArity_bits stateCode inputArity valuesCode
      literalArity decisionCode maximumBits hrequestBits
  have hrun :
      runNPOracleProgram source maximumBits sourceFuel
          (guardedBranchEntry entry stateCode inputArity valuesCode literalArity
            decisionCode) = some output :=
    run_bits_mono (newBits := maximumBits)
    (hsource
      (guardedBranchEntry entry stateCode inputArity valuesCode literalArity
        decisionCode) rfl
      (by simp [guardedBranchEntry, NPOracleState.write]))
    (by exact Nat.le_max_right _ _)
  rw [show sourceFuel + 7 = (sourceFuel + 6) + 1 by omega]
  rw [run_copy_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := request)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix])
    hentryPc (by simpa [request] using hentryInput) hrequestBits]
  rw [show sourceFuel + 6 = (sourceFuel + 5) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := tailOne)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix]) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hentryInput, request,
      tailOne]) htailOneBits]
  rw [show sourceFuel + 5 = (sourceFuel + 4) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := tailTwo)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix]) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tailOne, tailTwo])
    htailTwoBits]
  rw [show sourceFuel + 4 = (sourceFuel + 3) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 3) (source := 4) (destination := 5) (next := 4)
    (value := tailThree)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix]) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tailOne, tailTwo,
      tailThree]) htailThreeBits]
  rw [show sourceFuel + 3 = (sourceFuel + 2) + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 4) (source := 5) (destination := 6) (next := 5)
    (value := literalArity)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix]) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tailOne, tailTwo,
      tailThree]) harityBits]
  rw [show sourceFuel + 2 = (sourceFuel + 1) + 1 by omega]
  rw [run_branchZero_instruction
    (program := totalSelectiveClausesProgram)
    (pc := 5) (register := 6) (zeroTarget := 6) (nonzeroTarget := 7)
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix]) rfl]
  simp only [NPOracleState.write, NPOracleState.jump, ite_true]
  rw [hbranch]
  rw [show sourceFuel + 1 = sourceFuel + 1 by rfl]
  rw [run_copy_instruction hcopy rfl
    (by simp) hrequestBits]
  convert run_relocated (fun _ => 0) hat hrun using 1
  cases entry
  simp [guardedBranchEntry, request, tailOne, tailTwo, tailThree,
    NPOracleState.write, NPOracleState.jump, relocateState]

theorem run_totalSelectiveClausesProgram_zero_of_run
    (stateCode inputArity valuesCode decisionCode sourceBits sourceFuel
      output : ℕ) (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        totalSelectiveClausesRequest stateCode inputArity valuesCode 0
          decisionCode)
    (hsource : ∀ sourceEntry : NPOracleState, sourceEntry.pc = 0 →
      sourceEntry.registers 0 =
          totalSelectiveClausesRequest stateCode inputArity valuesCode 0
            decisionCode →
      runNPOracleProgram selectiveClausesZeroProgram sourceBits sourceFuel
        sourceEntry = some output) :
    runNPOracleProgram totalSelectiveClausesProgram
        (max
          (natBitLength
            (totalSelectiveClausesRequest stateCode inputArity valuesCode 0
              decisionCode)) sourceBits)
        (sourceFuel + 7) entry = some output := by
  exact run_totalSelectiveClausesProgram_branch stateCode inputArity valuesCode
    0 decisionCode sourceBits sourceFuel output 6 8 rfl
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix])
    totalSelectiveClausesProgram_zeroAt entry hentryPc hentryInput hsource

theorem run_totalSelectiveClausesProgram_positive_of_run
    (stateCode inputArity valuesCode literalArity decisionCode sourceBits
      sourceFuel output : ℕ) (harity : 0 < literalArity)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        totalSelectiveClausesRequest stateCode inputArity valuesCode
          literalArity decisionCode)
    (hsource : ∀ sourceEntry : NPOracleState, sourceEntry.pc = 0 →
      sourceEntry.registers 0 =
          totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode →
      runNPOracleProgram selectiveClausesProgram sourceBits sourceFuel
        sourceEntry = some output) :
    runNPOracleProgram totalSelectiveClausesProgram
        (max
          (natBitLength
            (totalSelectiveClausesRequest stateCode inputArity valuesCode
              literalArity decisionCode)) sourceBits)
        (sourceFuel + 7) entry = some output := by
  exact run_totalSelectiveClausesProgram_branch stateCode inputArity valuesCode
    literalArity decisionCode sourceBits sourceFuel output 7
    (8 + selectiveClausesZeroProgram.length) (if_neg (Nat.ne_of_gt harity))
    (by simp [totalSelectiveClausesProgram, selectiveClausesGuardPrefix])
    totalSelectiveClausesProgram_positiveAt entry hentryPc hentryInput hsource

end NearCubicWires.TotalSelectiveClausesGuardedProgram
