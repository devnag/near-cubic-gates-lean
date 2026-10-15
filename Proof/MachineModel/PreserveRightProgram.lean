import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.PolynomialClock
import Proof.Foundations.VerifiedLinker

/-!
# Count-preserving program adapter

`preserveRightProgram source` adapts a fixed program from `left ↦ output` to
`pair(left, right) ↦ pair(output, right)`.  It executes `source` exactly once,
keeps the right component outside the source's register span, and proves the
exact fuel and register-width refinement needed by downstream linkers.
-/

namespace NearCubicWires.PreserveRightProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

private def preserveRightLayout (source : NPOracleProgram) : LinkLayout where
  firstSpan := programRegisterSpan source
  secondSpan := 0
  firstBase := 2
  resetBase := source.length + 2
  secondBase := source.length + 2
  secondRegisterBase := programRegisterSpan source
  savedLengthRegister := programRegisterSpan source
  transferRegister := programRegisterSpan source + 1

/-- Run `source` on the left component of a pair and preserve the right
component in the result. -/
def preserveRightProgram (source : NPOracleProgram) : NPOracleProgram :=
  let layout := preserveRightLayout source
  (([.unpairRight 0 layout.savedLengthRegister 1,
      .unpairLeft 0 0 layout.firstBase] ++
    source.map
      (continueInstruction layout.firstBase layout.transferRegister
        layout.resetBase)) ++
  [.pair layout.transferRegister layout.savedLengthRegister 0
      (layout.resetBase + 1),
    .halt 0])

def preserveRightFuel (sourceFuel : ℕ) : ℕ :=
  sourceFuel + 4

def preserveRightBits
    (sourceBits left right output : ℕ) : ℕ :=
  max sourceBits <|
    max
      (natBitLength (Nat.pair left right))
      (natBitLength (Nat.pair output right))

private theorem preserveRight_continued (source : NPOracleProgram) :
    ProgramContinuedAt (preserveRightProgram source) source
      (preserveRightLayout source).firstBase
      (preserveRightLayout source).transferRegister
      (preserveRightLayout source).resetBase := by
  intro pc instruction hlookup
  have hpc : pc < source.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [preserveRightProgram, preserveRightLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 + pc - 2 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem preserveRightState_ext (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem preserveRight_entry
    (source : NPOracleProgram) (inputLength left right : ℕ) :
    let publicState :=
      initialNPOracleState inputLength (Nat.pair left right)
    let saved :=
      (publicState.write
        (preserveRightLayout source).savedLengthRegister right).jump 1
    let parsed :=
      (saved.write 0 left).jump (preserveRightLayout source).firstBase
    parsed =
      firstStageState (preserveRightLayout source) right
        (initialNPOracleState inputLength left) := by
  dsimp only
  apply preserveRightState_ext
  · rfl
  · funext register
    have hspan : 2 ≤ programRegisterSpan source :=
      two_le_programRegisterSpan source
    have hspanNeZero : programRegisterSpan source ≠ 0 := by
      omega
    have hspanNeOne : programRegisterSpan source ≠ 1 := by
      omega
    have hzeroLt : 0 < programRegisterSpan source := by
      omega
    have honeLt : 1 < programRegisterSpan source := by
      omega
    by_cases hzero : register = 0
    · subst register
      simp [firstStageState, preserveRightLayout, initialNPOracleState,
        NPOracleState.write, NPOracleState.jump, hzeroLt]
    · by_cases hone : register = 1
      · subst register
        simp [firstStageState, preserveRightLayout, initialNPOracleState,
          NPOracleState.write, NPOracleState.jump, Ne.symm hspanNeOne,
          honeLt]
      · by_cases hsaved : register = programRegisterSpan source
        · subst register
          simp [firstStageState, preserveRightLayout, initialNPOracleState,
            NPOracleState.write, NPOracleState.jump, hspanNeZero]
        · by_cases hlow : register < programRegisterSpan source
          · simp [firstStageState, preserveRightLayout, initialNPOracleState,
              NPOracleState.write, NPOracleState.jump, hzero, hone, hlow,
              hsaved]
          · simp [firstStageState, preserveRightLayout, initialNPOracleState,
              NPOracleState.write, NPOracleState.jump, hzero, hone, hlow,
              hsaved]

theorem preserveRightProgram_oracleFree
    (source : NPOracleProgram) (hsource : OracleFree source) :
    OracleFree (preserveRightProgram source) := by
  rw [oracleFree_iff_containsSAT_false]
  have hcontains :=
    (oracleFree_iff_containsSAT_false source).mp hsource
  simpa only [containsSAT, preserveRightProgram, List.cons_append,
    List.nil_append, List.any_cons, List.any_append, List.any_map,
    Function.comp_def, containsSAT_continueInstruction, List.any_nil,
    Bool.or_self, Bool.or_false, Bool.false_or, List.any_eq_false,
    Bool.not_eq_true] using hcontains

/-- Exact refinement of the count-preserving adapter.  The public input length
is forwarded to `source`; only the pair representation changes. -/
theorem run_preserveRightProgram
    (source : NPOracleProgram)
    (inputLength sourceBits sourceFuel left right output : ℕ)
    (hsource :
      runNPOracleProgram source sourceBits sourceFuel
          (initialNPOracleState inputLength left) =
        some output) :
    runNPOracleProgram (preserveRightProgram source)
        (preserveRightBits sourceBits left right output)
        (preserveRightFuel sourceFuel)
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair output right) := by
  let maximumBits := preserveRightBits sourceBits left right output
  have hsourceBits : sourceBits ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hinputBits :
      natBitLength (Nat.pair left right) ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtputBits :
      natBitLength (Nat.pair output right) ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hleftBits : natBitLength left ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hinputBits
    exact Nat.left_le_pair left right
  have hrightBits : natBitLength right ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hinputBits
    exact Nat.right_le_pair left right
  have hsourceAtMaximum :
      runNPOracleProgram source maximumBits sourceFuel
          (initialNPOracleState inputLength left) =
        some output := by
    exact run_bits_mono hsource hsourceBits
  have hsavedNeZero :
      (preserveRightLayout source).savedLengthRegister ≠ 0 := by
    have hspan := two_le_programRegisterSpan source
    simp only [preserveRightLayout]
    omega
  rw [show preserveRightFuel sourceFuel =
      ((sourceFuel + 2) + 1) + 1 by
    simp only [preserveRightFuel]]
  rw [run_unpairRight_instruction
    (program := preserveRightProgram source)
    (pc := 0)
    (source := 0)
    (destination := (preserveRightLayout source).savedLengthRegister)
    (next := 1) (value := right)
    (by simp [preserveRightProgram])
    rfl
    (by simp [initialNPOracleState])
    hrightBits]
  let state1 :=
    ((initialNPOracleState inputLength (Nat.pair left right)).write
      (preserveRightLayout source).savedLengthRegister right).jump 1
  rw [run_unpairLeft_instruction
    (program := preserveRightProgram source)
    (pc := 1)
    (source := 0) (destination := 0)
    (next := (preserveRightLayout source).firstBase) (value := left)
    (by simp [preserveRightProgram])
    rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, Ne.symm hsavedNeZero])
    hleftBits]
  let parsed :=
    (state1.write 0 left).jump (preserveRightLayout source).firstBase
  have hentry :
      parsed =
        firstStageState (preserveRightLayout source) right
          (initialNPOracleState inputLength left) := by
    exact preserveRight_entry source inputLength left right
  change
    runNPOracleProgram (preserveRightProgram source)
        maximumBits (sourceFuel + 2) parsed =
      some (Nat.pair output right)
  rw [hentry]
  apply run_continued
    (preserveRight_continued source)
    (le_refl (programRegisterSpan source))
    hsourceAtMaximum
  intro haltState unused
  rw [show unused + 2 = (unused + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := preserveRightProgram source)
    (pc := (preserveRightLayout source).resetBase)
    (left := (preserveRightLayout source).transferRegister)
    (right := (preserveRightLayout source).savedLengthRegister)
    (destination := 0)
    (next := (preserveRightLayout source).resetBase + 1)
    (value := Nat.pair output right)
    (by simp [preserveRightProgram, preserveRightLayout])
    rfl
    (by
      simp only [NPOracleState.jump, NPOracleState.write]
      simp only [if_true]
      rw [if_neg (by simp [preserveRightLayout])]
      simp only [firstStageState]
      simp [preserveRightLayout])
    houtputBits]
  apply run_halt_instruction
    (program := preserveRightProgram source)
    (pc := (preserveRightLayout source).resetBase + 1)
    (outputRegister := 0)
    (value := Nat.pair output right)
  · simp [preserveRightProgram, preserveRightLayout]
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact houtputBits

end NearCubicWires.PreserveRightProgram
