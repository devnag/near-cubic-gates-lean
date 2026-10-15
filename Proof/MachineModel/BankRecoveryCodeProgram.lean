import Proof.MachineModel.BankRefuterWordFrameProgram
import Proof.MachineModel.BoundedOracleStructuralFormulaPrefixSATProgram
import Proof.MachineModel.CanonicalBranchSelectorProgram

namespace NearCubicWires.BankRecoveryCodeProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBranchSelectorProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The reversed canonical stream folds to the formula's own code

`DynamicCNFBuilder.run_cnfListBuilder` fixes the public input length to
`cnfVariableCount`, which a linked stage cannot choose.  The same
`run_cnfListBuilder_from` refinement holds at every public length. -/

private def reverseStreamBits (formula : EncodedCNF) : ℕ :=
  natBitLength
    (max (canonicalReverseClauseStream formula) (Encodable.encode formula))

private theorem run_cnfListBuilderProgram_at
    (inputLength : ℕ) (formula : EncodedCNF) :
    runNPOracleProgram cnfListBuilderProgram (reverseStreamBits formula)
        (cnfListBuilderFuel ((formula.map Encodable.encode).reverse))
        (initialNPOracleState inputLength
          (canonicalReverseClauseStream formula)) =
      some (Encodable.encode formula) := by
  have hrun :=
    run_cnfListBuilder_from ((formula.map Encodable.encode).reverse) []
      (sourceBound := canonicalReverseClauseStream formula)
      (outputBound := Encodable.encode formula)
      (maximumBits := reverseStreamBits formula)
      (initialNPOracleState inputLength
        (canonicalReverseClauseStream formula))
      (by rfl)
      (by simp [initialNPOracleState, canonicalReverseClauseStream])
      (by simp [initialNPOracleState, encodeCodeList])
      (by rw [canonicalReverseClauseStream])
      (by simp [encodeCodeList_map_encode])
      (le_refl _)
  simpa [encodeCodeList_map_encode] using hrun

/-! ## 2. From the forward raw-clause stream to the formula code -/

/-- Canonicalize, reverse, and fold: the exact `EncodedCNF` code of a formula
presented as its forward raw-clause stream. -/
def formulaCodeProgram : NPOracleProgram :=
  linkPrograms structuralClauseStreamProgram cnfListBuilderProgram

theorem formulaCodeProgram_oracleFree : OracleFree formulaCodeProgram :=
  oracleFree_linkPrograms structuralClauseStreamProgram_oracleFree
    cnfListBuilder_oracleFree

def formulaCodeFuel (formula : EncodedCNF) : ℕ :=
  linkFuel cnfListBuilderProgram (structuralClauseStreamFuel formula)
    (cnfListBuilderFuel ((formula.map Encodable.encode).reverse))

def formulaCodeBits (inputLength : ℕ) (formula : EncodedCNF) : ℕ :=
  occurrenceStageBits inputLength (structuralClauseStreamMaximumBits formula)
    (reverseStreamBits formula)

/-- **The formula code, executed.**  The only premise is the structural
three-literal invariant `StructuralClauseStreamProgram` already requires. -/
theorem run_formulaCodeProgram (inputLength : ℕ) (formula : EncodedCNF)
    (hthree : formula.all (fun clause => clause.length = 3) = true) :
    runNPOracleProgram formulaCodeProgram (formulaCodeBits inputLength formula)
        (formulaCodeFuel formula)
        (initialNPOracleState inputLength (rawClauseStream formula)) =
      some (Encodable.encode formula) :=
  run_occurrenceStage
    (run_structuralClauseStreamProgram formula hthree inputLength)
    (run_cnfListBuilderProgram_at inputLength formula)

/-! ## 3. From the balanced clause atoms to the formula code -/

/-- The complete circuit-input CNF of a Boolean circuit, from its balanced
clause-atom schedule to the formula's own code. -/
def circuitFormulaCodeProgram : NPOracleProgram :=
  linkPrograms circuitInputFormulaBalancedFoldProgram formulaCodeProgram

theorem circuitFormulaCodeProgram_oracleFree :
    OracleFree circuitFormulaCodeProgram :=
  oracleFree_linkPrograms circuitInputFormulaBalancedFoldProgram_oracleFree
    formulaCodeProgram_oracleFree

def circuitFormulaCodeFuel {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  linkFuel formulaCodeProgram (circuitInputFormulaBalancedFoldFuel circuit)
    (formulaCodeFuel (circuitInputFormula circuit))

def circuitFormulaCodeBits {n : ℕ} (inputLength : ℕ)
    (circuit : BooleanCircuit n) : ℕ :=
  occurrenceStageBits inputLength
    (circuitInputFormulaBalancedFoldBits inputLength circuit)
    (formulaCodeBits inputLength (circuitInputFormula circuit))

/-- **The circuit-input CNF code, executed.**  No premise remains: the
three-literal invariant is `CircuitInputCNF.circuitInputFormula_threeLiteral`. -/
theorem run_circuitFormulaCodeProgram {n : ℕ} (inputLength : ℕ)
    (circuit : BooleanCircuit n) :
    runNPOracleProgram circuitFormulaCodeProgram
        (circuitFormulaCodeBits inputLength circuit)
        (circuitFormulaCodeFuel circuit)
        (initialNPOracleState inputLength
          (encodeBalancedList (circuitInputFormulaAtoms circuit))) =
      some (Encodable.encode (circuitInputFormula circuit)) :=
  run_occurrenceStage
    (run_circuitInputFormulaBalancedFoldProgram inputLength circuit)
    (run_formulaCodeProgram inputLength (circuitInputFormula circuit)
      (circuitInputFormula_threeLiteral circuit))

/-! ## 4. From the tagged emitter stream to the bounded-oracle recovery code -/

/-- **The recovery-code assembler.**  One fixed oracle-free instruction stream
from the structural emitter's tagged atom schedule to the canonical
bounded-oracle recovery code. -/
def recoveryCodeProgram : NPOracleProgram :=
  linkPrograms taggedToBalancedProgram circuitFormulaCodeProgram

theorem recoveryCodeProgram_oracleFree : OracleFree recoveryCodeProgram :=
  oracleFree_linkPrograms taggedToBalancedProgram_oracleFree
    circuitFormulaCodeProgram_oracleFree

def recoveryCodeFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  linkFuel circuitFormulaCodeProgram
    (taggedToBalancedFuel (boundedOracleStructuralFormulaAtoms pcp input bound))
    (circuitFormulaCodeFuel (boundedOracleVerifierCircuit pcp input bound))

def recoveryCodeBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (taggedToBalancedRegisterBitsFor inputLength
      (boundedOracleStructuralFormulaAtoms pcp input bound))
    (circuitFormulaCodeBits inputLength
      (boundedOracleVerifierCircuit pcp input bound))

/-- **The recovery code, executed.**  From the emitter's tagged atom stream the
fixed stream returns exactly the word the branch selector queries. -/
theorem run_recoveryCodeProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength : ℕ) :
    runNPOracleProgram recoveryCodeProgram
        (recoveryCodeBits pcp input bound inputLength)
        (recoveryCodeFuel pcp input bound)
        (initialNPOracleState inputLength
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp input bound))) =
      some (boundedOracleRecoveryCode pcp input bound) := by
  have hstream :
      runNPOracleProgram
          (linkPrograms taggedToBalancedProgram circuitFormulaCodeProgram)
          (occurrenceStageBits inputLength
            (taggedToBalancedRegisterBitsFor inputLength
              (circuitInputFormulaAtoms
                (boundedOracleVerifierCircuit pcp input bound)))
            (circuitFormulaCodeBits inputLength
              (boundedOracleVerifierCircuit pcp input bound)))
          (linkFuel circuitFormulaCodeProgram
            (taggedToBalancedFuel
              (circuitInputFormulaAtoms
                (boundedOracleVerifierCircuit pcp input bound)))
            (circuitFormulaCodeFuel
              (boundedOracleVerifierCircuit pcp input bound)))
          (initialNPOracleState inputLength
            (encodeTaggedList
              (circuitInputFormulaAtoms
                (boundedOracleVerifierCircuit pcp input bound)))) =
        some
          (Encodable.encode
            (circuitInputFormula
              (boundedOracleVerifierCircuit pcp input bound))) :=
    run_occurrenceStage
      (run_taggedToBalancedProgram_from inputLength
        (circuitInputFormulaAtoms
          (boundedOracleVerifierCircuit pcp input bound)))
      (run_circuitFormulaCodeProgram inputLength
        (boundedOracleVerifierCircuit pcp input bound))
  simp only [recoveryCodeProgram, recoveryCodeBits, recoveryCodeFuel,
    boundedOracleRecoveryCode, boundedOracleRecoveryFormula,
    boundedOracleStructuralFormulaAtoms_eq]
  exact hstream

/-! ## 5. The branch selector with no query immediate

`CanonicalBranchSelectorProgram.branchSelectorProgram` is `copy`, `set`, `sat`,
`pair`.  Replacing its `set` by the assembler of §4 keeps the interface — a
retained point code in, the tagged point code out — and removes the immediate.
-/

/-- Query the assembled code and retag the retained point code. -/
private def satTagProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .sat 2 4 3
  , .pair 4 3 0 4
  , .halt 0
  ]

private def satTagBits (queryCode pointCode : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair queryCode pointCode)
      (Nat.pair (encodedSat queryCode).toNat pointCode))

private theorem run_satTagProgram
    (inputLength queryCode pointCode : ℕ) :
    runNPOracleProgram satTagProgram (satTagBits queryCode pointCode) 5
        (initialNPOracleState inputLength (Nat.pair queryCode pointCode)) =
      some (Nat.pair (encodedSat queryCode).toNat pointCode) := by
  have hrequest :
      natBitLength (Nat.pair queryCode pointCode) ≤
        satTagBits queryCode pointCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtput :
      natBitLength (Nat.pair (encodedSat queryCode).toNat pointCode) ≤
        satTagBits queryCode pointCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hquery : natBitLength queryCode ≤ satTagBits queryCode pointCode :=
    (natBitLength_mono (Nat.left_le_pair queryCode pointCode)).trans hrequest
  have hpoint : natBitLength pointCode ≤ satTagBits queryCode pointCode :=
    (natBitLength_mono (Nat.right_le_pair queryCode pointCode)).trans hrequest
  have htag :
      natBitLength (encodedSat queryCode).toNat ≤
        satTagBits queryCode pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (encodedSat queryCode).toNat pointCode)).trans houtput
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hquery]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpoint]
  rw [show 3 = 2 + 1 by omega]
  rw [run_sat_instruction (query := queryCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery htag]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (encodedSat queryCode).toNat pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- **The register-driven branch query.**  From the emitter's tagged atom
stream beside the retained point code, the assembled recovery code is queried
once and the point code returned with the answer. -/
def recoveryQuerySelectorProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram recoveryCodeProgram) satTagProgram

def recoveryQuerySelectorFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  linkFuel satTagProgram (preserveRightFuel (recoveryCodeFuel pcp input bound))
    5

def recoveryQuerySelectorBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength pointCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits (recoveryCodeBits pcp input bound inputLength)
      (encodeTaggedList (boundedOracleStructuralFormulaAtoms pcp input bound))
      pointCode (boundedOracleRecoveryCode pcp input bound))
    (satTagBits (boundedOracleRecoveryCode pcp input bound) pointCode)

/-- **The branch query, executed.**  No query immediate appears in the stream:
the word queried is assembled from the emitter's stream at run time. -/
theorem run_recoveryQuerySelectorProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength pointCode : ℕ) :
    runNPOracleProgram recoveryQuerySelectorProgram
        (recoveryQuerySelectorBits pcp input bound inputLength pointCode)
        (recoveryQuerySelectorFuel pcp input bound)
        (initialNPOracleState inputLength
          (Nat.pair
            (encodeTaggedList
              (boundedOracleStructuralFormulaAtoms pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodedSat (boundedOracleRecoveryCode pcp input bound)).toNat
          pointCode) :=
  run_occurrenceStage
    (run_preserveRightProgram recoveryCodeProgram inputLength
      (recoveryCodeBits pcp input bound inputLength)
      (recoveryCodeFuel pcp input bound)
      (encodeTaggedList (boundedOracleStructuralFormulaAtoms pcp input bound))
      pointCode (boundedOracleRecoveryCode pcp input bound)
      (run_recoveryCodeProgram pcp input bound inputLength))
    (run_satTagProgram inputLength (boundedOracleRecoveryCode pcp input bound)
      pointCode)

/-! ## 6. The emitter as the sole remaining parameter -/

/-- The branch selector driven by a structural emitter: one program parameter,
one run hypothesis, no immediate. -/
def emittedBranchSelectorProgram (emitter : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms emitter recoveryQuerySelectorProgram

def emittedBranchSelectorFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound emitterFuel : ℕ) : ℕ :=
  linkFuel recoveryQuerySelectorProgram emitterFuel
    (recoveryQuerySelectorFuel pcp input bound)

def emittedBranchSelectorBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength pointCode emitterBits : ℕ) : ℕ :=
  occurrenceStageBits inputLength emitterBits
    (recoveryQuerySelectorBits pcp input bound inputLength pointCode)

/-- **The branch selector from one emitter premise.**  Whatever request code
the emitter consumes, the linked stream returns the point code tagged with the
encoded satisfiability of the canonical bounded-oracle recovery formula — the
exact output of `CanonicalBranchSelectorProgram.branchSelectorProgram`, with
the query computed rather than baked. -/
theorem run_emittedBranchSelectorProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength requestCode pointCode emitterBits
      emitterFuel : ℕ)
    (emitter : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some
          (Nat.pair
            (encodeTaggedList
              (boundedOracleStructuralFormulaAtoms pcp input bound))
            pointCode)) :
    runNPOracleProgram (emittedBranchSelectorProgram emitter)
        (emittedBranchSelectorBits pcp input bound inputLength pointCode
          emitterBits)
        (emittedBranchSelectorFuel pcp input bound emitterFuel)
        (initialNPOracleState inputLength requestCode) =
      some
        (Nat.pair
          (encodedSat (boundedOracleRecoveryCode pcp input bound)).toNat
          pointCode) :=
  run_occurrenceStage hemitter
    (run_recoveryQuerySelectorProgram pcp input bound inputLength pointCode)

/-! ## 7. The scheduled split, decided without an immediate

`CanonicalBranchSelectorProgram.scheduledSelectorQuery` is definitionally the
recovery code of §4 at the scheduled size bound, so the two tag lemmas of that
module apply to the emitted selector unchanged.
-/

theorem scheduledSelectorQuery_eq_recoveryCode
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) :
    scheduledSelectorQuery outer requiredDegree sourceIndex input =
      boundedOracleRecoveryCode (paddedOuterPCP outer) input
        (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex)) :=
  rfl

/-- **The emitted selector on the Case-1 branch.**  The tag is zero, and the
stream contains no target-derived immediate. -/
theorem run_emittedBranchSelectorProgram_caseOne
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier requiredDegree sourceIndex
      input)
    (inputLength requestCode pointCode emitterBits emitterFuel : ℕ)
    (emitter : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some
          (Nat.pair
            (encodeTaggedList
              (boundedOracleStructuralFormulaAtoms (paddedOuterPCP outer) input
                (oracleSizeBound requiredDegree
                  (scheduledWidth outer sourceIndex))))
            pointCode)) :
    runNPOracleProgram (emittedBranchSelectorProgram emitter)
        (emittedBranchSelectorBits (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
          inputLength pointCode emitterBits)
        (emittedBranchSelectorFuel (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
          emitterFuel)
        (initialNPOracleState inputLength requestCode) =
      some (Nat.pair 0 pointCode) := by
  have hrun :=
    run_emittedBranchSelectorProgram (paddedOuterPCP outer) input
      (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
      inputLength requestCode pointCode emitterBits emitterFuel emitter hemitter
  rw [← scheduledSelectorQuery_eq_recoveryCode outer requiredDegree sourceIndex
    input, encodedSat_scheduledSelectorQuery_eq_false data] at hrun
  exact hrun

/-- **The emitted selector on the Case-2 branch.** -/
theorem run_emittedBranchSelectorProgram_caseTwo
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength requestCode pointCode emitterBits emitterFuel : ℕ)
    (emitter : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some
          (Nat.pair
            (encodeTaggedList
              (boundedOracleStructuralFormulaAtoms (paddedOuterPCP outer) input
                (oracleSizeBound requiredDegree
                  (scheduledWidth outer sourceIndex))))
            pointCode)) :
    runNPOracleProgram (emittedBranchSelectorProgram emitter)
        (emittedBranchSelectorBits (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
          inputLength pointCode emitterBits)
        (emittedBranchSelectorFuel (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
          emitterFuel)
        (initialNPOracleState inputLength requestCode) =
      some (Nat.pair 1 pointCode) := by
  have hrun :=
    run_emittedBranchSelectorProgram (paddedOuterPCP outer) input
      (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
      inputLength requestCode pointCode emitterBits emitterFuel emitter hemitter
  rw [← scheduledSelectorQuery_eq_recoveryCode outer requiredDegree sourceIndex
    input, encodedSat_scheduledSelectorQuery_eq_true caseTwo] at hrun
  exact hrun

end NearCubicWires.BankRecoveryCodeProgram
