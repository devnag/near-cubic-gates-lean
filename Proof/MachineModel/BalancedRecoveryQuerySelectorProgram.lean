import Proof.MachineModel.BankRecoveryCodeProgram
import Proof.Foundations.NestedBalancedCNFSATEncoding
import Proof.MachineModel.BalancedStructuralAtomEmitterProgram

/-!
# The branch query at the balanced codec

`BankRecoveryCodeProgram.recoveryQuerySelectorProgram` assembles the STANDARD
recovery code — `Encodable.encode` of the circuit-input formula, geometric in
the clause count — from the emitter's TAGGED atom stream, paying the
balanced-to-tagged builder clock (`taggedToBalancedRegisterBitsFor`), the
tagged clause streams, and the nested-pairing formula code on the way
(`RecoveryQuery*GeometricFloor`, Lean-checked).

This twin queries a BALANCED word instead.  The `.sat` opcode's semantics
were already spliced (`NestedBalancedCNFSATEncoding.nestedEncodedSatPromotion`
is definitional): any word the nested balanced decoder recognizes receives
exactly the historical answer on the ordinary canonical code of its decoded
formula.  So a selector that queries any nested balanced encoding of the
SAME circuit-input formula decides the SAME branch — proved here as the
word-level join `encodedSat_eq_recoveryCode_of_decodeNestedBalancedCNF` —
and both scheduled tag lemmas of `CanonicalBranchSelectorProgram` transfer
verbatim.

The producer of the balanced query word (from the balanced emitter's atom
list to a decodable nested word) is taken as ONE named program parameter
`assembler` with one named run hypothesis and one decode hypothesis — the
exact discipline `BankRecoveryCodeProgram` §6 uses for its emitter.  The
selector itself adds one point-preserving wrapper and the frozen `sat`/tag
stage, so its OWN charge carries the assembler width, the two frame words,
and the tag word — no tagged codec, no builder clock, no `Encodable` list
code.  Nothing frozen is edited; the tagged route remains in tree.
-/

namespace NearCubicWires.BalancedRecoveryQuerySelectorProgram

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.BalancedCNFSATEncodingConservativeExtension
open NearCubicWires.BalancedStructuralAtomEmitterProgram
open NearCubicWires.BankRecoveryCodeProgram
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
open NearCubicWires.NestedBalancedCNFSATEncoding
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF
open NearCubicWires.VerifiedLinker

open private satTagProgram satTagBits run_satTagProgram from
  Proof.MachineModel.BankRecoveryCodeProgram

/-! ## 1. The word-level join: any decodable nested word decides the branch -/

/-- Any word the nested balanced decoder sends to the recovery formula has
exactly the recovery code's own SAT answer: the branch decision is preserved
under the balanced re-encoding. -/
theorem encodedSat_eq_recoveryCode_of_decodeNestedBalancedCNF
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) {word : ℕ}
    (hdecode : decodeNestedBalancedCNF word =
      some (boundedOracleRecoveryFormula pcp input bound)) :
    encodedSat word = encodedSat (boundedOracleRecoveryCode pcp input bound) := by
  have hleft := encodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF
    hdecode
  have hwell :
      wellSizedCNFEncoding (boundedOracleRecoveryCode pcp input bound)
          (decodeCNF (boundedOracleRecoveryCode pcp input bound)) = true := by
    have hformula := boundedOracleRecoveryFormula_wellSized pcp input bound
    simpa only [boundedOracleRecoveryCode, decodeCNF_encode] using hformula
  have hright := encodedSat_eq_legacyEncodedSat_of_wellSized hwell
  rw [hleft, hright]
  rfl

/-! ## 2. The balanced branch query with the assembler as sole parameter -/

/-- Assemble the balanced query word from the balanced atom list under a
point-preserving wrapper, then query it once and retag the point code. -/
def balancedRecoveryQuerySelectorProgram (assembler : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms (preserveRightProgram assembler) satTagProgram

def balancedRecoveryQuerySelectorFuel (assemblerFuel : ℕ) : ℕ :=
  linkFuel satTagProgram (preserveRightFuel assemblerFuel) 5

def balancedRecoveryQuerySelectorBits
    (inputLength assemblerBits atomsWord pointCode word : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits assemblerBits atomsWord pointCode word)
    (satTagBits word pointCode)

/-- **The balanced branch query, executed.**  From any assembler run that
produces a nested balanced encoding of the recovery formula, the linked
stream returns the point code tagged with the recovery code's own encoded
satisfiability — the exact output shape of the frozen
`run_recoveryQuerySelectorProgram`, at a polynomial query word. -/
theorem run_balancedRecoveryQuerySelectorProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (bound inputLength atomsWord pointCode word assemblerBits assemblerFuel :
      ℕ)
    (assembler : NPOracleProgram)
    (hassembler :
      runNPOracleProgram assembler assemblerBits assemblerFuel
          (initialNPOracleState inputLength atomsWord) =
        some word)
    (hdecode : decodeNestedBalancedCNF word =
      some (boundedOracleRecoveryFormula pcp input bound)) :
    runNPOracleProgram (balancedRecoveryQuerySelectorProgram assembler)
        (balancedRecoveryQuerySelectorBits inputLength assemblerBits atomsWord
          pointCode word)
        (balancedRecoveryQuerySelectorFuel assemblerFuel)
        (initialNPOracleState inputLength (Nat.pair atomsWord pointCode)) =
      some
        (Nat.pair
          (encodedSat (boundedOracleRecoveryCode pcp input bound)).toNat
          pointCode) := by
  have hrun := run_occurrenceStage
    (run_preserveRightProgram assembler inputLength assemblerBits
      assemblerFuel atomsWord pointCode word hassembler)
    (run_satTagProgram inputLength word pointCode)
  rw [encodedSat_eq_recoveryCode_of_decodeNestedBalancedCNF pcp input bound
    hdecode] at hrun
  exact hrun

/-! ## 3. The emitter and assembler as the two remaining parameters -/

/-- The balanced branch selector driven by a balanced structural emitter and
a balanced query-word assembler: two program parameters, two run hypotheses,
one decode hypothesis, no immediate. -/
def balancedEmittedBranchSelectorProgram
    (emitter assembler : NPOracleProgram) : NPOracleProgram :=
  linkPrograms emitter (balancedRecoveryQuerySelectorProgram assembler)

def balancedEmittedBranchSelectorFuel
    (assembler : NPOracleProgram) (emitterFuel assemblerFuel : ℕ) : ℕ :=
  linkFuel (balancedRecoveryQuerySelectorProgram assembler) emitterFuel
    (balancedRecoveryQuerySelectorFuel assemblerFuel)

def balancedEmittedBranchSelectorBits
    (inputLength emitterBits assemblerBits atomsWord pointCode word : ℕ) :
    ℕ :=
  occurrenceStageBits inputLength emitterBits
    (balancedRecoveryQuerySelectorBits inputLength assemblerBits atomsWord
      pointCode word)

/-- **The balanced branch selector from one emitter premise and one
assembler premise.** -/
theorem run_balancedEmittedBranchSelectorProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (bound inputLength requestCode atomsWord pointCode word emitterBits
      emitterFuel assemblerBits assemblerFuel : ℕ)
    (emitter assembler : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some (Nat.pair atomsWord pointCode))
    (hassembler :
      runNPOracleProgram assembler assemblerBits assemblerFuel
          (initialNPOracleState inputLength atomsWord) =
        some word)
    (hdecode : decodeNestedBalancedCNF word =
      some (boundedOracleRecoveryFormula pcp input bound)) :
    runNPOracleProgram
        (balancedEmittedBranchSelectorProgram emitter assembler)
        (balancedEmittedBranchSelectorBits inputLength emitterBits
          assemblerBits atomsWord pointCode word)
        (balancedEmittedBranchSelectorFuel assembler emitterFuel
          assemblerFuel)
        (initialNPOracleState inputLength requestCode) =
      some
        (Nat.pair
          (encodedSat (boundedOracleRecoveryCode pcp input bound)).toNat
          pointCode) :=
  run_occurrenceStage hemitter
    (run_balancedRecoveryQuerySelectorProgram pcp input bound inputLength
      atomsWord pointCode word assemblerBits assemblerFuel assembler
      hassembler hdecode)

/-! ## 4. The scheduled split at the balanced word -/

/-- **The balanced emitted selector on the Case-1 branch.**  The tag is zero;
the stream contains no target-derived immediate and no tagged codec. -/
theorem run_balancedEmittedBranchSelectorProgram_caseOne
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier requiredDegree sourceIndex
      input)
    (inputLength requestCode atomsWord pointCode word emitterBits emitterFuel
      assemblerBits assemblerFuel : ℕ)
    (emitter assembler : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some (Nat.pair atomsWord pointCode))
    (hassembler :
      runNPOracleProgram assembler assemblerBits assemblerFuel
          (initialNPOracleState inputLength atomsWord) =
        some word)
    (hdecode : decodeNestedBalancedCNF word =
      some
        (boundedOracleRecoveryFormula (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree
            (scheduledWidth outer sourceIndex)))) :
    runNPOracleProgram
        (balancedEmittedBranchSelectorProgram emitter assembler)
        (balancedEmittedBranchSelectorBits inputLength emitterBits
          assemblerBits atomsWord pointCode word)
        (balancedEmittedBranchSelectorFuel assembler emitterFuel
          assemblerFuel)
        (initialNPOracleState inputLength requestCode) =
      some (Nat.pair 0 pointCode) := by
  have hrun := run_balancedEmittedBranchSelectorProgram (paddedOuterPCP outer)
    input (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    inputLength requestCode atomsWord pointCode word emitterBits emitterFuel
    assemblerBits assemblerFuel emitter assembler hemitter hassembler hdecode
  rw [← scheduledSelectorQuery_eq_recoveryCode outer requiredDegree sourceIndex
    input, encodedSat_scheduledSelectorQuery_eq_false data] at hrun
  exact hrun

/-- **The balanced emitted selector on the Case-2 branch.** -/
theorem run_balancedEmittedBranchSelectorProgram_caseTwo
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength requestCode atomsWord pointCode word emitterBits emitterFuel
      assemblerBits assemblerFuel : ℕ)
    (emitter assembler : NPOracleProgram)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState inputLength requestCode) =
        some (Nat.pair atomsWord pointCode))
    (hassembler :
      runNPOracleProgram assembler assemblerBits assemblerFuel
          (initialNPOracleState inputLength atomsWord) =
        some word)
    (hdecode : decodeNestedBalancedCNF word =
      some
        (boundedOracleRecoveryFormula (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree
            (scheduledWidth outer sourceIndex)))) :
    runNPOracleProgram
        (balancedEmittedBranchSelectorProgram emitter assembler)
        (balancedEmittedBranchSelectorBits inputLength emitterBits
          assemblerBits atomsWord pointCode word)
        (balancedEmittedBranchSelectorFuel assembler emitterFuel
          assemblerFuel)
        (initialNPOracleState inputLength requestCode) =
      some (Nat.pair 1 pointCode) := by
  have hrun := run_balancedEmittedBranchSelectorProgram (paddedOuterPCP outer)
    input (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))
    inputLength requestCode atomsWord pointCode word emitterBits emitterFuel
    assemblerBits assemblerFuel emitter assembler hemitter hassembler hdecode
  rw [← scheduledSelectorQuery_eq_recoveryCode outer requiredDegree sourceIndex
    input, encodedSat_scheduledSelectorQuery_eq_true caseTwo] at hrun
  exact hrun

/-! ## 5. Width ledger — five public bounds, one budget, no codec head -/

/-- Closed-form collapse of the balanced selector charge.  The five
hypotheses are at public coordinates (the assembler width, the two frame
words, the tag word, the public length); there is no builder-clock arm and
no tagged payload anywhere in the charge. -/
theorem balancedRecoveryQuerySelectorBits_le
    {inputLength assemblerBits atomsWord pointCode word budget : ℕ}
    (hlen : natBitLength inputLength ≤ budget)
    (hassembler : assemblerBits ≤ budget)
    (hin : natBitLength (Nat.pair atomsWord pointCode) ≤ budget)
    (hmid : natBitLength (Nat.pair word pointCode) ≤ budget)
    (hout :
      natBitLength (Nat.pair (encodedSat word).toNat pointCode) ≤ budget) :
    balancedRecoveryQuerySelectorBits inputLength assemblerBits atomsWord
        pointCode word ≤ budget := by
  have hsat :
      natBitLength
          (max (Nat.pair word pointCode)
            (Nat.pair (encodedSat word).toNat pointCode)) ≤ budget := by
    rcases Nat.le_total (Nat.pair word pointCode)
        (Nat.pair (encodedSat word).toNat pointCode) with h | h
    · rw [Nat.max_eq_right h]
      exact hout
    · rw [Nat.max_eq_left h]
      exact hmid
  simp only [balancedRecoveryQuerySelectorBits, satTagBits,
    occurrenceStageBits, preserveRightBits]
  exact max_le hlen (max_le (max_le hassembler (max_le hin hmid)) hsat)

end NearCubicWires.BalancedRecoveryQuerySelectorProgram
