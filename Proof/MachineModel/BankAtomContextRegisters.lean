import Proof.MachineModel.BankAtomShapeCountStage
import Proof.MachineModel.BankOracleSizeBoundProgram
import Proof.PCP.PaddedProjectionPresentation

/-!
# The atom-shape context, assembled from the bank's registers

`BankAtomShapeCountStage.inverseAtomShapeRuns_ofContext` reduces the adapter's
residual to `InverseAtomContextRuns`: from the numeral bank's frame produce

`pair table (pair width (pair queryCount bound))`.

Three of those four components are already on the machine.  The width and the
query count are literally two of the bank's five registers, and the size cap is
`RecoveryScheduleEnvelope.oracleSizeBound requiredDegree width`, which
`BankOracleSizeBoundProgram.run_bankSizeBoundProgram` computes from the width
register by the pairing clock with no premise at all.  Only the projection
runner's balanced table is left.

§1–§3 build the three straight-line frames this needs (frame duplication, the
pair swap, and the register projection out of `bankBoundFrame`).  §4 links them
around one table stage, and §5 identifies the assembled word with
`BankEmittedAtomLoop.inverseAtomContext`.

## Where the diagonal lives, exactly

§5 is the only place in the reduction that needs a hypothesis, and it needs two:

* the **presentation** premise, which supplies
  `pcp.nativeWidth = widthEnvelope outer` and `pcp.queryCount = outer.pcp.queryCount`;
* the **diagonal**, `target = inverseScheduleLength …`, which is what makes the
  bank's length-decoded registers the *schedule's* registers.

`BankScheduleDiagonal` records that the consumer of `bodyRun` does not pin the
request's public length to a scheduled source length, so the identification is
threaded as a hypothesis of the one theorem that needs it and is never
asserted.  Everything in §1–§4 is unconditional.

After §5 the adapter's residual is exactly `InverseAtomTableRuns`: the balanced
projection-runner table at the bank's frame, and nothing else.
-/

namespace NearCubicWires.BankAtomContextRegisters

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankOracleSizeBoundProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-! ## 1. Frame duplication -/

private def contextDuplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] private theorem contextDuplicateProgram_oracleFree :
    OracleFree contextDuplicateProgram := by
  rfl

private def contextDuplicateBits (frame : ℕ) : ℕ :=
  natBitLength (Nat.pair frame frame)

private theorem run_contextDuplicateProgram (inputLength frame : ℕ) :
    runNPOracleProgram contextDuplicateProgram (contextDuplicateBits frame) 2
        (initialNPOracleState inputLength frame) =
      some (Nat.pair frame frame) := by
  have hbits : natBitLength (Nat.pair frame frame) ≤
      contextDuplicateBits frame := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair frame frame) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-! ## 2. The pair swap -/

private def contextSwapProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] private theorem contextSwapProgram_oracleFree :
    OracleFree contextSwapProgram := by
  rfl

private def contextSwapBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (Nat.pair right left))

private theorem run_contextSwapProgram (inputLength left right : ℕ) :
    runNPOracleProgram contextSwapProgram (contextSwapBits left right) 4
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right left) := by
  have hinput : natBitLength (Nat.pair left right) ≤
      contextSwapBits left right :=
    natBitLength_mono' (le_max_left _ _)
  have houtput : natBitLength (Nat.pair right left) ≤
      contextSwapBits left right :=
    natBitLength_mono' (le_max_right _ _)
  have hleft : natBitLength left ≤ contextSwapBits left right :=
    (natBitLength_mono' (Nat.left_le_pair left right)).trans hinput
  have hright : natBitLength right ≤ contextSwapBits left right :=
    (natBitLength_mono' (Nat.right_le_pair left right)).trans hinput
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair right left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The register projection -/

/-- Project the shape numerals out of the bank's frame with the size cap
installed: `bankBoundFrame ↦ pair width (pair queryCount bound)`. -/
private def bankRegisterProjectProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairLeft 0 2 2
  , .unpairRight 0 0 3
  , .unpairLeft 0 3 4
  , .unpairRight 0 0 5
  , .unpairRight 0 0 6
  , .unpairLeft 0 4 7
  , .pair 3 4 3 8
  , .pair 2 3 0 9
  , .halt 0
  ]

@[simp] private theorem bankRegisterProjectProgram_oracleFree :
    OracleFree bankRegisterProjectProgram := by
  rfl

/-- The shape numerals the atom loop's context pairs, beside the table. -/
def bankShapeNumerals (sizeBound width queryCount : ℕ) : ℕ :=
  Nat.pair width (Nat.pair queryCount sizeBound)

private def bankRegisterProjectBits
    (sizeBound sourceLen width queryCount copies code : ℕ) : ℕ :=
  natBitLength
    (max (bankBoundFrame sizeBound sourceLen width queryCount copies code)
      (bankShapeNumerals sizeBound width queryCount))

private theorem run_bankRegisterProjectProgram
    (inputLength sizeBound sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram bankRegisterProjectProgram
        (bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code) 10
        (initialNPOracleState inputLength
          (bankBoundFrame sizeBound sourceLen width queryCount copies code)) =
      some (bankShapeNumerals sizeBound width queryCount) := by
  have hframe :
      natBitLength (bankBoundFrame sizeBound sourceLen width queryCount copies
          code) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    natBitLength_mono' (le_max_left _ _)
  have houtput :
      natBitLength (bankShapeNumerals sizeBound width queryCount) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    natBitLength_mono' (le_max_right _ _)
  have hone :
      natBitLength
          (Nat.pair width
            (Nat.pair queryCount
              (Nat.pair copies (Nat.pair sizeBound code)))) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.right_le_pair _ _)).trans hframe
  have hwidth :
      natBitLength width ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.left_le_pair _ _)).trans hone
  have htwo :
      natBitLength
          (Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code))) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.right_le_pair _ _)).trans hone
  have hquery :
      natBitLength queryCount ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.left_le_pair _ _)).trans htwo
  have hthree :
      natBitLength (Nat.pair copies (Nat.pair sizeBound code)) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.right_le_pair _ _)).trans htwo
  have hfour :
      natBitLength (Nat.pair sizeBound code) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.right_le_pair _ _)).trans hthree
  have hbound :
      natBitLength sizeBound ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.left_le_pair _ _)).trans hfour
  have hpaired :
      natBitLength (Nat.pair queryCount sizeBound) ≤
        bankRegisterProjectBits sizeBound sourceLen width queryCount copies
          code :=
    (natBitLength_mono' (Nat.right_le_pair _ _)).trans houtput
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair width (Nat.pair queryCount (Nat.pair copies
        (Nat.pair sizeBound code))))
    (by rfl) rfl
    (by simp [initialNPOracleState, bankBoundFrame, scheduleNumeralBankOutput])
    hone]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies (Nat.pair sizeBound code)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := queryCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair copies (Nat.pair sizeBound code)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sizeBound code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sizeBound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbound]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair queryCount sizeBound)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hpaired]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bankShapeNumerals sizeBound width queryCount) (by rfl) rfl
    (by simp [bankShapeNumerals, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. The shape numerals, executed from the bank's frame -/

/-- The size cap computed from the width register, then the projection. -/
def bankShapeNumeralProgram (requiredDegree : ℕ) : NPOracleProgram :=
  linkPrograms (bankSizeBoundProgram requiredDegree) bankRegisterProjectProgram

theorem bankShapeNumeralProgram_oracleFree (requiredDegree : ℕ) :
    OracleFree (bankShapeNumeralProgram requiredDegree) :=
  oracleFree_linkPrograms (bankSizeBoundProgram_oracleFree requiredDegree)
    bankRegisterProjectProgram_oracleFree

def bankShapeNumeralBits
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    ℕ :=
  occurrenceStageBits inputLength
    (bankSizeBoundBits requiredDegree inputLength sourceLen width queryCount
      copies code)
    (bankRegisterProjectBits (oracleSizeBound requiredDegree width) sourceLen
      width queryCount copies code)

def bankShapeNumeralFuel (requiredDegree : ℕ) : ℕ :=
  linkFuel bankRegisterProjectProgram (bankSizeBoundFuel requiredDegree) 10

/-- **The shape numerals, executed.**  From the numeral bank's frame, with no
premise and no schedule immediate, the fixed stream returns
`pair width (pair queryCount (oracleSizeBound requiredDegree width))`. -/
theorem run_bankShapeNumeralProgram
    (requiredDegree inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram (bankShapeNumeralProgram requiredDegree)
        (bankShapeNumeralBits requiredDegree inputLength sourceLen width
          queryCount copies code)
        (bankShapeNumeralFuel requiredDegree)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) =
      some
        (bankShapeNumerals (oracleSizeBound requiredDegree width) width
          queryCount) :=
  run_occurrenceStage
    (run_bankSizeBoundProgram requiredDegree inputLength sourceLen width
      queryCount copies code)
    (run_bankRegisterProjectProgram inputLength
      (oracleSizeBound requiredDegree width) sourceLen width queryCount copies
      code)

/-! ## 5. The context, from the table stage alone -/

/-- **The adapter's last residual.**  From the numeral bank's frame the table
stage returns the balanced encoding of the projection runner's call outputs at
the scheduled PCP input.  This is the only thing in the whole atom-shape stage
that is not either a bank register or already executed. -/
def InverseAtomTableRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram table (tableBits ⟨target, input⟩)
        (tableFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))

/-- **The context stage.**  Duplicate the bank's frame, compute the shape
numerals on one copy, swap them behind the retained frame, then run the table
stage on that frame. -/
def inverseAtomContextProgram (requiredDegree : ℕ) (table : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms contextDuplicateProgram
    (linkPrograms (preserveRightProgram (bankShapeNumeralProgram requiredDegree))
      (linkPrograms contextSwapProgram (preserveRightProgram table)))

theorem inverseAtomContextProgram_oracleFree (requiredDegree : ℕ)
    {table : NPOracleProgram} (htable : OracleFree table) :
    OracleFree (inverseAtomContextProgram requiredDegree table) :=
  oracleFree_linkPrograms contextDuplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (bankShapeNumeralProgram_oracleFree requiredDegree))
      (oracleFree_linkPrograms contextSwapProgram_oracleFree
        (preserveRightProgram_oracleFree table htable)))

/-- The bank's width register at one public length. -/
noncomputable def inverseBankWidth
    (contracts : PublishedContracts) (clockDepth : ℕ) (target : ℕ) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (sourceIndexOfLength target)

/-- The bank's query-count register at one public length. -/
noncomputable def inverseBankQueryCount
    (contracts : PublishedContracts) (clockDepth : ℕ) (target : ℕ) : ℕ :=
  (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
    (bankSourceLength target)

/-- **The join fact.**  On the schedule's diagonal, and for a presented PCP,
the loop's public request context is the projection-runner table paired with
the bank's *own* width and query-count registers and the size cap computed from
the width register.  Nothing schedule-derived is left in it. -/
theorem inverseAtomContext_ofRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseBankWidth contracts clockDepth target))
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)) =
      inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target := by
  have hindex :
      sourceIndexOfLength target =
        inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target) :=
    sourceIndexOfLength_of_eq_sourceLength hdiagonal
  have hlength :
      bankSourceLength target =
        inverseScheduleLength contracts clockDepth advantageExponent target :=
    bankSourceLength_of_eq_sourceLength hdiagonal
  have hwidth :
      inverseBankWidth contracts clockDepth target =
        pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            target) := by
    rw [inverseBankWidth, hindex]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      inverseBankQueryCount contracts clockDepth target =
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target) := by
    rw [inverseBankQueryCount, hlength]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hbound :
      oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseBankWidth contracts clockDepth target) =
        inverseScheduleBound contracts clockDepth advantageExponent target := by
    rw [inverseBankWidth, hindex]
    rfl
  rw [inverseAtomContext_eq, bankShapeNumerals, hbound, hwidth, hquery]

/-- Width of the context stage at one request. -/
noncomputable def inverseAtomContextBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (contextDuplicateBits
      (inverseAdapterFrame contracts clockDepth advantageExponent request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        (bankShapeNumeralBits
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (LanguageEvaluationRequest.length request)
          (bankSourceLength (LanguageEvaluationRequest.length request))
          (inverseBankWidth contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseBankQueryCount contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (sourceIndexOfLength
              (LanguageEvaluationRequest.length request)))
          (LanguageEvaluationRequest.code request))
        (inverseAdapterFrame contracts clockDepth advantageExponent
          request)
        (inverseAdapterFrame contracts clockDepth advantageExponent
          request)
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (inverseBankWidth contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseBankQueryCount contracts clockDepth
            (LanguageEvaluationRequest.length request))))
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (contextSwapBits
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseBankWidth contracts clockDepth
                (LanguageEvaluationRequest.length request)))
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request))
            (inverseBankQueryCount contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (inverseAdapterFrame contracts clockDepth advantageExponent
            request))
        (preserveRightBits (tableBits request)
          (inverseAdapterFrame contracts clockDepth advantageExponent
            request)
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseBankWidth contracts clockDepth
                (LanguageEvaluationRequest.length request)))
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request))
            (inverseBankQueryCount contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent
                (LanguageEvaluationRequest.length request)))))))

/-- Fuel of the context stage at one request. -/
noncomputable def inverseAtomContextFuel
    (contracts : PublishedContracts) (advantageExponent : ℝ)
    (table : NPOracleProgram)
    (tableFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      (linkPrograms contextSwapProgram (preserveRightProgram table)))
    2
    (linkFuel
      (linkPrograms contextSwapProgram (preserveRightProgram table))
      (preserveRightFuel
        (bankShapeNumeralFuel
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      (linkFuel (preserveRightProgram table) 4
        (preserveRightFuel (tableFuel request))))

/-- **`InverseAtomContextRuns` from the table stage alone.**  The register half
of the context is executed here; the schedule's diagonal and the presentation
premise are threaded, never asserted. -/
theorem inverseAtomContextRuns_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ)
    (htable :
      InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
        table tableBits tableFuel) :
    InverseAtomContextRuns contracts clockDepth machine advantageExponent pcp
      (inverseAtomContextProgram
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        table)
      (inverseAtomContextBits contracts clockDepth machine advantageExponent
        pcp tableBits)
      (inverseAtomContextFuel contracts advantageExponent table tableFuel) := by
  intro target hlarge input
  refine Eq.trans ?_
    (congrArg some
      (inverseAtomContext_ofRegisters contracts clockDepth machine
        advantageExponent pcp hpresentation target (hdiagonal target hlarge)))
  exact run_occurrenceStage
    (run_contextDuplicateProgram target
      (inverseAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        target _ _
        (inverseAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩)
        (inverseAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩)
        _
        (run_bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target (bankSourceLength target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (sourceIndexOfLength target))
          (encodeBitInput input)))
      (run_occurrenceStage
        (run_contextSwapProgram target _
          (inverseAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩))
        (run_preserveRightProgram table target (tableBits ⟨target, input⟩)
          (tableFuel ⟨target, input⟩)
          (inverseAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)
          _ _ (htable target hlarge input))))

end NearCubicWires.BankAtomContextRegisters
