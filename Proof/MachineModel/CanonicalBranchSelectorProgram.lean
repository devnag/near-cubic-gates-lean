import Proof.MachineModel.CaseTwoBlockOccurrenceProgram

/-!
# The executable Case-1/Case-2 branch selector

`BranchTargetLanguageProgram` links two closed chains onto the fixed tag
dispatcher and leaves the tag itself as a parameter: one program returning
`pair tag pointCode`, with `tag ≠ 0` exactly when the scheduled outer split
lands in Case 2.  This module builds that program.

The whole discrimination is one `sat` opcode.
`CanonicalTargetLanguageProgram.scheduledCaseTwo_iff_encodedSat` proves that
the encoded satisfiability of the canonical bounded-oracle recovery formula of
the scheduled refuter word is equivalent to the existence of a canonical
accepting oracle, which is precisely the branch condition of
`ScheduledRecovery.scheduledOuterBranch`.  The selector therefore consists of
one `copy`, one `set` of the recovery code, one `sat`, and one `pair`: no
circuit, oracle, or branch witness is supplied from outside, and no second
decision procedure is introduced.

Both directions are then instantiated:

* a `ScheduledCaseOneData` — the Case-1 payload of the canonical split, whose
  single field is the literal non-existence of a small accepting oracle —
  forces the tag to zero;
* a `CanonicalAcceptingOracle` forces the tag to one.

Composing with `CaseTwoBlockOccurrenceProgram`, §4 states the branch-dispatched
canonical target at both published schedules with the selector and the
per-block occurrence callee both discharged.  On the Case-1 branch the
scheduled query-count positivity of `OuterProofRowStageProgram` remains the one
side condition, exactly as `BranchTargetLanguageProgram` records.
-/

namespace NearCubicWires.CanonicalBranchSelectorProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoBlockOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. One SAT query, then the tagged request

Register ABI: `r2` the retained point code, `r3` the recovery code, `r4` the
decided tag. -/

/-- The branch selector: one oracle query on the supplied recovery code, and
the requested point code retagged with its answer. -/
def branchSelectorProgram (queryCode : ℕ) : NPOracleProgram :=
  [ .copy 0 2 1
  , .set 3 queryCode 2
  , .sat 3 4 3
  , .pair 4 2 0 4
  , .halt 0
  ]

def branchSelectorFuel : ℕ := 5

def branchSelectorBits (queryCode pointCode : ℕ) : ℕ :=
  natBitLength
    (max queryCode (Nat.pair (encodedSat queryCode).toNat pointCode))

/-- **The branch selector, executed.**  One fixed instruction stream returns
the requested point code tagged with the encoded satisfiability of the supplied
recovery code. -/
theorem run_branchSelectorProgram (inputLength queryCode pointCode : ℕ) :
    runNPOracleProgram (branchSelectorProgram queryCode)
        (branchSelectorBits queryCode pointCode) branchSelectorFuel
        (initialNPOracleState inputLength pointCode) =
      some (Nat.pair (encodedSat queryCode).toNat pointCode) := by
  have hquery : natBitLength queryCode ≤ branchSelectorBits queryCode pointCode :=
    natBitLength_mono (Nat.le_max_left _ _)
  have houtput :
      natBitLength (Nat.pair (encodedSat queryCode).toNat pointCode) ≤
        branchSelectorBits queryCode pointCode :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hpoint : natBitLength pointCode ≤ branchSelectorBits queryCode pointCode :=
    (natBitLength_mono
      (Nat.right_le_pair (encodedSat queryCode).toNat pointCode)).trans houtput
  have htag :
      natBitLength (encodedSat queryCode).toNat ≤
        branchSelectorBits queryCode pointCode :=
    (natBitLength_mono
      (Nat.left_le_pair (encodedSat queryCode).toNat pointCode)).trans houtput
  rw [show branchSelectorFuel = 4 + 1 by rfl]
  rw [run_copy_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hpoint]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := queryCode) (by rfl) rfl hquery]
  rw [show 3 = 2 + 1 by omega]
  rw [run_sat_instruction (query := queryCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hquery htag]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (encodedSat queryCode).toNat pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The scheduled recovery code and its two branch values -/

/-- The recovery code the scheduled split is decided by. -/
noncomputable def scheduledSelectorQuery
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) : ℕ :=
  boundedOracleRecoveryCode (paddedOuterPCP outer) input
    (oracleSizeBound requiredDegree (scheduledWidth outer sourceIndex))

/-- The Case-1 payload of the canonical split rules out every canonical
accepting oracle: its single field is exactly that non-existence. -/
theorem not_nonempty_canonicalAcceptingOracle_of_caseOneData
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier requiredDegree sourceIndex
      input) :
    ¬ Nonempty
      (CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) := by
  rintro ⟨canonical⟩
  exact data.noSmallAcceptingOracle canonical.circuit canonical.sizeBounded
    canonical.accepts

/-- **The Case-1 tag.**  The scheduled query is unsatisfiable on the Case-1
branch. -/
theorem encodedSat_scheduledSelectorQuery_eq_false
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier requiredDegree sourceIndex
      input) :
    encodedSat (scheduledSelectorQuery outer requiredDegree sourceIndex input) =
      false := by
  unfold scheduledSelectorQuery
  rw [Bool.eq_false_iff, ne_eq,
    scheduledCaseTwo_iff_encodedSat outer requiredDegree sourceIndex input]
  exact not_nonempty_canonicalAcceptingOracle_of_caseOneData data

/-- **The Case-2 tag.**  The scheduled query is satisfiable whenever a
canonical accepting oracle exists. -/
theorem encodedSat_scheduledSelectorQuery_eq_true
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    encodedSat (scheduledSelectorQuery outer requiredDegree sourceIndex input) =
      true :=
  (scheduledCaseTwo_iff_encodedSat outer requiredDegree sourceIndex
    input).mpr ⟨caseTwo⟩

/-- **The scheduled selector on the Case-1 branch.** -/
theorem run_scheduledSelectorProgram_caseOne
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source} {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier requiredDegree sourceIndex
      input)
    (inputLength pointCode : ℕ) :
    runNPOracleProgram
        (branchSelectorProgram
          (scheduledSelectorQuery outer requiredDegree sourceIndex input))
        (branchSelectorBits
          (scheduledSelectorQuery outer requiredDegree sourceIndex input)
          pointCode)
        branchSelectorFuel
        (initialNPOracleState inputLength pointCode) =
      some (Nat.pair 0 pointCode) := by
  have hrun :=
    run_branchSelectorProgram inputLength
      (scheduledSelectorQuery outer requiredDegree sourceIndex input) pointCode
  rw [encodedSat_scheduledSelectorQuery_eq_false data] at hrun
  exact hrun

/-- **The scheduled selector on the Case-2 branch.** -/
theorem run_scheduledSelectorProgram_caseTwo
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (inputLength pointCode : ℕ) :
    runNPOracleProgram
        (branchSelectorProgram
          (scheduledSelectorQuery outer requiredDegree sourceIndex input))
        (branchSelectorBits
          (scheduledSelectorQuery outer requiredDegree sourceIndex input)
          pointCode)
        branchSelectorFuel
        (initialNPOracleState inputLength pointCode) =
      some (Nat.pair 1 pointCode) := by
  have hrun :=
    run_branchSelectorProgram inputLength
      (scheduledSelectorQuery outer requiredDegree sourceIndex input) pointCode
  rw [encodedSat_scheduledSelectorQuery_eq_true caseTwo] at hrun
  exact hrun

/-! ## 3. The selector at both published schedules -/

/-- The inverse schedule's branch query. -/
noncomputable def inverseSelectorQuery
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  scheduledSelectorQuery outer
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
    (inverseRefuterInput contracts outer machine advantageExponent target)

/-- The fixed schedule's branch query. -/
noncomputable def fixedSelectorQuery
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) : ℕ :=
  scheduledSelectorQuery outer (fixedRequiredDegree contracts requestedRate)
    (fixedSelectedSource contracts outer requestedRate target)
    (fixedRefuterInput contracts outer machine requestedRate target)

/-! ## 4. The branch-dispatched canonical target, selector discharged -/

/-- **The inverse schedule's canonical target on the Case-1 branch, with the
selector discharged.**  Only the scheduled query-count positivity remains. -/
theorem run_inverseTargetProgram_caseOne_closed
    (occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseOne data)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target
          (branchSelectorProgram
            (inverseSelectorQuery contracts outer machine advantageExponent
              target))
          occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point)
          (branchSelectorBits
            (inverseSelectorQuery contracts outer machine advantageExponent
              target)
            (encodeBitInput point))
          (inverseCaseOneChainBits contracts outer machine advantageExponent
            target point)
          (inverseCanonicalTargetFunction contracts outer machine
            advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent
            target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target
            occurrence)
          branchSelectorFuel
          (inverseCaseOneChainFuel contracts outer machine advantageExponent
            target point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_inverseTargetProgram_caseOne
    (branchSelectorProgram
      (inverseSelectorQuery contracts outer machine advantageExponent target))
    occurrence contracts outer machine advantageExponent target hlarge hyes
    hrejects haccepts data hbranch point
    (branchSelectorBits
      (inverseSelectorQuery contracts outer machine advantageExponent target)
      (encodeBitInput point))
    branchSelectorFuel
    (run_scheduledSelectorProgram_caseOne data target (encodeBitInput point))
    hcount

/-- **The inverse schedule's canonical target on the Case-2 branch, fully
closed.**  Both the selector and the per-block occurrence callee are
discharged. -/
theorem run_inverseTargetProgram_caseTwo_closed
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target
          (branchSelectorProgram
            (inverseSelectorQuery contracts outer machine advantageExponent
              target))
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo))
        (branchTargetBitBits target 1 (encodeBitInput point)
          (branchSelectorBits
            (inverseSelectorQuery contracts outer machine advantageExponent
              target)
            (encodeBitInput point))
          (inverseCaseTwoChainBits contracts outer machine advantageExponent
            target caseTwo
            (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts)
              caseTwo target (encodeBitInput point))
            point)
          (inverseCanonicalTargetFunction contracts outer machine
            advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent
            target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target
            (caseTwoScheduledOccurrenceProgram
              (publishedPointwisePCPP contracts) caseTwo))
          branchSelectorFuel
          (inverseCaseTwoChainFuel contracts outer machine advantageExponent
            target caseTwo
            (caseTwoScheduledOccurrenceProgram
              (publishedPointwisePCPP contracts) caseTwo)
            (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts)
              caseTwo target (encodeBitInput point))
            point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_inverseTargetProgram_caseTwo
    (branchSelectorProgram
      (inverseSelectorQuery contracts outer machine advantageExponent target))
    (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
      caseTwo)
    contracts outer machine advantageExponent target hlarge hyes hrejects
    haccepts caseTwo hbranch point
    (branchSelectorBits
      (inverseSelectorQuery contracts outer machine advantageExponent target)
      (encodeBitInput point))
    branchSelectorFuel 1
    (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    Nat.one_ne_zero
    (run_scheduledSelectorProgram_caseTwo caseTwo target (encodeBitInput point))
    (fun block _ =>
      run_caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
        caseTwo target (encodeBitInput point) block)

/-- **The fixed schedule's canonical target on the Case-1 branch, with the
selector discharged.** -/
theorem run_fixedTargetProgram_caseOne_closed
    (occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseOne data)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (fixedSelectedSource contracts outer requestedRate target))) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target
          (branchSelectorProgram
            (fixedSelectorQuery contracts outer machine requestedRate target))
          occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point)
          (branchSelectorBits
            (fixedSelectorQuery contracts outer machine requestedRate target)
            (encodeBitInput point))
          (fixedCaseOneChainBits contracts outer machine requestedRate target
            point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
            target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate
            target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target
            occurrence)
          branchSelectorFuel
          (fixedCaseOneChainFuel contracts outer machine requestedRate target
            point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_fixedTargetProgram_caseOne
    (branchSelectorProgram
      (fixedSelectorQuery contracts outer machine requestedRate target))
    occurrence contracts outer machine requestedRate target hlarge hyes
    hrejects haccepts data hbranch point
    (branchSelectorBits
      (fixedSelectorQuery contracts outer machine requestedRate target)
      (encodeBitInput point))
    branchSelectorFuel
    (run_scheduledSelectorProgram_caseOne data target (encodeBitInput point))
    hcount

/-- **The fixed schedule's canonical target on the Case-2 branch, fully
closed.** -/
theorem run_fixedTargetProgram_caseTwo_closed
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseTwo caseTwo)
    (point : BitInput target) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target
          (branchSelectorProgram
            (fixedSelectorQuery contracts outer machine requestedRate target))
          (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
            caseTwo))
        (branchTargetBitBits target 1 (encodeBitInput point)
          (branchSelectorBits
            (fixedSelectorQuery contracts outer machine requestedRate target)
            (encodeBitInput point))
          (fixedCaseTwoChainBits contracts outer machine requestedRate target
            caseTwo
            (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts)
              caseTwo target (encodeBitInput point))
            point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
            target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate
            target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target
            (caseTwoScheduledOccurrenceProgram
              (publishedPointwisePCPP contracts) caseTwo))
          branchSelectorFuel
          (fixedCaseTwoChainFuel contracts outer machine requestedRate target
            caseTwo
            (caseTwoScheduledOccurrenceProgram
              (publishedPointwisePCPP contracts) caseTwo)
            (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts)
              caseTwo target (encodeBitInput point))
            point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_fixedTargetProgram_caseTwo
    (branchSelectorProgram
      (fixedSelectorQuery contracts outer machine requestedRate target))
    (caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
      caseTwo)
    contracts outer machine requestedRate target hlarge hyes hrejects
    haccepts caseTwo hbranch point
    (branchSelectorBits
      (fixedSelectorQuery contracts outer machine requestedRate target)
      (encodeBitInput point))
    branchSelectorFuel 1
    (caseTwoScheduledOccurrenceBits (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    (caseTwoScheduledOccurrenceFuel (publishedPointwisePCPP contracts) caseTwo
      target (encodeBitInput point))
    Nat.one_ne_zero
    (run_scheduledSelectorProgram_caseTwo caseTwo target (encodeBitInput point))
    (fun block _ =>
      run_caseTwoScheduledOccurrenceProgram (publishedPointwisePCPP contracts)
        caseTwo target (encodeBitInput point) block)

end NearCubicWires.CanonicalBranchSelectorProgram
