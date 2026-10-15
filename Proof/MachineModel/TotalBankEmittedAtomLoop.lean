import Proof.Circuits.TotalInverseCompilerRuns
import Proof.MachineModel.TotalStructuralAtomEmitterProgram

/-!
# The guarded atom loop at the numeral bank frame

The frame adapter and schedule presentation contracts are unchanged.  This
module exposes the emitter in the bank linker, installs the total structural
atom emitter, and consumes the `InverseCompilerRuns`-shaped guarded schedule
proposition.
-/

namespace NearCubicWires.TotalBankEmittedAtomLoop

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.TotalStructuralAtomEmitterProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Program-parametric bank linking -/

/-- One frame adapter followed by an explicitly supplied atom emitter. -/
def inverseBankEmitterProgramFor
    (emitterProgram adapter : NPOracleProgram) : NPOracleProgram :=
  linkPrograms adapter emitterProgram

/-- The bank linker with the total structural atom emitter installed. -/
def totalInverseBankEmitterProgram (adapter : NPOracleProgram) :
    NPOracleProgram :=
  inverseBankEmitterProgramFor totalStructuralAtomEmitterProgram adapter

/-- The unchanged two-stage bank width composition. -/
noncomputable def inverseBankEmitterBitsFor
    (adapterBits emitterBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (adapterBits request) (emitterBits request)

/-- The linker fuel with emitter ownership exposed. -/
noncomputable def inverseBankEmitterFuelFor
    (emitterProgram : NPOracleProgram)
    (adapterFuel emitterFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel emitterProgram (adapterFuel request) (emitterFuel request)

/-! ## 2. Exact guarded resource functions -/

noncomputable def totalInverseAtomEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (request : LanguageEvaluationRequest) : ℕ :=
  totalStructuralAtomEmitterBits
    (rangeBits (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.length request)
    (inverseAtomCount contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))
    (inverseAtomContext contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))
    (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (inverseSelectorAtoms contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent (LanguageEvaluationRequest.length request))

noncomputable def totalInverseAtomEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  totalStructuralAtomEmitterFuel
    (LanguageEvaluationRequest.length request)
    (inverseAtomCount contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))
    (inverseAtomContext contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))
    (totalStructuralAtomCalleeRequestFuel
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          (LanguageEvaluationRequest.length request)))
      (pcp.nativeWidth
        (inverseScheduleLength contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request)))
      (pcp.queryCount
        (inverseScheduleLength contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request)))
      (inverseScheduleBound contracts clockDepth advantageExponent
        (LanguageEvaluationRequest.length request))
      (compilerFuel (LanguageEvaluationRequest.length request)))
    (inverseSelectorAtoms contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent (LanguageEvaluationRequest.length request))

/-- The guarded bank-emitter width under the old bank resource ABI. -/
noncomputable def totalInverseBankEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterBits : LanguageEvaluationRequest → ℕ) (rangeBits : ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  inverseBankEmitterBitsFor adapterBits
    (totalInverseAtomEmitterBits contracts clockDepth machine advantageExponent
      pcp rangeBits)
    request

/-- The guarded bank-emitter fuel under the old bank resource ABI. -/
noncomputable def totalInverseBankEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  inverseBankEmitterFuelFor totalStructuralAtomEmitterProgram adapterFuel
    (totalInverseAtomEmitterFuel contracts clockDepth machine advantageExponent
      pcp compilerFuel)
    request

/-! ## 3. The bank emitter from guarded schedule compiler runs -/

/-- **The selector's bank-framed emitter premise, guarded.**  The conclusion
is the existing `InverseEmitterRuns` interface, so downstream bank consumers
need no new proposition.  The compiler premise is its total
`InverseCompilerRuns`-shaped replacement and has no query-count positivity
side condition. -/
theorem totalInverseEmitterRuns_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hatoms :
      InverseScheduleAtomsAgree contracts clockDepth machine advantageExponent
        pcp)
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseFrameAdapterRuns contracts clockDepth machine advantageExponent pcp
        adapter adapterBits adapterFuel)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)
              (inverseScheduleBound contracts clockDepth advantageExponent
                target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    InverseEmitterRuns contracts clockDepth machine advantageExponent
      (totalInverseBankEmitterProgram adapter)
      (totalInverseBankEmitterBits contracts clockDepth machine
        advantageExponent pcp adapterBits rangeBits)
      (totalInverseBankEmitterFuel contracts clockDepth machine
        advantageExponent pcp adapterFuel compilerFuel) := by
  intro target hlarge input
  have hloop :=
    run_totalStructuralAtomEmitterProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target
      (inverseScheduleBound contracts clockDepth advantageExponent target)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target
        (encodeBitInput input))
      (compilerBits target) (compilerFuel target) (hpositive target)
      (hlengthBits target) (hrangeBits target) (hlistBits target)
      (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms target] at hloop
  exact run_occurrenceStage (hadapter target hlarge input) hloop

end NearCubicWires.TotalBankEmittedAtomLoop
