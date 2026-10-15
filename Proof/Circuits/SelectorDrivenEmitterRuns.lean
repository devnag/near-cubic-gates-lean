import Proof.Circuits.SelectorDrivenAtomContextRuns

/-!
# The emitter runs at the selector-driven frame

Site 2a of the body-chain replay.  `BankEmittedAtomLoop.inverseEmitterRuns_ofCompiler`
assembles `InverseEmitterRuns` (the atom emitter run on the bank frame) from the
frame adapter runs and the compiler.  This module produces the same emitter — an
`encodeTaggedList` of the schedule's selector atoms beside the retained frame —
at the **selector-driven frame**, consuming `SelectorDrivenAtomContextRuns`'s
`InverseSelectorFrameAdapterRuns` (site 1, `hdiagonal`-free).

Only the emitter bits are frame-dependent; the fuel
(`inverseBankEmitterFuel`) is frame-independent and reused verbatim.
-/

namespace NearCubicWires.SelectorDrivenEmitterRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
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
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank

/-- **The atom emitter's run at the selector frame.**  Frame-shifted twin of
`InverseEmitterRuns`; the retained frame is the selector frame. -/
def InverseSelectorEmitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram emitter (emitterBits ⟨target, input⟩)
        (emitterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (Nat.pair
          (encodeTaggedList
            (inverseSelectorAtoms contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩))

/-- Width of the emitter at the selector frame: the frozen
`inverseBankEmitterBits` mirror with the selector frame retained. -/
noncomputable def inverseSelectorBankEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterBits : LanguageEvaluationRequest → ℕ) (rangeBits : ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (adapterBits request)
    (structuralAtomEmitterBits
      (rangeBits (LanguageEvaluationRequest.length request))
      (LanguageEvaluationRequest.length request)
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent (LanguageEvaluationRequest.length request)))

/-- **`InverseSelectorEmitterRuns` from the selector adapter and the compiler.**
The emitter loop is frame-independent given its arguments; the adapter supplies
the selector frame. -/
theorem inverseSelectorEmitterRuns_ofCompiler
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
      InverseSelectorFrameAdapterRuns contracts clockDepth machine
        advantageExponent pcp adapter adapterBits adapterFuel)
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
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseSelectorEmitterRuns contracts clockDepth machine advantageExponent
      (inverseBankEmitterProgram adapter)
      (inverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp adapterBits rangeBits)
      (inverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
        adapterFuel compilerFuel) := by
  intro target hlarge input
  have hloop :=
    run_structuralAtomEmitterProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target
      (inverseScheduleBound contracts clockDepth advantageExponent target)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (compilerBits target) (compilerFuel target) (hpositive target)
      (hlengthBits target) (hrangeBits target) (hlistBits target)
      (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms target] at hloop
  exact run_occurrenceStage (hadapter target hlarge input) hloop

end NearCubicWires.SelectorDrivenEmitterRuns
