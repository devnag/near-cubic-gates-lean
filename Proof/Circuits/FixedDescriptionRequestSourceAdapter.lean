import Proof.CaseAnalysis.CaseTwoCanonicalCircuitEncoder
import Proof.Circuits.FixedSelectorAtomContextRuns
import Proof.Circuits.SelectorDrivenLengthStage

/-!
# Fixed description-request source adapter

The selector-driven numeral bank loads its closed frame from the public target.
The ordinary linker then enters one frame-local body with the same public input
length in `r1`.  This module exposes only that ABI seam and the canonical
circuit-description request it returns.
-/

namespace NearCubicWires.FixedDescriptionRequestSourceAdapter

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedSelectorAtomContextReplay
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The public target-code firewall -/

/-- The unique bounded bit input whose code is the public target itself. -/
def fixedTargetCodeInput (target : ℕ) : BitInput target :=
  fun bit => target.testBit bit.val

@[simp] theorem encode_fixedTargetCodeInput (target : ℕ) :
    encodeBitInput (fixedTargetCodeInput target) = target :=
  encodeBitInput_testBit Nat.lt_two_pow_self

@[simp] theorem encode_fixedTargetCodeInput_zero :
    encodeBitInput (fixedTargetCodeInput 0) = 0 := by
  exact encode_fixedTargetCodeInput 0

/-- Out-of-range raw words cannot enter the trusted target-code path.  This is
the malformed-request firewall; the source theorem below makes no execution
claim for such a raw word. -/
theorem malformed_raw_ne_fixedTargetCode
    {target raw : ℕ} (hmalformed : 2 ^ target ≤ raw) :
    raw ≠ encodeBitInput (fixedTargetCodeInput target) := by
  rw [encode_fixedTargetCodeInput]
  exact ne_of_gt (Nat.lt_two_pow_self.trans_le hmalformed)

/-! ## 2. The exact description request -/

noncomputable def fixedCanonicalDescriptionRequest
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) : ℕ :=
  canonicalCircuitEncoderInput
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate))

/-- A frame-local body produces only the canonical description request.  Its
entry frame is exactly the frame consumed by the existing fixed selector
emitter, and its public input-length channel remains `r1 = target`. -/
def FixedDescriptionRequestAtSelectorFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram) (bodyBits bodyFuel : ℕ → ℕ) : Prop :=
  ∀ target : ℕ,
    fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
      target →
    runNPOracleProgram body (bodyBits target) (bodyFuel target)
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, fixedTargetCodeInput target⟩)) =
      some
        (fixedCanonicalDescriptionRequest contracts clockDepth machine
          requestedRate target)

/-! ## 3. Load the selector frame from `(target, target)` -/

noncomputable def fixedDescriptionRequestSourceProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (publishedSourceDrivenBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate)
      (fixedLengthProgram contracts clockDepth requestedRate))
    body

noncomputable def fixedDescriptionRequestSourceBits
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (bodyBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (publishedSourceDrivenBankBits
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) target
      (fixedLengthBits contracts clockDepth requestedRate
        ⟨target, fixedTargetCodeInput target⟩)
      (fixedScheduleLength contracts clockDepth requestedRate target) target)
    (bodyBits target)

noncomputable def fixedDescriptionRequestSourceFuel
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram) (bodyFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel body
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate)
      (fixedLengthFuel contracts clockDepth requestedRate
        ⟨target, fixedTargetCodeInput target⟩)
      (fixedScheduleLength contracts clockDepth requestedRate target))
    (bodyFuel target)

/-- The smallest source-adapter theorem: the closed selector bank loads the
fixed emitter frame, and the linker hands that frame to the body while retaining
the public target in `r1`.  The only output is the canonical description
request. -/
theorem run_fixedDescriptionRequestSourceProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram) (bodyBits bodyFuel : ℕ → ℕ)
    (hbody : FixedDescriptionRequestAtSelectorFrame contracts clockDepth
      machine requestedRate body bodyBits bodyFuel)
    (target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target) :
    runNPOracleProgram
        (fixedDescriptionRequestSourceProgram contracts clockDepth requestedRate
          body)
        (fixedDescriptionRequestSourceBits contracts clockDepth requestedRate
          bodyBits target)
        (fixedDescriptionRequestSourceFuel contracts clockDepth requestedRate
          body bodyFuel target)
        (initialNPOracleState target target) =
      some
        (fixedCanonicalDescriptionRequest contracts clockDepth machine
          requestedRate target) := by
  have hbank := run_fixedSelectorBank_closed contracts clockDepth requestedRate
    target (fixedTargetCodeInput target)
  have hbank' :
      runNPOracleProgram
          (publishedSourceDrivenBankProgram
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (fixedLengthProgram contracts clockDepth requestedRate))
          (publishedSourceDrivenBankBits
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (fixedLengthBits contracts clockDepth requestedRate
              ⟨target, fixedTargetCodeInput target⟩)
            (fixedScheduleLength contracts clockDepth requestedRate target)
            target)
          (publishedSourceDrivenBankFuel
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (fixedLengthFuel contracts clockDepth requestedRate
              ⟨target, fixedTargetCodeInput target⟩)
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (initialNPOracleState target target) =
        some
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, fixedTargetCodeInput target⟩) := by
    simpa [fixedSelectorAdapterFrame, LanguageEvaluationRequest.length,
      LanguageEvaluationRequest.code] using hbank
  rw [fixedDescriptionRequestSourceProgram,
    fixedDescriptionRequestSourceBits, fixedDescriptionRequestSourceFuel]
  exact run_occurrenceStage hbank' (hbody target hlarge)

end NearCubicWires.FixedDescriptionRequestSourceAdapter
