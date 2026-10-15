import Proof.MachineModel.BankCaseTwoEnvelopeClosure
import Proof.Circuits.SelectorDrivenBodyClosure

/-!
# Programs and envelopes for direct inverse selector target chains

The selector body already starts at scheduled numeral registers.  These two
programs are the register-driven branch bodies without the old
request-length-indexed `uniformTargetProgram` wrapper, and the two maxima are
their shared dispatcher envelope.
-/

namespace NearCubicWires.SelectorDrivenRegisterTargetChainBase

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

noncomputable def inverseSelectorCaseOneProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (row : NPOracleProgram) :
    NPOracleProgram :=
  bankRegisterCaseOneTargetBitProgram (publishedAmplifier contracts).algorithm
    (publishedRefuterSource contracts clockDepth).refuter.runner.program row
    machine.description clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent

noncomputable def inverseSelectorCaseTwoProgram
    (contracts : PublishedContracts) (occurrence : NPOracleProgram) :
    NPOracleProgram :=
  inverseChainTwoBodyProgram contracts occurrence

noncomputable def inverseSelectorDirectChainBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (rowBits occurrenceBits : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (inverseChainOneBodyBits contracts clockDepth machine advantageExponent
      rowBits request)
    (inverseCaseTwoBodyBits contracts clockDepth machine advantageExponent
      occurrenceBits request)

noncomputable def inverseSelectorDirectChainFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row occurrence : NPOracleProgram)
    (rowFuel occurrenceFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (inverseChainOneBodyFuel contracts clockDepth machine advantageExponent row
      rowFuel request)
    (inverseCaseTwoBodyFuel contracts clockDepth machine advantageExponent
      occurrence occurrenceFuel request)

theorem run_fuel_mono {program : NPOracleProgram}
    {maximumBits fuel target : ℕ} {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program maximumBits fuel state = some output)
    (hfuel : fuel ≤ target) :
    runNPOracleProgram program maximumBits target state = some output := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hexec extra

end NearCubicWires.SelectorDrivenRegisterTargetChainBase
