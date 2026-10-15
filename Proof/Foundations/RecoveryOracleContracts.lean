import Proof.Foundations.RecoveryOracleSemantics
import StatementSupport

/-! Actual ordinary-oracle execution and the LOCAL recovery realization targets.
Finite query-control rules extend the existing local finite-tape machine. A
query is made from head zero on its fresh query tape; the framed query's
literal length plus one is charged. This conservative query convention is
polynomially equivalent to ordinary SAT-oracle time and is used only in the
refuter/recovery branches, never to justify the ordinary fast competitor.
-/
namespace NearCubicWires.RepairSource
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure OrdinaryOracleWordFunction (oracle : ℕ → Bool) (Request : Type)
    (input output : Request → List Bool) (budget : Request → ℕ) where
  program : OrdinaryOracleProgram
  realizes : ∀ request, OrdinaryOracleRuns oracle program
    (input request) (output request) (budget request)

/-- LOCAL simulator target, including reading/framing the language input,
computing its length and initial binary registers, all queries and output.
The polynomial may depend on the one fixed program. -/
structure RegisterLanguageSimulation (oracle : ℕ → Bool) where
  translate : NPOracleProgram → OrdinaryOracleProgram
  coefficient : NPOracleProgram → ℕ
  coefficientPositive : ∀ program, 1 ≤ coefficient program
  degree : NPOracleProgram → ℕ
  realizes : ∀ (program : NPOracleProgram) (width fuel n : ℕ)
    (input : BitInput n) (output : ℕ),
    RecoveryOracle.runWithOracle oracle program width fuel
      (initialNPOracleState n (encodeBitInput input)) = some output →
    OrdinaryOracleRuns oracle (translate program) (List.ofFn input) output.bits
      (coefficient program * (fuel + 1) * (width + n + 1) ^ degree program)

/-- The recovered language is the output of one fixed corrected-oracle stream,
including the bounded malformed/zero-length branches. -/
structure RecoveryProgramCertificate (language : Language) where
  program : NPOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    RecoveryOracle.runWithOracle RecoveryOracle.correctedSat program
      (2 ^ (exponent * max 1 n)) (2 ^ (exponent * max 1 n))
      (initialNPOracleState n (encodeBitInput input)) = some (language n input).toNat

/-- Literal ordinary exponential time with an NP oracle. The max convention
only fixes the finite zero-length cost; it changes no asymptotic class. -/
def OrdinaryInENP (language : Language) : Prop :=
  ∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
    Nonempty (OrdinaryENPCertificate oracle language)

theorem OrdinaryOracleRuns.enlarge {oracle : ℕ → Bool} {program : OrdinaryOracleProgram}
    {input output : List Bool} {budget larger : ℕ}
    (run : OrdinaryOracleRuns oracle program input output budget) (h : budget ≤ larger) :
    OrdinaryOracleRuns oracle program input output larger := by
  obtain ⟨cost, final, hcost, trace, halted, result⟩ := run
  exact ⟨cost, final, hcost.trans h, trace, halted, result⟩

/-- Coarse bit simulation is sufficient at E^NP; this is not an o(T) claim. -/
theorem recovery_simulation_bound (coefficient degree exponent n : ℕ)
    (he : 1 ≤ exponent) :
    coefficient * (2 ^ (exponent * max 1 n) + 1) *
      (2 ^ (exponent * max 1 n) + n + 1) ^ degree ≤
    2 ^ (((exponent + 1) * (degree + 1) + coefficient) * max 1 n) := by
  let m := max 1 n
  have hm : 1 ≤ m := Nat.le_max_left _ _
  have hn : n ≤ m := Nat.le_max_right _ _
  have heprod : m ≤ exponent * m := by nlinarith
  have hexp : m + 1 ≤ 2 ^ (exponent * m) :=
    (Nat.succ_le_of_lt (show m < 2 ^ m from Nat.lt_two_pow_self)).trans
      (Nat.pow_le_pow_right (by decide) heprod)
  have hfirst : 2 ^ (exponent * m) + 1 ≤ 2 * 2 ^ (exponent * m) := by omega
  have hsecond : 2 ^ (exponent * m) + n + 1 ≤ 2 * 2 ^ (exponent * m) := by omega
  have hcoefficient : coefficient ≤ 2 ^ coefficient :=
    (show coefficient < 2 ^ coefficient from Nat.lt_two_pow_self).le
  have hpower : 2 * 2 ^ (exponent * m) = 2 ^ (exponent * m + 1) := by
    rw [pow_succ]
    omega
  change coefficient * (2 ^ (exponent * m) + 1) *
      (2 ^ (exponent * m) + n + 1) ^ degree ≤ _
  calc
    _ ≤ 2 ^ coefficient * (2 * 2 ^ (exponent * m)) *
        (2 * 2 ^ (exponent * m)) ^ degree :=
      Nat.mul_le_mul (Nat.mul_le_mul hcoefficient hfirst)
        (Nat.pow_le_pow_left hsecond degree)
    _ = 2 ^ (coefficient + (exponent * m + 1) * (degree + 1)) := by
      rw [hpower, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have h1 : exponent * m + 1 ≤ (exponent + 1) * m := by nlinarith
      have h2 := Nat.mul_le_mul_right (degree + 1) h1
      have h3 : coefficient ≤ coefficient * m := by nlinarith
      change coefficient + (exponent * m + 1) * (degree + 1) ≤
        ((exponent + 1) * (degree + 1) + coefficient) * m
      calc
        _ ≤ coefficient * m + (exponent + 1) * m * (degree + 1) :=
          Nat.add_le_add h3 h2
        _ = _ := by ring)

/-- Enclosing local application. NP membership and the ordinary simulator must
be proved locally, not appended as a ninth source assumption. -/
theorem recovery_ordinaryInENP {language : Language}
    (np : EncodedNPVerifier RecoveryOracle.correctedSat)
    (simulation : RegisterLanguageSimulation RecoveryOracle.correctedSat)
    (certificate : RecoveryProgramCertificate language) : OrdinaryInENP language := by
  let degree := simulation.degree certificate.program
  let coefficient := simulation.coefficient certificate.program
  let exponent := (certificate.exponent + 1) * (degree + 1) + coefficient
  have he : 1 ≤ exponent := by
    dsimp only [exponent]
    nlinarith [simulation.coefficientPositive certificate.program]
  refine ⟨RecoveryOracle.correctedSat, ⟨np⟩, ⟨{
    program := simulation.translate certificate.program
    exponent := exponent
    exponentPositive := he
    computes := ?_ }⟩⟩
  intro n input
  have hrun := simulation.realizes certificate.program
    (2 ^ (certificate.exponent * max 1 n)) (2 ^ (certificate.exponent * max 1 n))
    n input (language n input).toNat (certificate.computes n input)
  exact hrun.enlarge
    (recovery_simulation_bound coefficient degree certificate.exponent n certificate.exponentPositive)

end NearCubicWires.RepairSource
