import Proof.Circuits.CircuitInputCNF
import Mathlib.Tactic

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces": exact three-literal blocks and tautological power-of-two
padding. The gate conversion is the released free-input Tseitin construction;
it is proved here from that construction, never included in a source assumption.
The circuit argument is the constant-size decision circuit of CW19 Appendix A.
Constructing that circuit uniformly from its truth table is a separate step.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the conversion preserves each fixed query-answer tuple. -/
theorem circuit_block_iff {q : ℕ} (C : BooleanCircuit q) (input : BitInput q) :
    C.eval input = true ↔
      ∃ assignment : ℕ → Bool, recoveredCircuitInput assignment = input ∧
        formulaEval assignment (circuitInputFormula C) = true := by
  constructor
  · exact circuitInputFormula_complete C input
  · rintro ⟨assignment, hinput, hformula⟩
    simpa [hinput] using circuitInputFormula_sound C assignment hformula

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": every clause is already exactly three signed literals;
unit and binary clauses in that construction repeat their literals. -/
theorem circuit_block_three {q : ℕ} (C : BooleanCircuit q)
    (clause : EncodedClause) (h : clause ∈ circuitInputFormula C) : clause.length = 3 := by
  have hall := List.all_eq_true.mp (circuitInputFormula_threeLiteral C)
  simpa using hall clause h

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a rejected answer tuple forces a false clause for every extension. -/
theorem circuit_block_rejects {q : ℕ} (C : BooleanCircuit q) (input : BitInput q)
    (hreject : C.eval input = false) (assignment : ℕ → Bool)
    (hinput : recoveredCircuitInput assignment = input) :
    ∃ clause ∈ circuitInputFormula C, clauseEval assignment clause = false := by
  by_contra h
  push Not at h
  have hall : formulaEval assignment (circuitInputFormula C) = true := by
    apply List.all_eq_true.mpr
    intro clause hclause
    simpa using h clause hclause
  have haccept := circuitInputFormula_sound C assignment hall
  rw [hinput, hreject] at haccept
  contradiction

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a tautology uses its designated dummy coordinate in three positions. -/
theorem padding_tautology (assignment : ℕ → Bool) (dummy : ℕ) :
    clauseEval assignment (circuitInputTautology dummy) = true := by
  cases h : assignment dummy <;>
    simp [circuitInputTautology, clauseEval, triple, h]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": pad a block to a common count `B` using tautologies. -/
def padClauseBlock (B dummy : ℕ) (formula : EncodedCNF) : EncodedCNF :=
  formula ++ List.replicate (B - formula.length) (circuitInputTautology dummy)

theorem padClauseBlock_length {B dummy : ℕ} (formula : EncodedCNF)
    (h : formula.length ≤ B) : (padClauseBlock B dummy formula).length = B := by
  simp only [padClauseBlock, List.length_append, List.length_replicate]
  omega

theorem padClauseBlock_eval (B dummy : ℕ) (formula : EncodedCNF)
    (assignment : ℕ → Bool) :
    formulaEval assignment (padClauseBlock B dummy formula) = formulaEval assignment formula := by
  simp [padClauseBlock, formulaEval, padding_tautology]

theorem padClauseBlock_three (B dummy : ℕ) (formula : EncodedCNF)
    (h : ∀ clause ∈ formula, clause.length = 3) :
    ∀ clause ∈ padClauseBlock B dummy formula, clause.length = 3 := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hleft | hright
  · exact h clause hleft
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hright
    rfl

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": this common count is a power of two, including zero old clauses. -/
def binaryBlockSize (bound : ℕ) : ℕ := 2 ^ Nat.clog 2 bound

theorem binaryBlockSize_ge (bound : ℕ) : bound ≤ binaryBlockSize bound :=
  Nat.le_pow_clog (by decide) bound

theorem binaryBlockSize_pos (bound : ℕ) : 0 < binaryBlockSize bound := by
  unfold binaryBlockSize
  positivity

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": rounding loses only a fixed factor for a fixed clause bound.
Proof ported from `CanonicalBinaryProgram.two_pow_clog_le`. -/
theorem binaryBlockSize_le (bound : ℕ) : binaryBlockSize bound ≤ 2 * (bound + 1) := by
  unfold binaryBlockSize
  by_cases hsmall : bound ≤ 1
  · have hclog : Nat.clog 2 bound = 0 := Nat.clog_of_right_le_one hsmall 2
    simp [hclog]
    omega
  · have hlarge : 1 < bound := by omega
    have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by omega) hlarge
    have hpositive : 0 < Nat.clog 2 bound := Nat.clog_pos (by omega) hlarge
    have heq : (Nat.clog 2 bound).pred + 1 = Nat.clog 2 bound :=
      Nat.succ_pred_eq_of_pos hpositive
    rw [← heq, pow_succ]
    nlinarith

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": padding preserves exactly the accepting assignments. -/
theorem padded_circuit_iff {q : ℕ} (C : BooleanCircuit q) (input : BitInput q)
    (B dummy : ℕ) :
    C.eval input = true ↔
      ∃ assignment : ℕ → Bool, recoveredCircuitInput assignment = input ∧
        formulaEval assignment (padClauseBlock B dummy (circuitInputFormula C)) = true := by
  simp only [padClauseBlock_eval]
  exact circuit_block_iff C input

end NearCubicGates.Adapters.Proximity
