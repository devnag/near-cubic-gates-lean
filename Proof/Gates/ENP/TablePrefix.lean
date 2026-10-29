import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.CaseAnalysis.RecoveryCaseQuery
import Proof.Amplification.RecoveryFormulaPrefix

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.CanonicalRecoveryLanguage NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalSATSelfReduction NearCubicWires.CircuitInputCNF NearCubicWires.TseitinCNF
open NearCubicWires.BalancedCNFSATEncoding NearCubicWires.RepairSource

/-- The lex-least accepted input of a circuit (`sec:gadget-extract`: "'first' refers to this order"). -/
structure FirstInput {n : ℕ} (c : BooleanCircuit n) where
  input : BitInput n
  accepts : c.eval input = true
  minimal : ∀ x, c.eval x = true → CanonicalBoolListLE (List.ofFn input) (List.ofFn x)

theorem existsFirstInput {n : ℕ} (c : BooleanCircuit n) (h : ∃ x, c.eval x = true) : Nonempty (FirstInput c) := by
  classical
  letI : LinearOrder (BitInput n) := LinearOrder.lift' List.ofFn List.ofFn_injective
  let eligible : Finset (BitInput n) := Finset.univ.filter fun x => c.eval x = true
  have hne : eligible.Nonempty := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, by simp [eligible, hx]⟩
  refine ⟨{ input := eligible.min' hne, accepts := ?_, minimal := ?_ }⟩
  · have hm := eligible.min'_mem hne
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · intro x hx
    exact eligible.min'_le x (by simp [eligible, hx])

/-- **Prefix self-reduction on a circuit** returns the lex-least accepted input. -/
theorem circuitPrefix_eq_first {n : ℕ} (c : BooleanCircuit n) (first : FirstInput c) (count : ℕ)
    (hcount : count ≤ n) :
    recoveredPrefix count (circuitInputFormula c) = (List.ofFn first.input).take count := by
  let formula := circuitInputFormula c
  change recoveredPrefix count formula = (List.ofFn first.input).take count
  have hwell : wellSizedCNFEncoding (Encodable.encode formula) formula = true := circuitInputFormula_wellSized c
  have hvariables : n ≤ formula.length :=
    (Nat.le_add_right _ _).trans (circuitInputVariables_le_formula_length c)
  have hrange : count ≤ natBitLength (Encodable.encode formula) :=
    hcount.trans <| hvariables.trans <| list_length_le_encoded_bitLength formula
  rcases circuitInputFormula_complete c first.input first.accepts with ⟨canonicalAssignment, hrec, hform⟩
  have hformulaSatisfiable : FormulaSatisfiable formula := ⟨canonicalAssignment, hform⟩
  have hcanonicalPrefixSatisfiable :
      FormulaSatisfiable (constrainPrefixChoices 0 formula ((List.ofFn first.input).take count)) := by
    refine ⟨canonicalAssignment, ?_⟩
    apply (formulaEval_constrainPrefixChoices_iff canonicalAssignment 0 formula _).mpr
    constructor
    · have hprefix := prefixMatches_recoveredCircuitInput_take canonicalAssignment count hcount
      rw [hrec] at hprefix
      exact hprefix
    · exact hform
  have hforward : CanonicalBoolListLE (recoveredPrefix count formula) ((List.ofFn first.input).take count) := by
    apply recoveredPrefix_lexLeast count formula hwell hrange
    · simp [hcount]
    · exact hcanonicalPrefixSatisfiable
  rcases recoveredPrefix_satisfiable count formula hwell hrange hformulaSatisfiable with ⟨assignment, hassignment⟩
  have hsemantic := (formulaEval_constrainPrefixChoices_iff assignment 0 formula
    (recoveredPrefix count formula)).mp hassignment
  have hacc : c.eval (recoveredCircuitInput (n := n) assignment) = true :=
    circuitInputFormula_sound c assignment hsemantic.2
  have hminimal := first.minimal _ hacc
  have hback : CanonicalBoolListLE ((List.ofFn first.input).take count)
      ((List.ofFn (recoveredCircuitInput (n := n) assignment)).take count) :=
    take_le_take_of_le count hminimal
  have hrecovered : recoveredPrefix count formula =
      (List.ofFn (recoveredCircuitInput (n := n) assignment)).take count := by
    have hmatches := prefixMatches_eq_take_ofFn assignment 0 (recoveredPrefix count formula) n hsemantic.1
      (by rw [recoveredPrefix_length]; exact hcount)
    change recoveredPrefix count formula = (List.ofFn fun index : Fin n => assignment index.val).take count
    simpa only [recoveredPrefix_length, Nat.zero_add] using hmatches
  rw [← hrecovered] at hback
  unfold CanonicalBoolListLE at hforward hback
  exact le_antisymm hforward hback

/-- **The SAT flag of a circuit**: the corrected oracle on the uncommitted query of its input formula. -/
theorem circuit_query {n : ℕ} (c : BooleanCircuit n) :
    RecoveryOracle.correctedSat (RecoveryQuery.code true (RecoveryFormulaPrefix.payload (circuitInputFormula c)) 0 0) =
      decide (∃ x, c.eval x = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [CloseoutRecoveryCaseQuery.uncommitted_query _ (circuitInputFormula_wellSized c), decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨_, circuitInputFormula_sound c a ha⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, _, ha⟩ := circuitInputFormula_complete c x hx
    exact ⟨a, ha⟩

end NearCubicGates.Close.ENP
