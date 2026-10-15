import Proof.Foundations.RecoverySourceSAT

/-! A total finite witness checker for the exact corrected SAT predicate.
The binary committed-prefix count is retained as a number: no execution of
the checker constructs prefix clauses. The expanding operation below occurs
only in its semantic specification and correctness proofs. An actual ordinary
machine and its encoded-length polynomial clock remain separate local work. -/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CanonicalBinary BalancedCNFSATEncoding TseitinCNF
open private legacyDecodeCNF decodeClauseCodes from StatementSupport

def decodeFlatCompact (code : Nat) : Option CompactRequest :=
  match decodeCNF code with
  | [[], [(true, payload)]] =>
      (decodeBalancedList payload).map fun clauses =>
        ⟨decodeClauseCodes clauses, 0, 0⟩
  | [[], [(true, payload)], [(false, assignment), (true, count)]] =>
      (decodeBalancedList payload).map fun clauses =>
        ⟨decodeClauseCodes clauses, assignment, count⟩
  | _ => none

def decodeNestedCompact (code : Nat) : Option CompactRequest :=
  match decodeCNF code with
  | [[], [(false, payload)]] =>
      (decodeNestedBalancedCNFPayload payload).map fun clauses =>
        ⟨decodeClauseCodes clauses, 0, 0⟩
  | [[], [(false, payload)], [(false, assignment), (true, count)]] =>
      (decodeNestedBalancedCNFPayload payload).map fun clauses =>
        ⟨decodeClauseCodes clauses, assignment, count⟩
  | _ => none

/-- Specification only; the executable checker never calls this operation. -/
def CompactRequest.expanded (request : CompactRequest) : EncodedCNF :=
  balancedPrefixClauses request.count request.committed ++ request.base

theorem decodeFlatCompact_expanded (code : Nat) :
    (decodeFlatCompact code).map CompactRequest.expanded = decodeBalancedCNF code := by
  unfold decodeFlatCompact decodeBalancedCNF legacyDecodeCNF decodeCNF
  cases Encodable.decode (α := EncodedCNF) code
  · rfl
  split <;> simp_all only [Option.map_none]
  all_goals
    cases decodeBalancedList _ <;>
      simp [CompactRequest.expanded, decodeClauseCodes, balancedPrefixClauses]

theorem decodeNestedCompact_expanded (code : Nat) :
    (decodeNestedCompact code).map CompactRequest.expanded = decodeNestedBalancedCNF code := by
  unfold decodeNestedCompact decodeNestedBalancedCNF decodeCNF
  cases Encodable.decode (α := EncodedCNF) code <;> simp only [Option.getD_none, Option.getD_some]
  · rfl
  split <;> simp_all only [Option.map_none]
  all_goals
    cases decodeNestedBalancedCNFPayload _ <;>
      simp [CompactRequest.expanded, balancedPrefixClauses]

theorem compactVerifier_mathSat (request : CompactRequest) :
    (∃ witness, compactVerifier request witness = true) ↔
      (request.expanded.all (fun clause => clause.length = 3) &&
        mathSat request.expanded) = true := by
  classical
  simpa only [CompactRequest.expanded, Bool.and_eq_true, mathSat,
    decide_eq_true_eq] using compactVerifier_expanded_iff request

theorem legacySat_wellSized_iff (code : Nat)
    (hwell : wellSizedCNFEncoding code (decodeCNF code) = true) :
    legacyEncodedSat code = true ↔
      ∃ assignment : Nat → Bool, formulaEval assignment (decodeCNF code) = true := by
  unfold legacyEncodedSat
  rw [if_pos hwell, List.any_eq_true]
  constructor
  · rintro ⟨assignmentCode, _, haccepts⟩
    let assignment : Nat → Bool := fun index => assignmentCode.testBit index
    refine ⟨assignment, ?_⟩
    have heval := encodedCNFEval_restrictAssignment (decodeCNF code) assignment
    simpa [assignment, restrictAssignment] using heval.symm.trans haccepts
  · rintro ⟨assignment, haccepts⟩
    let finiteAssignment := restrictAssignment (decodeCNF code) assignment
    let assignmentCode := bitAssignmentCode finiteAssignment
    refine ⟨assignmentCode,
      List.mem_range.mpr (bitAssignmentCode_lt_two_pow finiteAssignment), ?_⟩
    have heq : (fun index : Fin (cnfVariableCount (decodeCNF code)) =>
        assignmentCode.testBit index.val) = finiteAssignment := by
      funext index
      exact bitAssignmentCode_testBit finiteAssignment index
    rw [heq]
    exact (encodedCNFEval_restrictAssignment (decodeCNF code) assignment).trans haccepts

/-- Total reference checker. Dispatch retains the corrected oracle's exact
raw, flat, nested precedence, including malformed inputs. -/
def correctedWitnessVerifier (code : Nat) (witness : List Bool) : Bool :=
  if wellSizedCNFEncoding code (decodeCNF code) then
    compactVerifier ⟨decodeCNF code, 0, 0⟩ witness
  else
    match decodeFlatCompact code with
    | some request => compactVerifier request witness
    | none => match decodeNestedCompact code with
      | some request => compactVerifier request witness
      | none => false

theorem correctedWitnessVerifier_iff (code : Nat) :
    (∃ witness : List Bool, correctedWitnessVerifier code witness = true) ↔
      correctedSat code = true := by
  by_cases hraw : wellSizedCNFEncoding code (decodeCNF code) = true
  · have hthree : (decodeCNF code).all (fun clause => clause.length = 3) = true := by
      simp only [wellSizedCNFEncoding, Bool.and_eq_true, List.all_eq_true] at hraw ⊢
      intro clause hc
      exact (hraw.2 clause hc).1
    simp only [correctedWitnessVerifier, correctedSat, if_pos hraw]
    rw [compactVerifier_iff, legacySat_wellSized_iff code hraw]
    simp [compactMeaning, hthree]
  · simp only [correctedWitnessVerifier, correctedSat, if_neg hraw]
    have hflat := decodeFlatCompact_expanded code
    have hnested := decodeNestedCompact_expanded code
    cases hf : decodeFlatCompact code with
    | some request =>
      simp only [hf, Option.map_some] at hflat
      rw [← hflat]
      exact compactVerifier_mathSat request
    | none =>
      simp only [hf, Option.map_none] at hflat
      rw [← hflat]
      cases hn : decodeNestedCompact code with
      | some request =>
        simp only [hn, Option.map_some] at hnested
        rw [← hnested]
        exact compactVerifier_mathSat request
      | none =>
        simp only [hn, Option.map_none] at hnested
        simp [← hnested]

end NearCubicWires.RepairSource.RecoveryOracle
