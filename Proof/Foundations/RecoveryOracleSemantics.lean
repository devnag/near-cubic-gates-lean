import Proof.Foundations.SourceCore
import Proof.Foundations.TseitinCNF
import Proof.Foundations.NestedBalancedCNFSATEncoding
import Proof.Foundations.BalancedCNFSATEncodingConservativeExtension
import StatementSupport

/-! Production statement vocabulary for the corrected recovery oracle.
These are the banked bounded-validation semantics and proofs, lifted without
changing their algorithms or resource claims. In particular the finite verifier
never expands the binary prefix count. Its ordinary encoded-length realization
and the register-to-ordinary simulator are separate LOCAL obligations.
-/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

inductive StepOutcome where
  | failed
  | done (value : Nat)
  | next (state : NPOracleState)

def stepWithOracle (oracle : Nat → Bool) (program : NPOracleProgram)
    (maximumBits : Nat) (state : NPOracleState) : StepOutcome :=
  match program[state.pc]? with
  | none => .failed
  | some (.halt outputRegister) =>
      if natBitLength (state.registers outputRegister) ≤ maximumBits then
        .done (state.registers outputRegister)
      else .failed
  | some (.set register value next) =>
      match state.boundedWrite maximumBits register value with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.copy source destination next) =>
      match state.boundedWrite maximumBits destination (state.registers source) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.increment register next) =>
      match state.boundedWrite maximumBits register (state.registers register + 1) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.decrement register next) =>
      match state.boundedWrite maximumBits register (Nat.pred (state.registers register)) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.add left right destination next) =>
      match state.boundedWrite maximumBits destination
          (state.registers left + state.registers right) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.subtract left right destination next) =>
      match state.boundedWrite maximumBits destination
          (state.registers left - state.registers right) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.pair left right destination next) =>
      match state.boundedWrite maximumBits destination
          (Nat.pair (state.registers left) (state.registers right)) with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.unpairLeft source destination next) =>
      match state.boundedWrite maximumBits destination
          (Nat.unpair (state.registers source)).1 with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.unpairRight source destination next) =>
      match state.boundedWrite maximumBits destination
          (Nat.unpair (state.registers source)).2 with
      | none => .failed
      | some nextState =>
          .next (nextState.jump next)
  | some (.branchZero register zeroTarget nonzeroTarget) =>
      .next
        (state.jump (if state.registers register = 0 then
          zeroTarget else nonzeroTarget))
  | some (.encodeNat source destination next) =>
      match state.boundedWrite maximumBits destination
          (CanonicalBinary.encodeNat (state.registers source)) with
      | none => .failed
      | some nextState =>
          .next
            (nextState.jump next)
  | some (.shiftRight source amount destination next) =>
      match state.boundedWrite maximumBits destination
          (Nat.shiftRight (state.registers source) amount) with
      | none => .failed
      | some nextState =>
          .next
            (nextState.jump next)
  | some (.shiftLeft source amount destination next) =>
      match state.boundedWrite maximumBits destination
          (Nat.shiftLeft (state.registers source) amount) with
      | none => .failed
      | some nextState =>
          .next
            (nextState.jump next)
  | some (.testBit source index destination next) =>
      match state.boundedWrite maximumBits destination
          (((state.registers source).testBit
            (state.registers index)).toNat) with
      | none => .failed
      | some nextState =>
          .next
            (nextState.jump next)
  | some (.sat queryRegister destination next) =>
      if natBitLength (state.registers queryRegister) ≤ maximumBits then
        match state.boundedWrite maximumBits destination
            (oracle (state.registers queryRegister)).toNat with
        | none => .failed
        | some nextState =>
            .next (nextState.jump next)
      else .failed

def runWithOracle (oracle : Nat → Bool) (program : NPOracleProgram)
    (maximumBits : Nat) : Nat → NPOracleState → Option Nat
  | 0, _ => none
  | fuel + 1, state =>
      match stepWithOracle oracle program maximumBits state with
      | .failed => none
      | .done value => some value
      | .next state' => runWithOracle oracle program maximumBits fuel state'

 theorem run_original (program : NPOracleProgram) (width fuel : Nat)
    (state : NPOracleState) :
    runWithOracle encodedSat program width fuel state =
      runNPOracleProgram program width fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases hi : program[state.pc]? with
    | none => simp [runWithOracle, stepWithOracle, runNPOracleProgram, hi]
    | some instruction =>
      cases instruction <;>
        simp only [runWithOracle, stepWithOracle, runNPOracleProgram, hi, NPOracleState.boundedWrite] <;>
        split_ifs <;> simp_all

 def queryAgrees (left right : Nat → Bool) (program : NPOracleProgram)
    (state : NPOracleState) : Prop :=
  match program[state.pc]? with
  | some (.sat query _ _) => left (state.registers query) = right (state.registers query)
  | _ => True

 def agreesOnRun (left right : Nat → Bool) (program : NPOracleProgram)
    (width : Nat) : Nat → NPOracleState → Prop
  | 0, _ => True
  | fuel + 1, state =>
      queryAgrees left right program state ∧
      match stepWithOracle left program width state with
      | .next state' => agreesOnRun left right program width fuel state'
      | _ => True

 theorem step_congr (left right : Nat → Bool) (program : NPOracleProgram)
    (width : Nat) (state : NPOracleState)
    (h : queryAgrees left right program state) :
    stepWithOracle left program width state = stepWithOracle right program width state := by
  cases hi : program[state.pc]? with
  | none => simp [stepWithOracle, hi]
  | some instruction =>
    cases instruction <;> simp_all [stepWithOracle, queryAgrees]

 theorem run_congr (left right : Nat → Bool) (program : NPOracleProgram)
    (width fuel : Nat) (state : NPOracleState)
    (h : agreesOnRun left right program width fuel state) :
    runWithOracle left program width fuel state =
      runWithOracle right program width fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨hquery, htail⟩ := h
    have hs := step_congr left right program width state hquery
    simp only [runWithOracle, ← hs]
    cases hout : stepWithOracle left program width state with
    | failed => rfl
    | done value => rfl
    | next nextState =>
      exact ih nextState (by simpa [hout] using htail)

theorem oracleFree_agrees (left right : Nat → Bool) (program : NPOracleProgram)
    (hfree : ExecutableInterfaces.OracleFree program) (width fuel : Nat)
    (state : NPOracleState) : agreesOnRun left right program width fuel state := by
  have hquery (state : NPOracleState) : queryAgrees left right program state := by
    cases hi : program[state.pc]? with
    | none => simp [queryAgrees, hi]
    | some instruction =>
      have hmem : instruction ∈ program := List.mem_of_getElem? hi
      have hf := (List.all_eq_true.mp hfree) instruction hmem
      cases instruction <;> simp_all [queryAgrees, ExecutableInterfaces.OracleFree]
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨hquery state, ?_⟩
    cases stepWithOracle left program width state with
    | failed => trivial
    | done value => trivial
    | next nextState => exact ih nextState

theorem oracleFree_run_congr (left right : Nat → Bool) (program : NPOracleProgram)
    (hfree : ExecutableInterfaces.OracleFree program) (width fuel : Nat)
    (state : NPOracleState) :
    runWithOracle left program width fuel state = runWithOracle right program width fuel state :=
  run_congr left right program width fuel state
    (oracleFree_agrees left right program hfree width fuel state)

open TseitinCNF BalancedCNFSATEncoding NestedBalancedCNFSATEncoding

structure CompactRequest where
  base : EncodedCNF
  committed : Nat
  count : Nat

def CompactRequest.variables (request : CompactRequest) : List Nat :=
  (request.base.flatten.map Prod.snd).eraseDups

def CompactRequest.assignment (request : CompactRequest) (witness : List Bool)
    (index : Nat) : Bool :=
  if index < request.count then request.committed.testBit index
  else witness.getD (request.variables.idxOf index) false

/-- Scans only explicit base clauses and a finite assignment witness. -/
def compactVerifier (request : CompactRequest) (witness : List Bool) : Bool :=
  witness.length = request.variables.length &&
    request.base.all (fun clause => clause.length = 3) &&
    formulaEval (request.assignment witness) request.base

def compactMeaning (request : CompactRequest) : Prop :=
  request.base.all (fun clause => clause.length = 3) = true ∧
    ∃ assignment : Nat → Bool,
      (∀ index < request.count, assignment index = request.committed.testBit index) ∧
      formulaEval assignment request.base = true

theorem assignment_on_base (request : CompactRequest) (assignment : Nat → Bool)
    (hp : ∀ index < request.count, assignment index = request.committed.testBit index)
    {clause : List (Bool × Nat)} (hc : clause ∈ request.base)
    {literal : Bool × Nat} (hl : literal ∈ clause) :
    request.assignment (request.variables.map assignment) literal.2 = assignment literal.2 := by
  have hv : literal.2 ∈ request.variables := by
    simp only [CompactRequest.variables, List.mem_eraseDups, List.mem_map]
    exact ⟨literal, List.mem_flatten.mpr ⟨clause, hc, hl⟩, rfl⟩
  by_cases hindex : literal.2 < request.count
  · simp [CompactRequest.assignment, hindex, hp _ hindex]
  · simp [CompactRequest.assignment, hindex, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_idxOf hv]

theorem compactVerifier_iff (request : CompactRequest) :
    (∃ witness : List Bool, compactVerifier request witness = true) ↔ compactMeaning request := by
  constructor
  · rintro ⟨witness, h⟩
    simp only [compactVerifier, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, request.assignment witness,
      (by intro index hi; simp [CompactRequest.assignment, hi]), h.2⟩
  · rintro ⟨hthree, assignment, hp, heval⟩
    refine ⟨request.variables.map assignment, ?_⟩
    simp only [compactVerifier, List.length_map, decide_true, Bool.true_and, hthree]
    have hcongr : formulaEval (request.assignment (request.variables.map assignment)) request.base =
        formulaEval assignment request.base := by
      unfold formulaEval clauseEval
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.any_eq_true]
      apply forall_congr'
      intro clause
      apply imp_congr_right
      intro hc
      apply exists_congr
      intro literal
      apply and_congr_right
      intro hl
      simp [literalEval, assignment_on_base request assignment hp hc hl]
    exact hcongr.trans heval

theorem prefix_eval_iff (request : CompactRequest) (assignment : Nat → Bool) :
    formulaEval assignment
      (balancedPrefixClauses request.count request.committed ++ request.base) = true ↔
      (∀ index < request.count, assignment index = request.committed.testBit index) ∧
        formulaEval assignment request.base = true := by
  simp only [formulaEval, List.all_append, Bool.and_eq_true, balancedPrefixClauses,
    List.all_map, List.all_reverse, List.all_eq_true, List.mem_range]
  apply and_congr
  · apply forall_congr'
    intro index
    apply imp_congr_right
    intro _
    cases hcommitted : request.committed.testBit index <;>
      cases hvalue : assignment index <;>
      simp [balancedPrefixUnitClause, clauseEval, literalEval, hcommitted, hvalue]
  · rfl

theorem prefix_three (request : CompactRequest) :
    (balancedPrefixClauses request.count request.committed ++ request.base).all
      (fun clause => clause.length = 3) =
    request.base.all (fun clause => clause.length = 3) := by
  simp [balancedPrefixClauses, balancedPrefixUnitClause]

theorem compactVerifier_expanded_iff (request : CompactRequest) :
    (∃ witness : List Bool, compactVerifier request witness = true) ↔
      (balancedPrefixClauses request.count request.committed ++ request.base).all
        (fun clause => clause.length = 3) = true ∧
      ∃ assignment : Nat → Bool,
        formulaEval assignment
          (balancedPrefixClauses request.count request.committed ++ request.base) = true := by
  rw [compactVerifier_iff, prefix_three]
  simp only [compactMeaning, prefix_eval_iff]

theorem mathSat_eq_encoded_of_wellSized (formula : EncodedCNF)
    (hwell : wellSizedCNFEncoding (Encodable.encode formula) formula = true) :
    mathSat formula = encodedSat (Encodable.encode formula) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [mathSat, decide_eq_true_eq]
  exact (encodedSat_encode_eq_true_iff formula hwell).symm

theorem corrected_raw (code : Nat)
    (hwell : wellSizedCNFEncoding code (decodeCNF code) = true) :
    correctedSat code = encodedSat code := by
  simp [correctedSat, encodedSat, hwell]

theorem corrected_nested (code : Nat) (formula : EncodedCNF)
    (hdecode : decodeNestedBalancedCNF code = some formula)
    (hwell : wellSizedCNFEncoding (Encodable.encode formula) formula = true) :
    correctedSat code = encodedSat code := by
  have hraw := wellSizedCNFEncoding_false_of_decodeNestedBalancedCNF hdecode
  have hflat := decodeBalancedCNF_eq_none_of_decodeNestedBalancedCNF hdecode
  have hthree : formula.all (fun clause => clause.length = 3) = true := by
    simp only [wellSizedCNFEncoding, Bool.and_eq_true, List.all_eq_true] at hwell ⊢
    intro clause hc
    exact (hwell.2 clause hc).1
  simp only [correctedSat, hraw, Bool.false_eq_true, if_false, hflat, hdecode, hthree, Bool.true_and]
  rw [mathSat_eq_encoded_of_wellSized formula hwell]
  rw [encodedSat_eq_legacyEncodedSat_of_decodeNestedBalancedCNF hdecode]
  exact BalancedCNFSATEncodingConservativeExtension.encodedSat_eq_legacyEncodedSat_of_wellSized
    (by simpa using hwell)

end NearCubicWires.RepairSource.RecoveryOracle
