import Proof.Circuits.BoundedOracleStructuralCircuit
import Proof.Circuits.CanonicalSATSelfReduction
import Proof.Circuits.CircuitInputCNF
import Proof.Foundations.OuterPCPRecovery

/-!
# Canonical Appendix-C recovery language

This module owns the formula-level C.12 construction.  The outer-proof branch
uses the PCP proof-table coordinates directly as SAT variables; no encoded
wrapper order is introduced.  The executable layer below this semantic seam
uses the same formula and the zero-first self-reducer.
-/

namespace NearCubicWires.CanonicalRecoveryLanguage

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputCNF
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TseitinCNF

def bitInputOfCode (width code : ℕ) : BitInput width :=
  fun bit => code.testBit bit.val

def allBitInputs (width : ℕ) : List (BitInput width) :=
  (List.range (2 ^ width)).map (bitInputOfCode width)

@[simp] theorem allBitInputs_length (width : ℕ) :
    (allBitInputs width).length = 2 ^ width := by
  simp [allBitInputs]

theorem bitInputOfCode_encodeBitInput {width : ℕ}
    (input : BitInput width) :
    bitInputOfCode width (encodeBitInput input) = input := by
  funext bit
  unfold bitInputOfCode
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt input bit.val bit.isLt

theorem encodeBitInput_lt_pow {width : ℕ} (input : BitInput width) :
    encodeBitInput input < 2 ^ width := by
  rw [encodeBitInput_eq_ofBits]
  exact Nat.ofBits_lt_two_pow input

@[simp] theorem mem_allBitInputs {width : ℕ} (input : BitInput width) :
    input ∈ allBitInputs width := by
  rw [allBitInputs, List.mem_map]
  exact
    ⟨encodeBitInput input,
      List.mem_range.mpr (encodeBitInput_lt_pow input),
      bitInputOfCode_encodeBitInput input⟩

def outerProofLiteral
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    Literal (pcp.queryCount n) → EncodedLiteral
  | .positive query =>
      positive (pcp.queryAddress input randomness query).val
  | .negative query =>
      negative (pcp.queryAddress input randomness query).val

def outerProofClause
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3 → Literal (pcp.queryCount n)) : EncodedClause :=
  triple
    (outerProofLiteral pcp input randomness (clause 0))
    (outerProofLiteral pcp input randomness (clause 1))
    (outerProofLiteral pcp input randomness (clause 2))

def outerProofRowFormula
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) : EncodedCNF :=
  (pcp.decision input randomness).clauses.map
    (outerProofClause pcp input randomness)

def outerProofRecoveryFormula
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : EncodedCNF :=
  circuitInputTautologies (2 ^ pcp.nativeWidth n) ++
    (allBitInputs (pcp.nativeWidth n)).flatMap
      (outerProofRowFormula pcp input)

def proofAssignment
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (assignment : ℕ → Bool) :
    BitInput (2 ^ pcp.nativeWidth n) :=
  fun index => assignment index.val

@[simp] theorem literalEval_outerProofLiteral
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (assignment : ℕ → Bool)
    (literal : Literal (pcp.queryCount n)) :
    literalEval assignment
        (outerProofLiteral pcp input randomness literal) =
      literal.eval (fun query =>
        proofAssignment pcp assignment
          (pcp.queryAddress input randomness query)) := by
  cases literal <;> rfl

theorem clauseEval_outerProofClause
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (assignment : ℕ → Bool)
    (clause : Fin 3 → Literal (pcp.queryCount n)) :
    clauseEval assignment
        (outerProofClause pcp input randomness clause) =
      decide (∃ index, (clause index).eval (fun query =>
        proofAssignment pcp assignment
          (pcp.queryAddress input randomness query)) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [outerProofClause, clauseEval, triple, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_true,
    literalEval_outerProofLiteral, decide_eq_true_eq]
  constructor
  · rintro (hzero | hone | htwo)
    · exact ⟨0, hzero⟩
    · exact ⟨1, hone⟩
    · exact ⟨2, htwo⟩
  · rintro ⟨index, hindex⟩
    fin_cases index
    · exact Or.inl hindex
    · exact Or.inr (Or.inl hindex)
    · exact Or.inr (Or.inr hindex)

theorem formulaEval_outerProofRowFormula
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (assignment : ℕ → Bool) :
    formulaEval assignment
        (outerProofRowFormula pcp input randomness) =
      pcp.accepts input (proofAssignment pcp assignment) randomness := by
  simp only [outerProofRowFormula, formulaEval, ProjectionPCP.accepts,
    ThreeCNF.eval, List.all_map]
  apply congrArg
    (fun predicate =>
      (pcp.decision input randomness).clauses.all predicate)
  funext clause
  exact clauseEval_outerProofClause pcp input randomness assignment clause

theorem formulaEval_flatMap_iff
    (assignment : ℕ → Bool) {α : Type}
    (values : List α) (part : α → EncodedCNF) :
    formulaEval assignment (values.flatMap part) = true ↔
      ∀ value ∈ values, formulaEval assignment (part value) = true := by
  induction values with
  | nil =>
      constructor
      · intro _ value hmember
        nomatch hmember
      · intro _
        rfl
  | cons value rest ih =>
      rw [List.flatMap_cons, formulaEval_append, ih]
      simp only [List.mem_cons, forall_eq_or_imp]

theorem listAll_flatMap_iff {α β : Type}
    (values : List α) (part : α → List β) (predicate : β → Bool) :
    (values.flatMap part).all predicate = true ↔
      ∀ value ∈ values, (part value).all predicate = true := by
  induction values with
  | nil =>
      constructor
      · intro _ value hmember
        nomatch hmember
      · intro _
        rfl
  | cons value rest ih =>
      rw [List.flatMap_cons, List.all_append, Bool.and_eq_true, ih]
      simp only [List.mem_cons, forall_eq_or_imp]

theorem outerProofRecoveryFormula_eval_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (assignment : ℕ → Bool) :
    formulaEval assignment (outerProofRecoveryFormula pcp input) = true ↔
      ∀ randomness,
        pcp.accepts input (proofAssignment pcp assignment) randomness = true := by
  unfold outerProofRecoveryFormula
  rw [formulaEval_append]
  constructor
  · rintro ⟨_htautologies, hrows⟩ randomness
    have hrow :=
      (formulaEval_flatMap_iff assignment
        (allBitInputs (pcp.nativeWidth n))
        (outerProofRowFormula pcp input)).mp hrows
        randomness (mem_allBitInputs randomness)
    rwa [formulaEval_outerProofRowFormula] at hrow
  · intro haccepts
    constructor
    · exact circuitInputTautologies_eval _ assignment
    · apply
        (formulaEval_flatMap_iff assignment
          (allBitInputs (pcp.nativeWidth n))
          (outerProofRowFormula pcp input)).mpr
      intro randomness _hrandomness
      rw [formulaEval_outerProofRowFormula]
      exact haccepts randomness

def bitInputAssignment {count : ℕ}
    (input : BitInput count) (index : ℕ) : Bool :=
  if hindex : index < count then input ⟨index, hindex⟩ else false

@[simp] theorem proofAssignment_bitInputAssignment
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (proof : BitInput (2 ^ pcp.nativeWidth n)) :
    proofAssignment pcp (bitInputAssignment proof) = proof := by
  funext index
  simp [proofAssignment, bitInputAssignment, index.isLt]

theorem outerProofRecoveryFormula_satisfiable_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    FormulaSatisfiable (outerProofRecoveryFormula pcp input) ↔
      ∃ proof : BitInput (2 ^ pcp.nativeWidth n),
        ∀ randomness, pcp.accepts input proof randomness := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    refine ⟨proofAssignment pcp assignment, ?_⟩
    exact (outerProofRecoveryFormula_eval_iff pcp input assignment).mp
      hsatisfies
  · rintro ⟨proof, haccepts⟩
    refine ⟨bitInputAssignment proof, ?_⟩
    apply (outerProofRecoveryFormula_eval_iff pcp input _).mpr
    simpa only [proofAssignment_bitInputAssignment] using haccepts

/-! ## Prefix semantics and canonicality -/

/-- The semantic meaning of the unit clauses committed by the self-reducer.
Keeping the starting coordinate explicit makes the invariant reusable at
every recursive call without introducing a second assignment representation. -/
def PrefixMatches (assignment : ℕ → Bool) :
    ℕ → List Bool → Prop
  | _index, [] => True
  | index, value :: rest =>
      assignment index = value ∧
        PrefixMatches assignment (index + 1) rest

theorem formulaEval_constrainPrefixChoices_iff
    (assignment : ℕ → Bool) (index : ℕ)
    (formula : EncodedCNF) (choices : List Bool) :
    formulaEval assignment
        (constrainPrefixChoices index formula choices) = true ↔
      PrefixMatches assignment index choices ∧
        formulaEval assignment formula = true := by
  induction choices generalizing index formula with
  | nil =>
      simp only [constrainPrefixChoices, PrefixMatches, true_and]
  | cons value rest ih =>
      rw [constrainPrefixChoices, ih,
        formulaEval_constrainPrefixBit]
      constructor
      · rintro ⟨htail, hvalue, hformula⟩
        exact ⟨⟨hvalue, htail⟩, hformula⟩
      · rintro ⟨⟨hvalue, htail⟩, hformula⟩
        exact ⟨htail, hvalue, hformula⟩

theorem prefixMatches_eq_take_ofFn
    (assignment : ℕ → Bool) (start : ℕ)
    (choices : List Bool) (variableCount : ℕ)
    (hmatches : PrefixMatches assignment start choices)
    (hbound : choices.length ≤ variableCount) :
    choices =
      (List.ofFn fun index : Fin variableCount =>
        assignment (start + index.val)).take choices.length := by
  induction choices generalizing start variableCount with
  | nil =>
      rfl
  | cons value rest ih =>
      cases variableCount with
      | zero =>
          simp only [List.length_cons] at hbound
          omega
      | succ variableCount =>
          rcases hmatches with ⟨hvalue, hrest⟩
          have hrestBound : rest.length ≤ variableCount := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using
              hbound
          have htail :=
            ih (start + 1) variableCount hrest hrestBound
          rw [List.ofFn_succ, List.length_cons, List.take_succ_cons]
          apply congrArg₂ List.cons
          · simpa only [Fin.val_zero, Nat.add_zero] using hvalue.symm
          · simpa [Fin.succ, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using htail

theorem prefixMatches_take_ofFn
    (assignment : ℕ → Bool) (start variableCount count : ℕ)
    (hbound : count ≤ variableCount) :
    PrefixMatches assignment start
      ((List.ofFn fun index : Fin variableCount =>
        assignment (start + index.val)).take count) := by
  induction count generalizing start variableCount with
  | zero =>
      simp only [List.take, PrefixMatches]
  | succ count ih =>
      cases variableCount with
      | zero =>
          omega
      | succ variableCount =>
          have htailBound : count ≤ variableCount := by
            omega
          rw [List.ofFn_succ, List.take_succ_cons]
          constructor
          · simp only [Fin.val_zero, Nat.add_zero]
          · simpa [Fin.succ, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              ih (start + 1) variableCount htailBound

theorem prefixMatches_bitInputAssignment_take
    {count : ℕ} (proof : BitInput count)
    (prefixLength : ℕ) (hbound : prefixLength ≤ count) :
    PrefixMatches (bitInputAssignment proof) 0
      ((List.ofFn proof).take prefixLength) := by
  have hmatches :=
    prefixMatches_take_ofFn (bitInputAssignment proof) 0 count
      prefixLength hbound
  have hfunctions :
      (fun index : Fin count =>
        bitInputAssignment proof (0 + index.val)) = proof := by
    funext index
    simp [bitInputAssignment, index.isLt]
  simpa only [hfunctions] using hmatches

theorem prefixMatches_recoveredCircuitInput_take
    {count : ℕ} (assignment : ℕ → Bool)
    (prefixLength : ℕ) (hbound : prefixLength ≤ count) :
    PrefixMatches assignment 0
      ((List.ofFn
        (recoveredCircuitInput (n := count) assignment)).take
          prefixLength) := by
  have hmatches :=
    prefixMatches_take_ofFn assignment 0 count prefixLength hbound
  have hfunctions :
      (fun index : Fin count => assignment (0 + index.val)) =
        recoveredCircuitInput assignment := by
    funext index
    simp [recoveredCircuitInput]
  simpa only [hfunctions] using hmatches

private theorem take_eq_or_lex_of_lex
    (count : ℕ) {left right : List Bool}
    (hlt : List.Lex (· < ·) left right) :
    left.take count = right.take count ∨
      List.Lex (· < ·) (left.take count) (right.take count) := by
  induction hlt generalizing count with
  | nil =>
      cases count with
      | zero =>
          exact Or.inl rfl
      | succ count =>
          exact Or.inr List.Lex.nil
  | rel hhead =>
      cases count with
      | zero =>
          exact Or.inl rfl
      | succ count =>
          exact Or.inr (List.Lex.rel hhead)
  | cons htail ih =>
      cases count with
      | zero =>
          exact Or.inl rfl
      | succ count =>
          rcases ih count with hequal | hlex
          · exact Or.inl (congrArg (List.cons _) hequal)
          · exact Or.inr (List.Lex.cons hlex)

theorem take_le_take_of_le
    (count : ℕ) {left right : List Bool}
    (hle : CanonicalBoolListLE left right) :
    CanonicalBoolListLE (left.take count) (right.take count) := by
  unfold CanonicalBoolListLE at hle ⊢
  rcases lt_or_eq_of_le hle with hlt | hequal
  · rcases take_eq_or_lex_of_lex count hlt with hequal | hprefix
    · exact hequal.le
    · exact le_of_lt hprefix
  · subst right
    exact le_refl _

@[simp] theorem outerProofClause_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3 → Literal (pcp.queryCount n)) :
    (outerProofClause pcp input randomness clause).length = 3 := by
  rfl

theorem outerProofLiteral_index_lt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (literal : Literal (pcp.queryCount n)) :
    (outerProofLiteral pcp input randomness literal).2 <
      2 ^ pcp.nativeWidth n := by
  cases literal with
  | positive query =>
      exact (pcp.queryAddress input randomness query).isLt
  | negative query =>
      exact (pcp.queryAddress input randomness query).isLt

theorem outerProofClause_indices_lt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3 → Literal (pcp.queryCount n)) :
    (outerProofClause pcp input randomness clause).all
        (fun literal => literal.2 < 2 ^ pcp.nativeWidth n) = true := by
  rw [List.all_eq_true]
  intro literal hliteral
  simp only [outerProofClause, triple, List.mem_cons,
    List.not_mem_nil, or_false] at hliteral
  rcases hliteral with hzero | hone | htwo
  · subst literal
    exact decide_eq_true
      (outerProofLiteral_index_lt pcp input randomness _)
  · subst literal
    exact decide_eq_true
      (outerProofLiteral_index_lt pcp input randomness _)
  · subst literal
    exact decide_eq_true
      (outerProofLiteral_index_lt pcp input randomness _)

theorem outerProofRowFormula_threeLiteral
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    (outerProofRowFormula pcp input randomness).all
        (fun clause => clause.length = 3) = true := by
  rw [outerProofRowFormula, List.all_map, List.all_eq_true]
  intro clause _hclause
  exact decide_eq_true
    (outerProofClause_length pcp input randomness clause)

theorem outerProofRowFormula_indices_lt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    (outerProofRowFormula pcp input randomness).all
        (fun clause =>
          clause.all (fun literal =>
            literal.2 < 2 ^ pcp.nativeWidth n)) = true := by
  rw [outerProofRowFormula, List.all_map, List.all_eq_true]
  intro clause _hclause
  exact outerProofClause_indices_lt pcp input randomness clause

theorem outerProofRecoveryFormula_threeLiteral
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (outerProofRecoveryFormula pcp input).all
        (fun clause => clause.length = 3) = true := by
  unfold outerProofRecoveryFormula
  rw [List.all_append, Bool.and_eq_true]
  exact
    ⟨circuitInputTautologies_threeLiteral _,
      (listAll_flatMap_iff
        (allBitInputs (pcp.nativeWidth n))
        (outerProofRowFormula pcp input)
        (fun clause => clause.length = 3)).mpr
          (fun randomness _ =>
            outerProofRowFormula_threeLiteral pcp input randomness)⟩

theorem outerProofRecoveryFormula_indices_lt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (outerProofRecoveryFormula pcp input).all
        (fun clause =>
          clause.all (fun literal =>
            literal.2 < 2 ^ pcp.nativeWidth n)) = true := by
  unfold outerProofRecoveryFormula
  rw [List.all_append, Bool.and_eq_true]
  exact
    ⟨circuitInputTautologies_indices_lt (2 ^ pcp.nativeWidth n) 0,
      (listAll_flatMap_iff
        (allBitInputs (pcp.nativeWidth n))
        (outerProofRowFormula pcp input)
        (fun clause =>
          clause.all (fun literal =>
            literal.2 < 2 ^ pcp.nativeWidth n))).mpr
          (fun randomness _ =>
            outerProofRowFormula_indices_lt pcp input randomness)⟩

theorem outerProofVariables_le_formula_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    2 ^ pcp.nativeWidth n ≤
      (outerProofRecoveryFormula pcp input).length := by
  unfold outerProofRecoveryFormula
  rw [List.length_append, circuitInputTautologies_length]
  omega

theorem outerProofRecoveryFormula_wellSized
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    wellSizedCNFEncoding
        (Encodable.encode (outerProofRecoveryFormula pcp input))
        (outerProofRecoveryFormula pcp input) = true := by
  exact wellSizedCNFEncoding_of_variableBound
    (outerProofRecoveryFormula pcp input) (2 ^ pcp.nativeWidth n)
    (outerProofRecoveryFormula_threeLiteral pcp input)
    (outerProofRecoveryFormula_indices_lt pcp input)
    (outerProofVariables_le_formula_length pcp input)

theorem recoveredOuterProofPrefix_eq_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingProof pcp input)
    (count : ℕ) (hcount : count ≤ 2 ^ pcp.nativeWidth n) :
    recoveredPrefix count (outerProofRecoveryFormula pcp input) =
      (List.ofFn canonical.proof).take count := by
  let formula := outerProofRecoveryFormula pcp input
  change
    recoveredPrefix count formula =
      (List.ofFn canonical.proof).take count
  have hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true := by
    exact outerProofRecoveryFormula_wellSized pcp input
  have hrange :
      count ≤ natBitLength (Encodable.encode formula) := by
    exact hcount.trans <|
      (outerProofVariables_le_formula_length pcp input).trans <|
        list_length_le_encoded_bitLength formula
  have hformulaSatisfiable : FormulaSatisfiable formula := by
    exact
      (outerProofRecoveryFormula_satisfiable_iff pcp input).mpr
        ⟨canonical.proof, canonical.accepts⟩
  have hcanonicalPrefixSatisfiable :
      FormulaSatisfiable
        (constrainPrefixChoices 0 formula
          ((List.ofFn canonical.proof).take count)) := by
    refine ⟨bitInputAssignment canonical.proof, ?_⟩
    apply
      (formulaEval_constrainPrefixChoices_iff
        (bitInputAssignment canonical.proof) 0 formula _).mpr
    constructor
    · exact prefixMatches_bitInputAssignment_take canonical.proof
        count hcount
    · apply (outerProofRecoveryFormula_eval_iff pcp input _).mpr
      simpa only [proofAssignment_bitInputAssignment] using
        canonical.accepts
  have hforward :
      CanonicalBoolListLE
        (recoveredPrefix count formula)
        ((List.ofFn canonical.proof).take count) := by
    apply recoveredPrefix_lexLeast count formula hwell hrange
    · simp [hcount]
    · exact hcanonicalPrefixSatisfiable
  rcases
      recoveredPrefix_satisfiable count formula hwell hrange
        hformulaSatisfiable with
    ⟨assignment, hassignment⟩
  have hsemantic :=
    (formulaEval_constrainPrefixChoices_iff assignment 0 formula
      (recoveredPrefix count formula)).mp hassignment
  have haccepts :
      ∀ randomness,
        pcp.accepts input (proofAssignment pcp assignment) randomness =
          true := by
    exact
      (outerProofRecoveryFormula_eval_iff pcp input assignment).mp
        hsemantic.2
  have hminimal :
      CanonicalBoolListLE
        (List.ofFn canonical.proof)
        (List.ofFn (proofAssignment pcp assignment)) :=
    canonical.minimal (proofAssignment pcp assignment) haccepts
  have hback :
      CanonicalBoolListLE
        ((List.ofFn canonical.proof).take count)
        ((List.ofFn (proofAssignment pcp assignment)).take count) :=
    take_le_take_of_le count hminimal
  have hrecovered :
      recoveredPrefix count formula =
        (List.ofFn
          (proofAssignment (n := n) pcp assignment)).take count := by
    have hmatches :=
      prefixMatches_eq_take_ofFn assignment 0
        (recoveredPrefix count formula) (2 ^ pcp.nativeWidth n)
        hsemantic.1 (by
          rw [recoveredPrefix_length]
          exact hcount)
    change
      recoveredPrefix count formula =
        (List.ofFn fun index : Fin (2 ^ pcp.nativeWidth n) =>
          assignment index.val).take count
    simpa only [recoveredPrefix_length, Nat.zero_add] using hmatches
  rw [← hrecovered] at hback
  unfold CanonicalBoolListLE at hforward hback
  exact le_antisymm hforward hback

/-! ## Structural bounded-oracle recovery -/

theorem recoveredBoundedOraclePrefix_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical :
      CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (count : ℕ)
    (hcount :
      count ≤
        descriptionWidth (pcp.nativeWidth n)
          (sizeBound (pcp.nativeWidth n))) :
    recoveredPrefix count
        (boundedOracleRecoveryFormula pcp input
          (sizeBound (pcp.nativeWidth n))) =
      (List.ofFn
        (canonicalDescriptionInput canonical.circuit
          canonical.sizeBounded)).take count := by
  let bound := sizeBound (pcp.nativeWidth n)
  let variableCount :=
    descriptionWidth (pcp.nativeWidth n) bound
  let verifier :=
    boundedOracleVerifierCircuit pcp input bound
  let formula :=
    boundedOracleRecoveryFormula pcp input bound
  let canonicalInput :=
    canonicalDescriptionInput canonical.circuit
      canonical.sizeBounded
  change
    recoveredPrefix count formula =
      (List.ofFn canonicalInput).take count
  have hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true := by
    exact boundedOracleRecoveryFormula_wellSized pcp input bound
  have hvariables : variableCount ≤ formula.length := by
    calc
      variableCount ≤ variableCount + verifier.nodes.length :=
        Nat.le_add_right _ _
      _ ≤ formula.length := by
        simpa only [formula, verifier, variableCount,
          boundedOracleRecoveryFormula] using
          circuitInputVariables_le_formula_length verifier
  have hrange :
      count ≤ natBitLength (Encodable.encode formula) := by
    exact hcount.trans <|
      hvariables.trans <| list_length_le_encoded_bitLength formula
  have hcanonicalAccepts : ∀ randomness,
      acceptsOracleCircuit pcp input canonical.circuit randomness =
        true := by
    intro randomness
    exact canonical.accepts randomness
  rcases boundedOracleRecoveryFormula_complete
      pcp input canonical.circuit canonical.sizeBounded
      hcanonicalAccepts with
    ⟨canonicalAssignment, hcanonicalRecovered,
      hcanonicalFormula⟩
  have hformulaSatisfiable : FormulaSatisfiable formula :=
    ⟨canonicalAssignment, hcanonicalFormula⟩
  have hcanonicalPrefixSatisfiable :
      FormulaSatisfiable
        (constrainPrefixChoices 0 formula
          ((List.ofFn canonicalInput).take count)) := by
    refine ⟨canonicalAssignment, ?_⟩
    apply
      (formulaEval_constrainPrefixChoices_iff
        canonicalAssignment 0 formula _).mpr
    constructor
    · have hprefix :=
        prefixMatches_recoveredCircuitInput_take
          canonicalAssignment count hcount
      rw [hcanonicalRecovered] at hprefix
      exact hprefix
    · exact hcanonicalFormula
  have hforward :
      CanonicalBoolListLE
        (recoveredPrefix count formula)
        ((List.ofFn canonicalInput).take count) := by
    apply recoveredPrefix_lexLeast count formula hwell hrange
    · simp [hcount]
    · exact hcanonicalPrefixSatisfiable
  rcases
      recoveredPrefix_satisfiable count formula hwell hrange
        hformulaSatisfiable with
    ⟨assignment, hassignment⟩
  have hsemantic :=
    (formulaEval_constrainPrefixChoices_iff assignment 0 formula
      (recoveredPrefix count formula)).mp hassignment
  rcases boundedOracleRecoveryFormula_sound
      pcp input assignment hsemantic.2 with
    ⟨candidate, hcandidateSize, hcandidateDescription,
      hcandidateAccepts⟩
  have hminimal :
      CanonicalBoolListLE
        (List.ofFn canonicalInput)
        (List.ofFn
          (canonicalDescriptionInput candidate hcandidateSize)) := by
    simpa only [canonicalInput, bound, CanonicalBoolListLE,
      listOfFn_canonicalDescriptionInput] using
      canonical.minimal candidate hcandidateSize
        (by
          intro randomness
          exact hcandidateAccepts randomness)
  have hback :
      CanonicalBoolListLE
        ((List.ofFn canonicalInput).take count)
        ((List.ofFn
          (canonicalDescriptionInput candidate hcandidateSize)).take
            count) :=
    take_le_take_of_le count hminimal
  have hrecovered :
      recoveredPrefix count formula =
        (List.ofFn
          (canonicalDescriptionInput candidate hcandidateSize)).take
            count := by
    have hmatches :=
      prefixMatches_eq_take_ofFn assignment 0
        (recoveredPrefix count formula) variableCount
        hsemantic.1 (by
          rw [recoveredPrefix_length]
          exact hcount)
    have hmatches' :
        recoveredPrefix count formula =
          (List.ofFn
            (recoveredCircuitInput
              (n := variableCount) assignment)).take count := by
      change
        recoveredPrefix count formula =
          (List.ofFn fun index : Fin variableCount =>
            assignment index.val).take count
      simpa only [recoveredPrefix_length, Nat.zero_add] using hmatches
    rw [hcandidateDescription] at hmatches'
    exact hmatches'
  rw [← hrecovered] at hback
  unfold CanonicalBoolListLE at hforward hback
  exact le_antisymm hforward hback

theorem latestPrefixBitCode_reverse_take_ofFn
    {count : ℕ} (values : Fin count → Bool) (index : Fin count) :
    latestPrefixBitCode
        ((List.ofFn values).take (index.val + 1)).reverse =
      (values index).toNat := by
  have hindex : index.val < (List.ofFn values).length := by
    simpa only [List.length_ofFn] using index.isLt
  rw [List.take_succ_eq_append_getElem hindex, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append,
    latestPrefixBitCode_cons]
  congr 1
  simp only [List.getElem_ofFn]

/-- The Case-2 recovery bit reads the canonical bounded-circuit description
through the same zero-first SAT self-reducer used by the executable kernel. -/
def recoveredBoundedOracleDescriptionBit
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (target :
      Fin (descriptionWidth (pcp.nativeWidth n)
        (sizeBound (pcp.nativeWidth n)))) : Bool :=
  decide
    (prefixSATOutput (target.val + 1)
      (boundedOracleRecoveryFormula pcp input
        (sizeBound (pcp.nativeWidth n))) ≠ 0)

theorem prefixSATOutput_boundedOracle_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical :
      CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (target :
      Fin (descriptionWidth (pcp.nativeWidth n)
        (sizeBound (pcp.nativeWidth n)))) :
    prefixSATOutput (target.val + 1)
        (boundedOracleRecoveryFormula pcp input
          (sizeBound (pcp.nativeWidth n))) =
      (canonicalDescriptionInput canonical.circuit
        canonical.sizeBounded target).toNat := by
  rw [prefixSATOutput_eq_latestPrefixBitCode,
    recoveredBoundedOraclePrefix_eq_canonical
      pcp input canonical (target.val + 1) (by omega)]
  exact latestPrefixBitCode_reverse_take_ofFn
    (canonicalDescriptionInput canonical.circuit
      canonical.sizeBounded) target

theorem recoveredBoundedOracleDescriptionBit_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical :
      CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (target :
      Fin (descriptionWidth (pcp.nativeWidth n)
        (sizeBound (pcp.nativeWidth n)))) :
    recoveredBoundedOracleDescriptionBit
        (sizeBound := sizeBound) pcp input target =
      canonicalDescriptionInput canonical.circuit
        canonical.sizeBounded target := by
  rw [recoveredBoundedOracleDescriptionBit,
    prefixSATOutput_boundedOracle_eq_canonical
      pcp input canonical target]
  cases canonicalDescriptionInput canonical.circuit
    canonical.sizeBounded target <;> rfl

/-- The semantic bit read by the fixed C.12 program.  The requested coordinate
determines the number of zero-first SAT decisions, so no full truth table is
materialized at runtime. -/
def recoveredTargetBit
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (target : Fin (2 ^ pcp.nativeWidth n)) : Bool :=
  decide
    (prefixSATOutput (target.val + 1)
      (outerProofRecoveryFormula pcp input) ≠ 0)

theorem prefixSATOutput_outerProof_eq_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingProof pcp input)
    (target : Fin (2 ^ pcp.nativeWidth n)) :
    prefixSATOutput (target.val + 1)
        (outerProofRecoveryFormula pcp input) =
      (canonical.proof target).toNat := by
  rw [prefixSATOutput_eq_latestPrefixBitCode,
    recoveredOuterProofPrefix_eq_canonical pcp input canonical
      (target.val + 1) (by omega)]
  exact latestPrefixBitCode_reverse_take_ofFn canonical.proof target

theorem recoveredTargetBit_eq_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingProof pcp input)
    (target : Fin (2 ^ pcp.nativeWidth n)) :
    recoveredTargetBit pcp input target = canonical.proof target := by
  rw [recoveredTargetBit,
    prefixSATOutput_outerProof_eq_canonical pcp input canonical target]
  cases canonical.proof target <;> rfl

end NearCubicWires.CanonicalRecoveryLanguage
