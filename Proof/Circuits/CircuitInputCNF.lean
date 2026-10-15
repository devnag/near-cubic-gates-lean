import Proof.Foundations.TseitinCNF

/-!
# Free-input Tseitin CNF

`TseitinCNF.circuitFormula` fixes a circuit input before encoding its gates.
Canonical recovery instead needs SAT to choose that input.  This module owns
the one free-input encoding: variables `0 .. n - 1` are circuit inputs and
variables `n .. n + size - 1` are the topological gate values.

One tautological clause per input makes the formula long enough for the
existing SAT opcode's syntactic index guard.  These clauses carry no semantic
constraint and avoid a second, looser SAT-validation path.
-/

namespace NearCubicWires.CircuitInputCNF

open NearCubicWires
open NearCubicWires.TseitinCNF

abbrev circuitInputGateVariable (inputArity index : ℕ) : ℕ :=
  gateVariable inputArity index

def circuitInputNodeClauses {n : ℕ} (index : ℕ) :
    BooleanNode n → EncodedCNF
  | .const true => [positiveUnit (circuitInputGateVariable n index)]
  | .const false => [negativeUnit (circuitInputGateVariable n index)]
  | .input source =>
      [triple
          (negative (circuitInputGateVariable n index))
          (positive source.val)
          (positive source.val),
        triple
          (positive (circuitInputGateVariable n index))
          (negative source.val)
          (negative source.val)]
  | .not child =>
      [triple
          (negative (circuitInputGateVariable n index))
          (negative (circuitInputGateVariable n child))
          (negative (circuitInputGateVariable n child)),
        triple
          (positive (circuitInputGateVariable n index))
          (positive (circuitInputGateVariable n child))
          (positive (circuitInputGateVariable n child))]
  | .and left right =>
      [triple
          (negative (circuitInputGateVariable n index))
          (positive (circuitInputGateVariable n left))
          (positive (circuitInputGateVariable n left)),
        triple
          (negative (circuitInputGateVariable n index))
          (positive (circuitInputGateVariable n right))
          (positive (circuitInputGateVariable n right)),
        triple
          (positive (circuitInputGateVariable n index))
          (negative (circuitInputGateVariable n left))
          (negative (circuitInputGateVariable n right))]
  | .or left right =>
      [triple
          (positive (circuitInputGateVariable n index))
          (negative (circuitInputGateVariable n left))
          (negative (circuitInputGateVariable n left)),
        triple
          (positive (circuitInputGateVariable n index))
          (negative (circuitInputGateVariable n right))
          (negative (circuitInputGateVariable n right)),
        triple
          (negative (circuitInputGateVariable n index))
          (positive (circuitInputGateVariable n left))
          (positive (circuitInputGateVariable n right))]

def circuitInputNodeValue {n : ℕ} (assignment : ℕ → Bool) :
    BooleanNode n → Bool
  | .const value => value
  | .input source => assignment source.val
  | .not child => !(assignment (circuitInputGateVariable n child))
  | .and left right =>
      assignment (circuitInputGateVariable n left) &&
        assignment (circuitInputGateVariable n right)
  | .or left right =>
      assignment (circuitInputGateVariable n left) ||
        assignment (circuitInputGateVariable n right)

theorem circuitInputNodeClauses_eval_iff {n : ℕ} (index : ℕ)
    (assignment : ℕ → Bool) (node : BooleanNode n) :
    formulaEval assignment (circuitInputNodeClauses index node) = true ↔
      assignment (circuitInputGateVariable n index) =
        circuitInputNodeValue assignment node := by
  cases node with
  | const value =>
      cases value <;>
        cases hgate :
            assignment (circuitInputGateVariable n index) <;>
        simp [circuitInputNodeClauses, circuitInputNodeValue, hgate,
          formulaEval, positiveUnit_eval, negativeUnit_eval]
  | input source =>
      cases hgate :
          assignment (circuitInputGateVariable n index) <;>
        cases hinput : assignment source.val <;>
        simp [circuitInputNodeClauses, circuitInputNodeValue,
          formulaEval, clauseEval, triple, hgate, hinput]
  | not child =>
      cases hgate :
          assignment (circuitInputGateVariable n index) <;>
        cases hchild :
          assignment (circuitInputGateVariable n child) <;>
        simp [circuitInputNodeClauses, circuitInputNodeValue,
          formulaEval, clauseEval, triple, hgate, hchild]
  | and left right =>
      cases hgate :
          assignment (circuitInputGateVariable n index) <;>
        cases hleft :
          assignment (circuitInputGateVariable n left) <;>
        cases hright :
          assignment (circuitInputGateVariable n right) <;>
        simp [circuitInputNodeClauses, circuitInputNodeValue,
          formulaEval, clauseEval, triple, hgate, hleft,
          hright]
  | or left right =>
      cases hgate :
          assignment (circuitInputGateVariable n index) <;>
        cases hleft :
          assignment (circuitInputGateVariable n left) <;>
        cases hright :
          assignment (circuitInputGateVariable n right) <;>
        simp [circuitInputNodeClauses, circuitInputNodeValue,
          formulaEval, clauseEval, triple, hgate, hleft,
          hright]

def circuitInputTautology (index : ℕ) : EncodedClause :=
  triple (positive index) (negative index) (positive index)

def circuitInputTautologies : ℕ → EncodedCNF
  | 0 => []
  | count + 1 =>
      circuitInputTautologies count ++ [circuitInputTautology count]

@[simp] theorem circuitInputTautologies_length (count : ℕ) :
    (circuitInputTautologies count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [circuitInputTautologies, ih]

theorem circuitInputTautologies_eval (count : ℕ)
    (assignment : ℕ → Bool) :
    formulaEval assignment (circuitInputTautologies count) = true := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      rw [circuitInputTautologies, formulaEval_append, ih]
      cases hvalue : assignment count <;>
        simp [circuitInputTautology, formulaEval, clauseEval,
          triple, hvalue]

def circuitInputNodesClausesFrom {n : ℕ} (start : ℕ) :
    List (BooleanNode n) → EncodedCNF
  | [] => []
  | node :: rest =>
      circuitInputNodeClauses start node ++
        circuitInputNodesClausesFrom (start + 1) rest

def circuitInputFormula {n : ℕ}
    (circuit : BooleanCircuit n) : EncodedCNF :=
  circuitInputTautologies n ++
    (circuitInputNodesClausesFrom 0 circuit.nodes ++
      [positiveUnit
        (circuitInputGateVariable n circuit.output.val)])

def recoveredCircuitInput {n : ℕ}
    (assignment : ℕ → Bool) : BitInput n :=
  fun index => assignment index.val

@[simp] theorem circuitInputNodeValue_eq_nodeValue {n : ℕ}
    (assignment : ℕ → Bool) (node : BooleanNode n) :
    circuitInputNodeValue assignment node =
      nodeValue n (recoveredCircuitInput assignment) assignment node := by
  cases node <;> rfl

theorem circuitInputNodesClausesFrom_eval_iff {n : ℕ}
    (start : ℕ) (assignment : ℕ → Bool)
    (nodes : List (BooleanNode n)) :
    formulaEval assignment
        (circuitInputNodesClausesFrom start nodes) = true ↔
      NodesModelFrom n start (recoveredCircuitInput assignment)
        assignment nodes := by
  induction nodes generalizing start with
  | nil =>
      simp [circuitInputNodesClausesFrom, formulaEval, NodesModelFrom]
  | cons node rest ih =>
      rw [circuitInputNodesClausesFrom, formulaEval_append,
        circuitInputNodeClauses_eval_iff, ih]
      simp only [NodesModelFrom, circuitInputNodeValue_eq_nodeValue]

theorem circuitInputFormula_eval_iff {n : ℕ}
    (circuit : BooleanCircuit n) (assignment : ℕ → Bool) :
    formulaEval assignment (circuitInputFormula circuit) = true ↔
      NodesModelFrom n 0 (recoveredCircuitInput assignment)
          assignment circuit.nodes ∧
        assignment
          (circuitInputGateVariable n circuit.output.val) = true := by
  unfold circuitInputFormula
  rw [formulaEval_append]
  have hrest :
      formulaEval assignment
          (circuitInputNodesClausesFrom 0 circuit.nodes ++
            [positiveUnit
              (circuitInputGateVariable n circuit.output.val)]) = true ↔
        NodesModelFrom n 0 (recoveredCircuitInput assignment)
            assignment circuit.nodes ∧
          assignment
            (circuitInputGateVariable n circuit.output.val) = true := by
    rw [formulaEval_append, circuitInputNodesClausesFrom_eval_iff]
    simp [formulaEval]
  rw [hrest]
  constructor
  · exact And.right
  · intro hparts
    exact ⟨circuitInputTautologies_eval n assignment, hparts⟩

private def AgreesOnCircuitGates (n : ℕ)
    (left right : ℕ → Bool) : Prop :=
  ∀ index, left (circuitInputGateVariable n index) =
    right (circuitInputGateVariable n index)

private theorem nodeValue_eq_of_gate_agreement {n : ℕ}
    {left right : ℕ → Bool}
    (hagree : AgreesOnCircuitGates n left right)
    (input : BitInput n) (node : BooleanNode n) :
    nodeValue n input left node = nodeValue n input right node := by
  cases node with
  | const value =>
      rfl
  | input source =>
      rfl
  | not child =>
      have hchild := hagree child
      simpa only [nodeValue, gateVariable] using congrArg Bool.not hchild
  | and childLeft childRight =>
      have hleft := hagree childLeft
      have hright := hagree childRight
      simpa only [nodeValue, gateVariable] using
        congrArg₂ (· && ·) hleft hright
  | or childLeft childRight =>
      have hleft := hagree childLeft
      have hright := hagree childRight
      simpa only [nodeValue, gateVariable] using
        congrArg₂ (· || ·) hleft hright

private theorem nodesModelFrom_congr_gate_assignment {n start : ℕ}
    {left right : ℕ → Bool}
    (hagree : AgreesOnCircuitGates n left right)
    (input : BitInput n) (nodes : List (BooleanNode n)) :
    NodesModelFrom n start input left nodes ↔
      NodesModelFrom n start input right nodes := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      simp only [NodesModelFrom]
      have hhead := hagree start
      have hvalue :=
        nodeValue_eq_of_gate_agreement hagree input node
      constructor
      · rintro ⟨heq, hrest⟩
        refine ⟨?_, (ih (start := start + 1)).mp hrest⟩
        exact hhead.symm.trans (heq.trans hvalue)
      · rintro ⟨heq, hrest⟩
        refine ⟨?_, (ih (start := start + 1)).mpr hrest⟩
        exact hhead.trans (heq.trans hvalue.symm)

theorem circuitInputFormula_sound {n : ℕ}
    (circuit : BooleanCircuit n) (assignment : ℕ → Bool)
    (hsatisfies :
      formulaEval assignment (circuitInputFormula circuit) = true) :
    circuit.eval (recoveredCircuitInput assignment) = true := by
  let input : BitInput n := recoveredCircuitInput assignment
  have hparts :=
    (circuitInputFormula_eval_iff circuit assignment).mp hsatisfies
  have hfixed :
      formulaEval assignment (circuitFormula n input circuit) = true := by
    apply (circuitFormula_eval_iff n input circuit assignment).mpr
    simpa [input, circuitInputGateVariable, gateVariable] using hparts
  exact
    (circuitFormula_satisfiable_iff_eval n input circuit).mp
      ⟨assignment, hfixed⟩

theorem circuitInputFormula_complete {n : ℕ}
    (circuit : BooleanCircuit n) (input : BitInput n)
    (haccepts : circuit.eval input = true) :
    ∃ assignment : ℕ → Bool,
      recoveredCircuitInput assignment = input ∧
        formulaEval assignment (circuitInputFormula circuit) = true := by
  rcases
      (circuitFormula_satisfiable_iff_eval n input circuit).mpr
        haccepts with
    ⟨gateAssignment, hgateFormula⟩
  let assignment : ℕ → Bool := fun address =>
    if hinput : address < n then input ⟨address, hinput⟩
    else gateAssignment address
  have hagree :
      AgreesOnCircuitGates n assignment gateAssignment := by
    intro index
    simp only [assignment]
    split
    · rename_i himpossible
      simp only [gateVariable] at himpossible
      omega
    · rfl
  have hrecovered :
      recoveredCircuitInput assignment = input := by
    funext index
    simp [recoveredCircuitInput, assignment, index.isLt]
  have hfixedParts :=
    (circuitFormula_eval_iff n input circuit gateAssignment).mp
      hgateFormula
  have hmodel :
      NodesModelFrom n 0 input assignment circuit.nodes :=
    (nodesModelFrom_congr_gate_assignment hagree input circuit.nodes).mpr
      hfixedParts.1
  have houtput :
      assignment
          (circuitInputGateVariable n circuit.output.val) = true := by
    rw [hagree circuit.output.val]
    simpa [circuitInputGateVariable, gateVariable] using hfixedParts.2
  refine ⟨assignment, hrecovered, ?_⟩
  apply (circuitInputFormula_eval_iff circuit assignment).mpr
  rw [hrecovered]
  exact ⟨hmodel, houtput⟩

theorem circuitInputFormula_satisfiable_iff {n : ℕ}
    (circuit : BooleanCircuit n) :
    (∃ assignment : ℕ → Bool,
      formulaEval assignment (circuitInputFormula circuit) = true) ↔
        ∃ input : BitInput n, circuit.eval input = true := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    exact
      ⟨recoveredCircuitInput assignment,
        circuitInputFormula_sound circuit assignment hsatisfies⟩
  · rintro ⟨input, haccepts⟩
    rcases circuitInputFormula_complete circuit input haccepts with
      ⟨assignment, _hrecovered, hsatisfies⟩
    exact ⟨assignment, hsatisfies⟩

/-! ## Canonical SAT guard -/

theorem circuitInputTautologies_threeLiteral (count : ℕ) :
    (circuitInputTautologies count).all
      (fun clause => clause.length = 3) = true := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp [circuitInputTautologies, circuitInputTautology, triple, ih]

theorem circuitInputNodeClauses_threeLiteral {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    (circuitInputNodeClauses index node).all
      (fun clause => clause.length = 3) = true := by
  cases node with
  | const value =>
      cases value <;>
        simp [circuitInputNodeClauses, positiveUnit, negativeUnit, triple]
  | input source =>
      simp [circuitInputNodeClauses, triple]
  | not child =>
      simp [circuitInputNodeClauses, triple]
  | and left right =>
      simp [circuitInputNodeClauses, triple]
  | or left right =>
      simp [circuitInputNodeClauses, triple]

theorem circuitInputNodesClausesFrom_threeLiteral {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputNodesClausesFrom start nodes).all
      (fun clause => clause.length = 3) = true := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      simp only [circuitInputNodesClausesFrom, List.all_append,
        Bool.and_eq_true]
      exact
        ⟨circuitInputNodeClauses_threeLiteral start node,
          ih (start + 1)⟩

theorem circuitInputFormula_threeLiteral {n : ℕ}
    (circuit : BooleanCircuit n) :
    (circuitInputFormula circuit).all
      (fun clause => clause.length = 3) = true := by
  simp [circuitInputFormula, circuitInputTautologies_threeLiteral,
    circuitInputNodesClausesFrom_threeLiteral, positiveUnit, triple]

theorem circuitInputTautologies_indices_lt
    (count nodeCount : ℕ) :
    (circuitInputTautologies count).all
      (fun clause =>
        clause.all (fun literal => literal.2 < count + nodeCount)) =
          true := by
  induction count generalizing nodeCount with
  | zero =>
      rfl
  | succ count ih =>
      rw [circuitInputTautologies, List.all_append, Bool.and_eq_true]
      constructor
      · have hmono :
          ∀ clause ∈ circuitInputTautologies count,
            clause.all
              (fun literal => literal.2 < count + 1 + nodeCount) = true := by
            intro clause hclause
            have hold :=
              (List.all_eq_true.mp (ih nodeCount)) clause hclause
            rw [List.all_eq_true] at hold ⊢
            intro literal hliteral
            have := of_decide_eq_true (hold literal hliteral)
            exact decide_eq_true (by omega)
        exact List.all_eq_true.mpr hmono
      · simp [circuitInputTautology, triple, positive, negative]
        omega

private theorem circuitInputNodeClauses_indices_lt {n : ℕ}
    {index nodeCount : ℕ} (node : BooleanNode n)
    (hindex : index < nodeCount)
    (hwell : node.WellFormedAt index) :
    (circuitInputNodeClauses index node).all
      (fun clause =>
        clause.all (fun literal => literal.2 < n + nodeCount)) = true := by
  cases node with
  | const value =>
      cases value <;>
        simp [circuitInputNodeClauses, positiveUnit, negativeUnit, triple,
          positive, negative, gateVariable] <;>
        omega
  | input source =>
      have hsource : source.val < n := source.isLt
      simp [circuitInputNodeClauses, triple, positive, negative,
        gateVariable]
      omega
  | not child =>
      have hchild : child < nodeCount := hwell.trans hindex
      simp [circuitInputNodeClauses, triple, positive, negative,
        gateVariable]
      omega
  | and left right =>
      have hleft : left < nodeCount := hwell.1.trans hindex
      have hright : right < nodeCount := hwell.2.trans hindex
      simp [circuitInputNodeClauses, triple, positive, negative,
        gateVariable]
      omega
  | or left right =>
      have hleft : left < nodeCount := hwell.1.trans hindex
      have hright : right < nodeCount := hwell.2.trans hindex
      simp [circuitInputNodeClauses, triple, positive, negative,
        gateVariable]
      omega

private theorem circuitInputNodesClausesFrom_indices_lt {n : ℕ}
    (start nodeCount : ℕ) (nodes : List (BooleanNode n))
    (hindex :
      ∀ offset : Fin nodes.length, start + offset.val < nodeCount)
    (hwell :
      ∀ offset : Fin nodes.length,
        (nodes.get offset).WellFormedAt (start + offset.val)) :
    (circuitInputNodesClausesFrom start nodes).all
      (fun clause =>
        clause.all (fun literal => literal.2 < n + nodeCount)) = true := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      have hheadIndex : start < nodeCount := by
        simpa using hindex ⟨0, by simp⟩
      have hheadWell : node.WellFormedAt start := by
        simpa using hwell ⟨0, by simp⟩
      have htailIndex :
          ∀ offset : Fin rest.length,
            start + 1 + offset.val < nodeCount := by
        intro offset
        have hnext := hindex ⟨offset.val + 1, by simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      have htailWell :
          ∀ offset : Fin rest.length,
            (rest.get offset).WellFormedAt
              (start + 1 + offset.val) := by
        intro offset
        have hnext := hwell ⟨offset.val + 1, by simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      simp only [circuitInputNodesClausesFrom, List.all_append,
        Bool.and_eq_true]
      exact
        ⟨circuitInputNodeClauses_indices_lt node hheadIndex hheadWell,
          ih (start + 1) htailIndex htailWell⟩

theorem circuitInputFormula_indices_lt {n : ℕ}
    (circuit : BooleanCircuit n) :
    (circuitInputFormula circuit).all
      (fun clause =>
        clause.all (fun literal =>
          literal.2 < n + circuit.nodes.length)) = true := by
  unfold circuitInputFormula
  rw [List.all_append, Bool.and_eq_true]
  constructor
  · exact circuitInputTautologies_indices_lt n circuit.nodes.length
  · rw [List.all_append, Bool.and_eq_true]
    constructor
    · apply circuitInputNodesClausesFrom_indices_lt
      · intro offset
        simpa only [Nat.zero_add] using offset.isLt
      · intro offset
        simpa using circuit.wellFormed offset
    · simp [positiveUnit, triple, positive, gateVariable,
        circuit.output.isLt]

private theorem circuitInputNodeClauses_length_positive {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    1 ≤ (circuitInputNodeClauses index node).length := by
  cases node with
  | const value =>
      cases value <;> simp [circuitInputNodeClauses]
  | input source =>
      simp [circuitInputNodeClauses]
  | not child =>
      simp [circuitInputNodeClauses]
  | and left right =>
      simp [circuitInputNodeClauses]
  | or left right =>
      simp [circuitInputNodeClauses]

private theorem circuitInputNodes_length_le_clauses_length {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    nodes.length ≤ (circuitInputNodesClausesFrom start nodes).length := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      simp only [List.length_cons, circuitInputNodesClausesFrom,
        List.length_append]
      have hnode := circuitInputNodeClauses_length_positive start node
      have hrest := ih (start + 1)
      omega

theorem circuitInputVariables_le_formula_length {n : ℕ}
    (circuit : BooleanCircuit n) :
    n + circuit.nodes.length ≤
      (circuitInputFormula circuit).length := by
  unfold circuitInputFormula
  simp only [List.length_append, circuitInputTautologies_length,
    List.length_singleton]
  have hnodes :=
    circuitInputNodes_length_le_clauses_length 0 circuit.nodes
  omega

/-- Shared bridge from a syntactic three-CNF variable bound to the SAT
interpreter's code-relative guard.  Formula builders need only account for
their genuine variable range and ensure at least one clause per variable. -/
theorem wellSizedCNFEncoding_of_variableBound
    (formula : EncodedCNF) (variableBound : ℕ)
    (hthree :
      formula.all (fun clause => clause.length = 3) = true)
    (hindices :
      formula.all (fun clause =>
        clause.all (fun literal => literal.2 < variableBound)) = true)
    (hvariables : variableBound ≤ formula.length) :
    wellSizedCNFEncoding (Encodable.encode formula) formula = true := by
  rw [wellSizedCNFEncoding, Bool.and_eq_true]
  constructor
  · exact decide_eq_true (list_length_le_encoded_bitLength formula)
  · rw [List.all_eq_true]
    intro clause hclause
    rw [Bool.and_eq_true]
    constructor
    · exact (List.all_eq_true.mp hthree) clause hclause
    · rw [List.all_eq_true]
      intro literal hliteral
      have hbounded :=
        (List.all_eq_true.mp
          ((List.all_eq_true.mp hindices) clause hclause))
          literal hliteral
      exact decide_eq_true <|
        (of_decide_eq_true hbounded).trans_le <|
          hvariables.trans (list_length_le_encoded_bitLength formula)

theorem circuitInputFormula_wellSized {n : ℕ}
    (circuit : BooleanCircuit n) :
    wellSizedCNFEncoding
      (Encodable.encode (circuitInputFormula circuit))
      (circuitInputFormula circuit) = true := by
  exact wellSizedCNFEncoding_of_variableBound
    (circuitInputFormula circuit) (n + circuit.nodes.length)
    (circuitInputFormula_threeLiteral circuit)
    (circuitInputFormula_indices_lt circuit)
    (circuitInputVariables_le_formula_length circuit)

theorem encodedSat_circuitInputFormula_eq_true_iff {n : ℕ}
    (circuit : BooleanCircuit n) :
    encodedSat (Encodable.encode (circuitInputFormula circuit)) = true ↔
      ∃ input : BitInput n, circuit.eval input = true := by
  rw [encodedSat_encode_eq_true_iff
    (circuitInputFormula circuit) (circuitInputFormula_wellSized circuit)]
  exact circuitInputFormula_satisfiable_iff circuit

end NearCubicWires.CircuitInputCNF
