import Proof.Foundations.DynamicCNFBuilder
import StatementSupport

/-!
# Canonical Tseitin CNF for Boolean DAGs

This module gives the SAT oracle a concrete formula rather than a semantic
formula-builder callback.  Every clause has exactly three literals (unit and
binary clauses are padded by repetition), gate variables retain the circuit's
topological node addresses, and the distinguished output variable is asserted.
-/

namespace NearCubicWires.TseitinCNF

open NearCubicWires

def positive (varIndex : ℕ) : EncodedLiteral := (true, varIndex)
def negative (varIndex : ℕ) : EncodedLiteral := (false, varIndex)

def triple (first second third : EncodedLiteral) : EncodedClause :=
  [first, second, third]

def positiveUnit (varIndex : ℕ) : EncodedClause :=
  triple (positive varIndex) (positive varIndex) (positive varIndex)

def negativeUnit (varIndex : ℕ) : EncodedClause :=
  triple (negative varIndex) (negative varIndex) (negative varIndex)

@[simp] theorem positive_eval (assignment : ℕ → Bool) (varIndex : ℕ) :
    literalEval assignment (positive varIndex) = assignment varIndex := by
  rfl

@[simp] theorem negative_eval (assignment : ℕ → Bool) (varIndex : ℕ) :
    literalEval assignment (negative varIndex) = !(assignment varIndex) := by
  rfl

@[simp] theorem positiveUnit_eval (assignment : ℕ → Bool) (varIndex : ℕ) :
    clauseEval assignment (positiveUnit varIndex) = assignment varIndex := by
  cases hvalue : assignment varIndex <;>
    simp [positiveUnit, triple, clauseEval, literalEval, positive, hvalue]

@[simp] theorem negativeUnit_eval (assignment : ℕ → Bool) (varIndex : ℕ) :
    clauseEval assignment (negativeUnit varIndex) = !(assignment varIndex) := by
  cases hvalue : assignment varIndex <;>
    simp [negativeUnit, triple, clauseEval, literalEval, negative, hvalue]

/-- Gate-variable addresses are shifted by `base`; child addresses remain
relative to the beginning of the same topological node block. -/
def gateVariable (base index : ℕ) : ℕ :=
  base + index

def nodeClauses {n : ℕ} (base index : ℕ) (input : BitInput n) :
    BooleanNode n → EncodedCNF
  | .const true => [positiveUnit (gateVariable base index)]
  | .const false => [negativeUnit (gateVariable base index)]
  | .input source =>
      if input source then
        [positiveUnit (gateVariable base index)]
      else
        [negativeUnit (gateVariable base index)]
  | .not child =>
      [triple
          (negative (gateVariable base index))
          (negative (gateVariable base child))
          (negative (gateVariable base child)),
        triple
          (positive (gateVariable base index))
          (positive (gateVariable base child))
          (positive (gateVariable base child))]
  | .and left right =>
      [triple
          (negative (gateVariable base index))
          (positive (gateVariable base left))
          (positive (gateVariable base left)),
        triple
          (negative (gateVariable base index))
          (positive (gateVariable base right))
          (positive (gateVariable base right)),
        triple
          (positive (gateVariable base index))
          (negative (gateVariable base left))
          (negative (gateVariable base right))]
  | .or left right =>
      [triple
          (positive (gateVariable base index))
          (negative (gateVariable base left))
          (negative (gateVariable base left)),
        triple
          (positive (gateVariable base index))
          (negative (gateVariable base right))
          (negative (gateVariable base right)),
        triple
          (negative (gateVariable base index))
          (positive (gateVariable base left))
          (positive (gateVariable base right))]

def nodeValue {n : ℕ} (base : ℕ) (input : BitInput n)
    (assignment : ℕ → Bool) : BooleanNode n → Bool
  | .const value => value
  | .input source => input source
  | .not child => !(assignment (gateVariable base child))
  | .and left right =>
      assignment (gateVariable base left) &&
        assignment (gateVariable base right)
  | .or left right =>
      assignment (gateVariable base left) ||
        assignment (gateVariable base right)

/-- The three-literal templates are exactly the bi-implication for one gate. -/
theorem nodeClauses_eval_iff {n : ℕ} (base index : ℕ)
    (input : BitInput n) (assignment : ℕ → Bool) (node : BooleanNode n) :
    formulaEval assignment (nodeClauses base index input node) = true ↔
      assignment (gateVariable base index) =
        nodeValue base input assignment node := by
  cases node with
  | const value =>
      cases value <;>
        cases hgate : assignment (gateVariable base index) <;>
        simp [nodeClauses, formulaEval, nodeValue, hgate,
          positiveUnit_eval, negativeUnit_eval]
  | input source =>
      cases hinput : input source <;>
        cases hgate : assignment (gateVariable base index) <;>
        simp [nodeClauses, formulaEval, nodeValue, hinput, hgate,
          positiveUnit_eval, negativeUnit_eval]
  | not child =>
      cases hgate : assignment (gateVariable base index) <;>
        cases hchild : assignment (gateVariable base child) <;>
        simp [nodeClauses, formulaEval, clauseEval, nodeValue, triple,
          hgate, hchild]
  | and left right =>
      cases hgate : assignment (gateVariable base index) <;>
        cases hleft : assignment (gateVariable base left) <;>
        cases hright : assignment (gateVariable base right) <;>
        simp [nodeClauses, formulaEval, clauseEval, nodeValue, triple,
          hgate, hleft, hright]
  | or left right =>
      cases hgate : assignment (gateVariable base index) <;>
        cases hleft : assignment (gateVariable base left) <;>
        cases hright : assignment (gateVariable base right) <;>
        simp [nodeClauses, formulaEval, clauseEval, nodeValue, triple,
          hgate, hleft, hright]

def nodesClausesFrom {n : ℕ} (base start : ℕ) (input : BitInput n) :
    List (BooleanNode n) → EncodedCNF
  | [] => []
  | node :: rest =>
      nodeClauses base start input node ++
        nodesClausesFrom base (start + 1) input rest

def circuitFormula {n : ℕ} (base : ℕ) (input : BitInput n)
    (circuit : BooleanCircuit n) : EncodedCNF :=
  nodesClausesFrom base 0 input circuit.nodes ++
    [positiveUnit (gateVariable base circuit.output.val)]

theorem nodeClauses_threeLiteral {n : ℕ} (base index : ℕ)
    (input : BitInput n) (node : BooleanNode n) :
    (nodeClauses base index input node).all
      (fun clause => clause.length = 3) = true := by
  cases node with
  | const value =>
      cases value <;>
        simp [nodeClauses, positiveUnit, negativeUnit, triple]
  | input source =>
      cases hinput : input source <;>
        simp [nodeClauses, positiveUnit, negativeUnit, triple, hinput]
  | not child =>
      simp [nodeClauses, triple]
  | and left right =>
      simp [nodeClauses, triple]
  | or left right =>
      simp [nodeClauses, triple]

theorem nodesClausesFrom_threeLiteral {n : ℕ} (base start : ℕ)
    (input : BitInput n) (nodes : List (BooleanNode n)) :
    (nodesClausesFrom base start input nodes).all
      (fun clause => clause.length = 3) = true := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest ih =>
      simp only [nodesClausesFrom, List.all_append, Bool.and_eq_true]
      exact ⟨nodeClauses_threeLiteral base start input node,
        ih (start + 1)⟩

theorem circuitFormula_threeLiteral {n : ℕ} (base : ℕ)
    (input : BitInput n) (circuit : BooleanCircuit n) :
    (circuitFormula base input circuit).all
      (fun clause => clause.length = 3) = true := by
  simp [circuitFormula, nodesClausesFrom_threeLiteral, positiveUnit, triple]

/-! ## Formula semantics -/

def NodesModelFrom {n : ℕ} (base start : ℕ) (input : BitInput n)
    (assignment : ℕ → Bool) : List (BooleanNode n) → Prop
  | [] => True
  | node :: rest =>
      assignment (gateVariable base start) =
          nodeValue base input assignment node ∧
        NodesModelFrom base (start + 1) input assignment rest

theorem formulaEval_append (assignment : ℕ → Bool)
    (first second : EncodedCNF) :
    formulaEval assignment (first ++ second) = true ↔
      formulaEval assignment first = true ∧
        formulaEval assignment second = true := by
  simp [formulaEval, List.all_append]

theorem nodesClausesFrom_eval_iff {n : ℕ} (base start : ℕ)
    (input : BitInput n) (assignment : ℕ → Bool)
    (nodes : List (BooleanNode n)) :
    formulaEval assignment (nodesClausesFrom base start input nodes) = true ↔
      NodesModelFrom base start input assignment nodes := by
  induction nodes generalizing start with
  | nil =>
      simp [nodesClausesFrom, formulaEval, NodesModelFrom]
  | cons node rest ih =>
      rw [nodesClausesFrom, formulaEval_append,
        nodeClauses_eval_iff, ih]
      rfl

theorem circuitFormula_eval_iff {n : ℕ} (base : ℕ)
    (input : BitInput n) (circuit : BooleanCircuit n)
    (assignment : ℕ → Bool) :
    formulaEval assignment (circuitFormula base input circuit) = true ↔
      NodesModelFrom base 0 input assignment circuit.nodes ∧
        assignment (gateVariable base circuit.output.val) = true := by
  rw [circuitFormula, formulaEval_append, nodesClausesFrom_eval_iff]
  simp [formulaEval]

/-! ## Agreement with the repository's array-fold circuit semantics -/

def PriorAgrees (base : ℕ) (assignment : ℕ → Bool)
    (prior : Array Bool) : Prop :=
  ∀ index (_hindex : index < prior.size),
    prior[index]? = some (assignment (gateVariable base index))

private theorem foldNodes_preserves {n : ℕ} (input : BitInput n)
    (nodes : List (BooleanNode n)) (prior : Array Bool)
    (index : ℕ) (hindex : index < prior.size) :
    (nodes.foldl
        (fun values node => values.push (node.eval input values))
        prior)[index]? =
      prior[index]? := by
  induction nodes generalizing prior with
  | nil => rfl
  | cons node rest ih =>
      rw [List.foldl_cons, ih (prior.push (node.eval input prior))
        (by simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem (by
        simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem hindex]
      exact congrArg some (Array.getElem_push_lt hindex)

private theorem foldNodes_size {n : ℕ} (input : BitInput n)
    (nodes : List (BooleanNode n)) (prior : Array Bool) :
    (nodes.foldl
        (fun values node => values.push (node.eval input values))
        prior).size =
      prior.size + nodes.length := by
  induction nodes generalizing prior with
  | nil =>
      simp
  | cons node rest ih =>
      rw [List.foldl_cons, ih]
      simp
      omega

private theorem node_eval_eq_nodeValue {n : ℕ} {base : ℕ}
    {input : BitInput n} {assignment : ℕ → Bool}
    {prior : Array Bool} {node : BooleanNode n}
    (hwell : node.WellFormedAt prior.size)
    (hagrees : PriorAgrees base assignment prior) :
    node.eval input prior = nodeValue base input assignment node := by
  cases node with
  | const value =>
      rfl
  | input source =>
      rfl
  | not child =>
      simp only [BooleanNode.eval, nodeValue]
      rw [hagrees child hwell]
      rfl
  | and left right =>
      simp only [BooleanNode.eval, nodeValue]
      rw [hagrees left hwell.1, hagrees right hwell.2]
      rfl
  | or left right =>
      simp only [BooleanNode.eval, nodeValue]
      rw [hagrees left hwell.1, hagrees right hwell.2]
      rfl

private theorem priorAgrees_push {n : ℕ} {base start : ℕ}
    {input : BitInput n} {assignment : ℕ → Bool}
    {prior : Array Bool} {node : BooleanNode n}
    (hstart : prior.size = start)
    (hwell : node.WellFormedAt start)
    (hagrees : PriorAgrees base assignment prior)
    (hmodel :
      assignment (gateVariable base start) =
        nodeValue base input assignment node) :
    PriorAgrees base assignment
      (prior.push (node.eval input prior)) := by
  have hnode :
      node.eval input prior = nodeValue base input assignment node :=
    node_eval_eq_nodeValue (by simpa [hstart] using hwell) hagrees
  intro index hindex
  by_cases hold : index < prior.size
  · have hprior := hagrees index hold
    rw [Array.getElem?_eq_getElem hold] at hprior
    rw [Array.getElem?_eq_getElem (by
      simpa using Nat.lt_succ_of_lt hold)]
    rw [Array.getElem_push_lt hold]
    exact hprior
  · have hnew : index = prior.size := by
      simp only [Array.size_push] at hindex
      omega
    subst index
    rw [Array.getElem?_eq_getElem (by simp)]
    rw [Array.getElem_push_eq]
    simp only [hnode, hstart]
    exact congrArg some hmodel.symm

private theorem foldNodes_agrees {n : ℕ} (base start : ℕ)
    (input : BitInput n) (assignment : ℕ → Bool)
    (nodes : List (BooleanNode n)) (prior : Array Bool)
    (hstart : prior.size = start)
    (hwell :
      ∀ offset : Fin nodes.length,
        (nodes.get offset).WellFormedAt (start + offset.val))
    (hmodel : NodesModelFrom base start input assignment nodes)
    (hagrees : PriorAgrees base assignment prior) :
    PriorAgrees base assignment
      (nodes.foldl
        (fun values node => values.push (node.eval input values))
        prior) := by
  induction nodes generalizing start prior with
  | nil =>
      exact hagrees
  | cons node rest ih =>
      have hhead : node.WellFormedAt start := by
        simpa using hwell ⟨0, by simp⟩
      have htail :
          ∀ offset : Fin rest.length,
            (rest.get offset).WellFormedAt (start + 1 + offset.val) := by
        intro offset
        have hnext := hwell
          ⟨offset.val + 1, by
            simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      have hnextAgrees :
          PriorAgrees base assignment
            (prior.push (node.eval input prior)) :=
        priorAgrees_push hstart hhead hagrees hmodel.1
      rw [List.foldl_cons]
      exact ih (start + 1) (prior.push (node.eval input prior))
        (by simp [hstart]) htail hmodel.2 hnextAgrees

def arrayAssignment (base : ℕ) (values : Array Bool) : ℕ → Bool :=
  fun varIndex => values[varIndex - base]?.getD false

@[simp] theorem arrayAssignment_gateVariable (base index : ℕ)
    (values : Array Bool) :
    arrayAssignment base values (gateVariable base index) =
      values[index]?.getD false := by
  simp [arrayAssignment, gateVariable]

private theorem canonicalModelFrom {n : ℕ} (base start : ℕ)
    (input : BitInput n) (nodes : List (BooleanNode n))
    (prior : Array Bool)
    (hstart : prior.size = start)
    (hwell :
      ∀ offset : Fin nodes.length,
        (nodes.get offset).WellFormedAt (start + offset.val)) :
    let final :=
      nodes.foldl
        (fun values node => values.push (node.eval input values))
        prior
    NodesModelFrom base start input (arrayAssignment base final) nodes := by
  induction nodes generalizing start prior with
  | nil =>
      trivial
  | cons node rest ih =>
      let nextPrior := prior.push (node.eval input prior)
      let final :=
        rest.foldl
          (fun values nextNode =>
            values.push (nextNode.eval input values))
          nextPrior
      have hhead : node.WellFormedAt start := by
        simpa using hwell ⟨0, by simp⟩
      have htail :
          ∀ offset : Fin rest.length,
            (rest.get offset).WellFormedAt (start + 1 + offset.val) := by
        intro offset
        have hnext := hwell
          ⟨offset.val + 1, by
            simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      have hpriorValue :
          ∀ child < prior.size,
            final[child]? = prior[child]? := by
        intro child hchild
        exact foldNodes_preserves input rest nextPrior child
          (by simpa [nextPrior] using Nat.lt_succ_of_lt hchild) |>.trans <| by
            rw [Array.getElem?_eq_getElem (by
              simpa [nextPrior] using Nat.lt_succ_of_lt hchild)]
            rw [Array.getElem?_eq_getElem hchild]
            exact congrArg some (Array.getElem_push_lt hchild)
      have hnodeValue :
          nodeValue base input (arrayAssignment base final) node =
            node.eval input prior := by
        cases node with
        | const value =>
            rfl
        | input source =>
            rfl
        | not child =>
            simp only [nodeValue, BooleanNode.eval,
              arrayAssignment_gateVariable]
            rw [hpriorValue child (by
              simpa [BooleanNode.WellFormedAt, hstart] using hhead)]
        | and left right =>
            simp only [nodeValue, BooleanNode.eval,
              arrayAssignment_gateVariable]
            rw [hpriorValue left (by simpa [hstart] using hhead.1),
              hpriorValue right (by simpa [hstart] using hhead.2)]
        | or left right =>
            simp only [nodeValue, BooleanNode.eval,
              arrayAssignment_gateVariable]
            rw [hpriorValue left (by simpa [hstart] using hhead.1),
              hpriorValue right (by simpa [hstart] using hhead.2)]
      have hnewValue :
          final[prior.size]? = some (node.eval input prior) := by
        rw [foldNodes_preserves input rest nextPrior prior.size (by
          simp [nextPrior])]
        rw [Array.getElem?_eq_getElem (by simp [nextPrior])]
        exact congrArg some (Array.getElem_push_eq
          (xs := prior) (x := node.eval input prior))
      change
        arrayAssignment base final (gateVariable base start) =
            nodeValue base input (arrayAssignment base final) node ∧
          NodesModelFrom base (start + 1) input
            (arrayAssignment base final) rest
      constructor
      · rw [arrayAssignment_gateVariable, ← hstart, hnewValue]
        simp [hnodeValue]
      · simpa [nextPrior, final] using
          ih (start + 1) nextPrior (by simp [nextPrior, hstart]) htail

theorem circuitFormula_satisfiable_iff_eval {n : ℕ}
    (base : ℕ) (input : BitInput n) (circuit : BooleanCircuit n) :
    (∃ assignment : ℕ → Bool,
      formulaEval assignment (circuitFormula base input circuit) = true) ↔
        circuit.eval input = true := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    have hparts :=
      (circuitFormula_eval_iff base input circuit assignment).mp hsatisfies
    have hagrees : PriorAgrees base assignment (circuit.values input) := by
      apply foldNodes_agrees base 0 input assignment circuit.nodes #[]
      · rfl
      · intro offset
        simpa using circuit.wellFormed offset
      · exact hparts.1
      · intro index hindex
        simp at hindex
    have houtput :=
      hagrees circuit.output.val (by
        rw [BooleanCircuit.values, foldNodes_size]
        simp only [Array.size_empty, zero_add]
        exact circuit.output.isLt)
    rw [show circuit.eval input =
        (circuit.values input)[circuit.output.val]?.getD false by rfl]
    rw [houtput]
    simp [hparts.2]
  · intro haccepts
    let values := circuit.values input
    let assignment := arrayAssignment base values
    refine ⟨assignment, (circuitFormula_eval_iff
      base input circuit assignment).mpr ?_⟩
    constructor
    · simpa [assignment, values, BooleanCircuit.values] using
        canonicalModelFrom base 0 input circuit.nodes #[] rfl (by
          intro offset
          simpa using circuit.wellFormed offset)
    · simpa [assignment, values, BooleanCircuit.eval] using haccepts

/-! ## Connection to the concrete SAT opcode -/

def clauseMaximum (initial : ℕ) (clause : EncodedClause) : ℕ :=
  clause.foldl (fun maximum literal => max maximum literal.2) initial

def formulaMaximum (formula : EncodedCNF) : ℕ :=
  formula.foldl clauseMaximum 0

theorem cnfVariableCount_eq_formulaMaximum (formula : EncodedCNF) :
    cnfVariableCount formula = formulaMaximum formula + 1 := by
  rfl

private theorem initial_le_clauseMaximum (initial : ℕ)
    (clause : EncodedClause) :
    initial ≤ clauseMaximum initial clause := by
  induction clause generalizing initial with
  | nil =>
      rfl
  | cons literal rest ih =>
      exact (Nat.le_max_left _ _).trans (ih (max initial literal.2))

private theorem literal_le_clauseMaximum (initial : ℕ)
    {clause : EncodedClause} {literal : EncodedLiteral}
    (hmember : literal ∈ clause) :
    literal.2 ≤ clauseMaximum initial clause := by
  induction clause generalizing initial with
  | nil =>
      simp at hmember
  | cons head rest ih =>
      simp only [List.mem_cons] at hmember
      simp only [clauseMaximum, List.foldl_cons]
      rcases hmember with rfl | htail
      · exact (Nat.le_max_right _ _).trans
          (initial_le_clauseMaximum (max initial literal.2) rest)
      · exact ih (max initial head.2) htail

private theorem initial_le_formulaFold (initial : ℕ)
    (formula : EncodedCNF) :
    initial ≤ formula.foldl clauseMaximum initial := by
  induction formula generalizing initial with
  | nil =>
      rfl
  | cons clause rest ih =>
      exact (initial_le_clauseMaximum initial clause).trans
        (ih (clauseMaximum initial clause))

private theorem clauseMaximum_mono {smaller larger : ℕ}
    (hbound : smaller ≤ larger) (clause : EncodedClause) :
    clauseMaximum smaller clause ≤ clauseMaximum larger clause := by
  induction clause generalizing smaller larger with
  | nil =>
      exact hbound
  | cons literal rest ih =>
      exact ih (max_le_max hbound le_rfl)

private theorem formulaFold_mono {smaller larger : ℕ}
    (hbound : smaller ≤ larger) (formula : EncodedCNF) :
    formula.foldl clauseMaximum smaller ≤
      formula.foldl clauseMaximum larger := by
  induction formula generalizing smaller larger with
  | nil =>
      exact hbound
  | cons clause rest ih =>
      exact ih (clauseMaximum_mono hbound clause)

private theorem literal_le_formulaMaximum {formula : EncodedCNF}
    {clause : EncodedClause} {literal : EncodedLiteral}
    (hclause : clause ∈ formula) (hliteral : literal ∈ clause) :
    literal.2 ≤ formulaMaximum formula := by
  induction formula generalizing clause with
  | nil =>
      simp at hclause
  | cons head rest ih =>
      simp only [List.mem_cons] at hclause
      simp only [formulaMaximum, List.foldl_cons]
      rcases hclause with hequal | htail
      · subst clause
        exact (literal_le_clauseMaximum 0 hliteral).trans
          (initial_le_formulaFold (clauseMaximum 0 head) rest)
      · have hrest :
          literal.2 ≤ rest.foldl clauseMaximum 0 :=
            ih htail hliteral
        have hmono :
            rest.foldl clauseMaximum 0 ≤
              rest.foldl clauseMaximum (clauseMaximum 0 head) := by
          exact formulaFold_mono (Nat.zero_le _) rest
        exact hrest.trans hmono

theorem literal_index_lt_cnfVariableCount {formula : EncodedCNF}
    {clause : EncodedClause} {literal : EncodedLiteral}
    (hclause : clause ∈ formula) (hliteral : literal ∈ clause) :
    literal.2 < cnfVariableCount formula := by
  rw [cnfVariableCount_eq_formulaMaximum]
  exact Nat.lt_succ_of_le (literal_le_formulaMaximum hclause hliteral)

def restrictAssignment (formula : EncodedCNF)
    (assignment : ℕ → Bool) : BitInput (cnfVariableCount formula) :=
  fun index => assignment index.val

theorem encodedCNFEval_restrictAssignment
    (formula : EncodedCNF) (assignment : ℕ → Bool) :
    encodedCNFEval formula (restrictAssignment formula assignment) =
      formulaEval assignment formula := by
  have clauseEquality :
      ∀ clause ∈ formula,
        clause.any (encodedLiteralEval
          (by simp [cnfVariableCount])
          (restrictAssignment formula assignment)) =
            clause.any (literalEval assignment) := by
    intro clause hclause
    have literalSublistEquality :
        ∀ literals : EncodedClause,
          (∀ literal ∈ literals, literal ∈ clause) →
          literals.any (encodedLiteralEval
            (by simp [cnfVariableCount])
            (restrictAssignment formula assignment)) =
              literals.any (literalEval assignment) := by
      intro literals hsubset
      induction literals with
      | nil =>
          rfl
      | cons literal rest ih =>
          simp only [List.any_cons]
          have hindex :
              literal.2 % cnfVariableCount formula = literal.2 :=
            Nat.mod_eq_of_lt
              (literal_index_lt_cnfVariableCount hclause
                (hsubset literal (by simp)))
          congr 1
          · simp [encodedLiteralEval, restrictAssignment, literalEval, hindex]
          · exact ih (by
              intro nextLiteral hnext
              exact hsubset nextLiteral (by simp [hnext]))
    exact literalSublistEquality clause (by simp)
  have subformulaEquality :
      ∀ subformula : EncodedCNF,
        (∀ clause ∈ subformula, clause ∈ formula) →
        subformula.all (fun clause =>
          clause.any (encodedLiteralEval
            (by simp [cnfVariableCount])
            (restrictAssignment formula assignment))) =
          subformula.all (clauseEval assignment) := by
    intro subformula hsubset
    induction subformula with
    | nil =>
        rfl
    | cons clause rest ih =>
        simp only [List.all_cons]
        rw [clauseEquality clause (hsubset clause (by simp))]
        rw [ih (by
          intro nextClause hnext
          exact hsubset nextClause (by simp [hnext]))]
        rfl
  exact subformulaEquality formula (by simp)

/-- Little-endian assignment encoding used only to exhibit the concrete member
of the SAT interpreter's exhaustive `List.range`; it is independent of the
repository's structural request codecs. -/
def bitAssignmentCode : {arity : ℕ} → BitInput arity → ℕ
  | 0, _ => 0
  | arity + 1, assignment =>
      Nat.bit (assignment ⟨0, by omega⟩)
        (bitAssignmentCode fun index => assignment index.succ)

theorem bitAssignmentCode_lt_two_pow {arity : ℕ}
    (assignment : BitInput arity) :
    bitAssignmentCode assignment < 2 ^ arity := by
  induction arity with
  | zero =>
      simp [bitAssignmentCode]
  | succ arity ih =>
      rw [bitAssignmentCode]
      have htail :=
        ih (fun index : Fin arity => assignment index.succ)
      cases hhead : assignment ⟨0, by omega⟩ <;>
        simp [Nat.bit, pow_succ] <;>
        omega

theorem bitAssignmentCode_testBit {arity : ℕ}
    (assignment : BitInput arity) (index : Fin arity) :
    (bitAssignmentCode assignment).testBit index.val = assignment index := by
  induction arity with
  | zero =>
      exact Fin.elim0 index
  | succ arity ih =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · simp [bitAssignmentCode]
      · simpa [bitAssignmentCode, Nat.testBit_bit_succ] using
          ih (fun next : Fin arity => assignment next.succ) tail

@[simp] theorem decodeCNF_encode (formula : EncodedCNF) :
    decodeCNF (Encodable.encode formula) = formula := by
  simp [decodeCNF, Encodable.encodek]

theorem encodedSat_encode_eq_true_iff
    (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true) :
    encodedSat (Encodable.encode formula) = true ↔
      ∃ assignment : ℕ → Bool,
        formulaEval assignment formula = true := by
  unfold encodedSat
  rw [decodeCNF_encode, if_pos hwell]
  unfold legacyEncodedSat
  rw [decodeCNF_encode, if_pos hwell, List.any_eq_true]
  constructor
  · rintro ⟨assignmentCode, hcode, haccepts⟩
    let assignment : ℕ → Bool :=
      fun index => assignmentCode.testBit index
    refine ⟨assignment, ?_⟩
    have heval :=
      encodedCNFEval_restrictAssignment formula assignment
    simpa [assignment, restrictAssignment] using heval.symm.trans haccepts
  · rintro ⟨assignment, haccepts⟩
    let finiteAssignment := restrictAssignment formula assignment
    let assignmentCode := bitAssignmentCode finiteAssignment
    refine ⟨assignmentCode,
      List.mem_range.mpr (bitAssignmentCode_lt_two_pow finiteAssignment), ?_⟩
    have hfunction :
        (fun index : Fin (cnfVariableCount formula) =>
          assignmentCode.testBit index.val) =
            finiteAssignment := by
      funext index
      exact bitAssignmentCode_testBit finiteAssignment index
    rw [hfunction]
    change encodedCNFEval formula
      (restrictAssignment formula assignment) = true
    rw [encodedCNFEval_restrictAssignment, haccepts]

theorem encodedSat_circuitFormula_eq_true_iff_eval {n : ℕ}
    (base : ℕ) (input : BitInput n) (circuit : BooleanCircuit n)
    (hwell :
      wellSizedCNFEncoding
        (Encodable.encode (circuitFormula base input circuit))
        (circuitFormula base input circuit) = true) :
    encodedSat (Encodable.encode (circuitFormula base input circuit)) = true ↔
      circuit.eval input = true := by
  rw [encodedSat_encode_eq_true_iff _ hwell,
    circuitFormula_satisfiable_iff_eval]

private theorem twice_right_le_pair_succ (left right : ℕ) :
    2 * right ≤ Nat.pair left right + 1 := by
  rw [Nat.pair]
  split_ifs with horder
  · have hpositive : 1 ≤ right := by omega
    nlinarith
  · have hle : right ≤ left := Nat.le_of_not_gt horder
    nlinarith

/-- Canonical list codes grow quickly enough that the SAT interpreter's
structural list-length guard is automatic. -/
theorem list_length_le_encoded_bitLength
    {α : Type} [Encodable α] (values : List α) :
    values.length ≤ natBitLength (Encodable.encode values) := by
  induction values with
  | nil =>
      simp [natBitLength]
  | cons value rest ih =>
      cases rest with
      | nil =>
          simp [natBitLength, Encodable.encode_list_cons]
      | cons next rest =>
          let tailCode := Encodable.encode (next :: rest)
          have htailPositive : tailCode ≠ 0 := by
            intro hzero
            have hequal :
                Encodable.encode (next :: rest) =
                  Encodable.encode ([] : List α) := by
              simp [tailCode] at hzero
            have := Encodable.encode_injective hequal
            simp at this
          have hdouble :
              tailCode * 2 ≤
                Encodable.encode (value :: next :: rest) := by
            rw [Encodable.encode_list_cons]
            simpa [tailCode, Nat.mul_comm] using
              twice_right_le_pair_succ (Encodable.encode value) tailCode
          have hlog :
              Nat.log 2 tailCode + 1 ≤
                Nat.log 2 (Encodable.encode (value :: next :: rest)) := by
            rw [← Nat.log_mul_base (b := 2)
              (n := tailCode) (by omega) htailPositive]
            exact Nat.log_mono_right hdouble
          dsimp only [tailCode] at hlog
          simp only [List.length_cons, natBitLength] at ih ⊢
          omega

private theorem nodeClauses_zero_indices_lt {n : ℕ}
    {index bound : ℕ} (input : BitInput n) (node : BooleanNode n)
    (hindex : index < bound)
    (hwell : node.WellFormedAt index) :
    (nodeClauses 0 index input node).all
      (fun clause =>
        clause.all (fun literal => literal.2 < bound)) = true := by
  cases node with
  | const value =>
      cases value <;>
        simp [nodeClauses, positiveUnit, negativeUnit, triple,
          positive, negative, gateVariable, hindex]
  | input source =>
      cases hinput : input source <;>
        simp [nodeClauses, positiveUnit, negativeUnit, triple,
          positive, negative, gateVariable, hindex, hinput]
  | not child =>
      have hchild : child < bound :=
        lt_trans hwell hindex
      simp [nodeClauses, triple, positive, negative, gateVariable,
        hindex, hchild]
  | and left right =>
      have hleft : left < bound :=
        lt_trans hwell.1 hindex
      have hright : right < bound :=
        lt_trans hwell.2 hindex
      simp [nodeClauses, triple, positive, negative, gateVariable,
        hindex, hleft, hright]
  | or left right =>
      have hleft : left < bound :=
        lt_trans hwell.1 hindex
      have hright : right < bound :=
        lt_trans hwell.2 hindex
      simp [nodeClauses, triple, positive, negative, gateVariable,
        hindex, hleft, hright]

private theorem nodesClausesFrom_zero_indices_lt {n : ℕ}
    (start bound : ℕ) (input : BitInput n)
    (nodes : List (BooleanNode n))
    (hindex :
      ∀ offset : Fin nodes.length, start + offset.val < bound)
    (hwell :
      ∀ offset : Fin nodes.length,
        (nodes.get offset).WellFormedAt (start + offset.val)) :
    (nodesClausesFrom 0 start input nodes).all
      (fun clause =>
        clause.all (fun literal => literal.2 < bound)) = true := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      have hheadIndex : start < bound := by
        simpa using hindex ⟨0, by simp⟩
      have hheadWell : node.WellFormedAt start := by
        simpa using hwell ⟨0, by simp⟩
      have htailIndex :
          ∀ offset : Fin rest.length,
            start + 1 + offset.val < bound := by
        intro offset
        have hnext := hindex
          ⟨offset.val + 1, by simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      have htailWell :
          ∀ offset : Fin rest.length,
            (rest.get offset).WellFormedAt
              (start + 1 + offset.val) := by
        intro offset
        have hnext := hwell
          ⟨offset.val + 1, by simp⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
      simp only [nodesClausesFrom, List.all_append, Bool.and_eq_true]
      exact ⟨nodeClauses_zero_indices_lt input node
          hheadIndex hheadWell,
        ih (start + 1) htailIndex htailWell⟩

theorem circuitFormula_zero_indices_lt {n : ℕ}
    (input : BitInput n) (circuit : BooleanCircuit n) :
    (circuitFormula 0 input circuit).all
      (fun clause =>
        clause.all (fun literal =>
          literal.2 < circuit.nodes.length)) = true := by
  rw [circuitFormula, List.all_append, Bool.and_eq_true]
  constructor
  · apply nodesClausesFrom_zero_indices_lt
    · intro offset
      rw [zero_add]
      exact offset.isLt
    · intro offset
      rw [zero_add]
      exact circuit.wellFormed offset
  · simp [positiveUnit, triple, positive, gateVariable,
      circuit.output.isLt]

private theorem nodeClauses_length_positive {n : ℕ}
    (base index : ℕ) (input : BitInput n) (node : BooleanNode n) :
    1 ≤ (nodeClauses base index input node).length := by
  cases node with
  | const value =>
      cases value <;> simp [nodeClauses]
  | input source =>
      cases hinput : input source <;> simp [nodeClauses, hinput]
  | not child =>
      simp [nodeClauses]
  | and left right =>
      simp [nodeClauses]
  | or left right =>
      simp [nodeClauses]

private theorem nodes_length_le_clauses_length {n : ℕ}
    (base start : ℕ) (input : BitInput n)
    (nodes : List (BooleanNode n)) :
    nodes.length ≤ (nodesClausesFrom base start input nodes).length := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      simp only [List.length_cons, nodesClausesFrom, List.length_append]
      have hnode :=
        nodeClauses_length_positive base start input node
      have hrest := ih (start + 1)
      omega

theorem circuit_nodes_length_le_formula_length {n : ℕ}
    (base : ℕ) (input : BitInput n) (circuit : BooleanCircuit n) :
    circuit.nodes.length ≤
      (circuitFormula base input circuit).length := by
  rw [circuitFormula, List.length_append]
  have hnodes :=
    nodes_length_le_clauses_length base 0 input circuit.nodes
  simp only [List.length_singleton]
  omega

/-- The canonical zero-based circuit formula always passes the SAT opcode's
syntactic guard: all clauses are ternary, node variables are topologically
bounded, and the canonical list code has enough bits for both bounds. -/
theorem circuitFormula_wellSized {n : ℕ}
    (input : BitInput n) (circuit : BooleanCircuit n) :
    wellSizedCNFEncoding
      (Encodable.encode (circuitFormula 0 input circuit))
      (circuitFormula 0 input circuit) = true := by
  rw [wellSizedCNFEncoding, Bool.and_eq_true]
  constructor
  · exact decide_eq_true
      (list_length_le_encoded_bitLength
        (circuitFormula 0 input circuit))
  · rw [List.all_eq_true]
    intro clause hclause
    rw [Bool.and_eq_true]
    constructor
    · have hthree :=
        (List.all_eq_true.mp
          (circuitFormula_threeLiteral 0 input circuit))
          clause hclause
      simpa using hthree
    · rw [List.all_eq_true]
      intro literal hliteral
      have hindices :=
        (List.all_eq_true.mp
          (circuitFormula_zero_indices_lt input circuit))
          clause hclause
      have hindex :=
        (List.all_eq_true.mp hindices) literal hliteral
      have hnodeLength :
          circuit.nodes.length ≤
            (circuitFormula 0 input circuit).length :=
        circuit_nodes_length_le_formula_length 0 input circuit
      have hcodeLength :
          (circuitFormula 0 input circuit).length ≤
            natBitLength
              (Encodable.encode (circuitFormula 0 input circuit)) :=
        list_length_le_encoded_bitLength
          (circuitFormula 0 input circuit)
      exact decide_eq_true
        (lt_of_lt_of_le (of_decide_eq_true hindex)
          (hnodeLength.trans hcodeLength))

theorem encodedSat_circuitFormula_zero_eq_true_iff_eval {n : ℕ}
    (input : BitInput n) (circuit : BooleanCircuit n) :
    encodedSat (Encodable.encode (circuitFormula 0 input circuit)) = true ↔
      circuit.eval input = true :=
  encodedSat_circuitFormula_eq_true_iff_eval 0 input circuit
    (circuitFormula_wellSized input circuit)

end NearCubicWires.TseitinCNF
