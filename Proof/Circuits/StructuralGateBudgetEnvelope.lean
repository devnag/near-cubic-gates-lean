import Proof.Circuits.BoundedOracleStructuralFormulaAtomSchedule
import Proof.Foundations.CanonicalBalanced
import Proof.Circuits.ValidatorLeafWidthCore

namespace NearCubicWires.R1Leaf56StructuralGateBudgetEnvelope

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TseitinCNF
open NearCubicWires.ValidatorLeafWidthCore

/-! ## §1 The four recurrence collapses -/
theorem literalNodeCount_le_one {q : ℕ} (literal : Literal q) :
    literalNodeCount literal ≤ 1 := by
  cases literal <;> simp [literalNodeCount]

theorem clauseNodeCount_le_five {q : ℕ} (clause : Fin 3 → Literal q) :
    clauseNodeCount clause ≤ 5 := by
  have h0 := literalNodeCount_le_one (clause 0)
  have h1 := literalNodeCount_le_one (clause 1)
  have h2 := literalNodeCount_le_one (clause 2)
  unfold clauseNodeCount
  omega

theorem clausesNodeCount_le {q : ℕ} (clauses : List (Fin 3 → Literal q)) :
    clausesNodeCount clauses ≤ 6 * clauses.length + 1 := by
  induction clauses with
  | nil => simp [clausesNodeCount]
  | cons clause rest ih =>
      have h := clauseNodeCount_le_five clause
      simp only [clausesNodeCount, List.length_cons]
      omega

theorem universalOutputsNodeCount_le {n bound : ℕ}
    (count : ℕ) (hcount : count ≤ bound) (perAddress : ℕ)
    (addresses : List (BitInput n))
    (h : ∀ address : BitInput n,
      universalOutputNodeCount (bound := bound) address count hcount ≤
        perAddress) :
    universalOutputsNodeCount (bound := bound) count hcount addresses ≤
      perAddress * addresses.length := by
  induction addresses with
  | nil => simp [universalOutputsNodeCount]
  | cons address rest ih =>
      have hhead := h address
      simp only [universalOutputsNodeCount, List.length_cons]
      refine (Nat.add_le_add hhead ih).trans (le_of_eq ?_)
      ring

theorem verifierRowsNodeCount_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (perRow : ℕ) (rows : List (BitInput (pcp.nativeWidth n)))
    (h : ∀ randomness : BitInput (pcp.nativeWidth n),
      verifierRowNodeCount (bound := bound) pcp input count hcount
        randomness ≤ perRow) :
    verifierRowsNodeCount (bound := bound) pcp input count hcount rows ≤
      (perRow + 1) * rows.length + 1 := by
  induction rows with
  | nil => simp [verifierRowsNodeCount]
  | cons randomness rest ih =>
      have hhead := h randomness
      simp only [verifierRowsNodeCount, List.length_cons]
      refine (Nat.add_le_add (Nat.add_le_add hhead ih) (le_refl 1)).trans
        (le_of_eq ?_)
      ring

theorem countCasesNodeCount_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (perCount : ℕ) (counts : List (Fin bound))
    (h : ∀ count : Fin bound,
      fixedCountNodeCount (bound := bound) pcp input count ≤ perCount) :
    countCasesNodeCount (bound := bound) pcp input counts ≤
      (perCount + 2) * counts.length + 1 := by
  induction counts with
  | nil => simp [countCasesNodeCount]
  | cons count rest ih =>
      have hhead := h count
      simp only [countCasesNodeCount, List.length_cons]
      have hexpand :
          (perCount + 2) * (rest.length + 1) + 1 =
            (perCount + 2) * rest.length + 1 + perCount + 2 := by ring
      omega

/-- The gate budget from a uniform per-count envelope. -/
theorem boundedOracleStructuralGateBudget_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound perCount : ℕ)
    (h : ∀ count : Fin bound,
      fixedCountNodeCount (bound := bound) pcp input count ≤ perCount) :
    boundedOracleStructuralGateBudget pcp input bound ≤
      (perCount + 2) * bound + 1 := by
  have hcollapse :=
    countCasesNodeCount_le pcp input perCount
      (List.ofFn (id : Fin bound → Fin bound)) h
  simpa only [boundedOracleStructuralGateBudget, List.length_ofFn] using
    hcollapse

/-- The per-count envelope from a grammar envelope and a per-row envelope. -/
theorem fixedCountNodeCount_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : Fin bound) (grammarNodes perRow : ℕ)
    (hgrammar :
      (fixedCountGrammarExpr (n := pcp.nativeWidth n)
        (bound := bound) count).nodeCount ≤ grammarNodes)
    (hrow : ∀ randomness : BitInput (pcp.nativeWidth n),
      verifierRowNodeCount (bound := bound) pcp input (count.val + 1)
        (by omega) randomness ≤ perRow) :
    fixedCountNodeCount (bound := bound) pcp input count ≤
      grammarNodes + ((perRow + 1) * 2 ^ pcp.nativeWidth n + 1) + 1 := by
  have hrows :=
    verifierRowsNodeCount_le pcp input (count.val + 1) (by omega) perRow
      (allRandomness (pcp.nativeWidth n)) hrow
  rw [allRandomness_length] at hrows
  unfold fixedCountNodeCount
  omega

/-- The per-row envelope from a per-address envelope and the decision clause
count. -/
theorem verifierRowNodeCount_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n))
    (perAddress clauseCount : ℕ)
    (haddress : ∀ address : BitInput (pcp.nativeWidth n),
      universalOutputNodeCount (bound := bound) address count hcount ≤
        perAddress)
    (hclauses :
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    verifierRowNodeCount (bound := bound) pcp input count hcount randomness ≤
      perAddress * pcp.queryCount n + (6 * clauseCount + 1) := by
  have hqueries :=
    universalOutputsNodeCount_le (bound := bound) count hcount perAddress
      (projectedAddresses pcp input randomness) haddress
  rw [projectedAddresses_length] at hqueries
  have hdecision :=
    (clausesNodeCount_le (pcp.decision input randomness).clauses).trans
      (by omega : 6 * (pcp.decision input randomness).clauses.length + 1 ≤
        6 * clauseCount + 1)
  unfold verifierRowNodeCount
  omega

/-! ## §2 `BoolExpr.nodeCount` envelopes -/

theorem nodeCount_all_ofFn_le {n m : ℕ} (f : Fin m → BoolExpr n) (b : ℕ)
    (h : ∀ i, (f i).nodeCount ≤ b) :
    (BoolExpr.all (List.ofFn f)).nodeCount ≤ m * (b + 1) + 1 := by
  have hmem : ∀ expression ∈ List.ofFn f, expression.nodeCount ≤ b := by
    intro expression hexpression
    simp only [List.mem_ofFn] at hexpression
    obtain ⟨i, rfl⟩ := hexpression
    exact h i
  simpa using BoolExpr.nodeCount_all_le (List.ofFn f) b hmem

theorem nodeCount_any_ofFn_le {n m : ℕ} (f : Fin m → BoolExpr n) (b : ℕ)
    (h : ∀ i, (f i).nodeCount ≤ b) :
    (BoolExpr.any (List.ofFn f)).nodeCount ≤ m * (b + 1) + 1 := by
  have hmem : ∀ expression ∈ List.ofFn f, expression.nodeCount ≤ b := by
    intro expression hexpression
    simp only [List.mem_ofFn] at hexpression
    obtain ⟨i, rfl⟩ := hexpression
    exact h i
  simpa using BoolExpr.nodeCount_any_le (List.ofFn f) b hmem

theorem nodeCount_any_map_range_le {n : ℕ} (upper : ℕ)
    (f : ℕ → BoolExpr n) (b : ℕ) (h : ∀ i, (f i).nodeCount ≤ b) :
    (BoolExpr.any ((List.range upper).map f)).nodeCount ≤
      upper * (b + 1) + 1 := by
  have hmem :
      ∀ expression ∈ (List.range upper).map f, expression.nodeCount ≤ b := by
    intro expression hexpression
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hexpression
    exact h i
  simpa using BoolExpr.nodeCount_any_le ((List.range upper).map f) b hmem

/-! ## The unary block -/

theorem unaryEqualsExpr_nodeCount_le {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    (unaryEqualsExpr (n := n) (bound := bound) row start limit value
      hblock).nodeCount ≤ 3 * limit + 1 := by
  have hbase :
      (unaryEqualsExpr (n := n) (bound := bound) row start limit value
        hblock).nodeCount ≤ limit * (2 + 1) + 1 := by
    refine nodeCount_all_ofFn_le _ 2 ?_
    intro offset
    dsimp only
    split <;> simp [BoolExpr.nodeCount]
  omega

theorem tagEqualsExpr_nodeCount_le {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (tagEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤ 19 := by
  have := unaryEqualsExpr_nodeCount_le (n := n) (bound := bound) row 0 6 value
    (by simp [rowWidth])
  simpa [tagEqualsExpr] using this

theorem firstFieldEqualsExpr_nodeCount_le {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (firstFieldEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤
      3 * boundedCircuitFieldLimit n bound + 1 := by
  have := unaryEqualsExpr_nodeCount_le (n := n) (bound := bound) row 6
    (boundedCircuitFieldLimit n bound) value (by simp [rowWidth]; omega)
  simpa [firstFieldEqualsExpr] using this

theorem secondFieldEqualsExpr_nodeCount_le {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (secondFieldEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤
      3 * boundedCircuitFieldLimit n bound + 1 := by
  have := unaryEqualsExpr_nodeCount_le (n := n) (bound := bound) row
    (6 + boundedCircuitFieldLimit n bound)
    (boundedCircuitFieldLimit n bound) value (by simp [rowWidth]; omega)
  simpa [secondFieldEqualsExpr] using this

/-! ## The atomic envelope -/

/-- One envelope covering every atomic structural predicate of a row. -/
def atomEnvelope (n bound : ℕ) : ℕ :=
  (n + bound + 1) * (3 * boundedCircuitFieldLimit n bound + 1 + 1) + 20

theorem fieldLimit_le_atomEnvelope (n bound : ℕ) :
    3 * boundedCircuitFieldLimit n bound + 1 ≤ atomEnvelope n bound := by
  unfold atomEnvelope boundedCircuitFieldLimit
  nlinarith [Nat.zero_le n, Nat.zero_le bound]

theorem tagEqualsExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (tagEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤
      atomEnvelope n bound := by
  refine (tagEqualsExpr_nodeCount_le row value).trans ?_
  unfold atomEnvelope
  omega

theorem firstFieldEqualsExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (firstFieldEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤
      atomEnvelope n bound :=
  (firstFieldEqualsExpr_nodeCount_le row value).trans
    (fieldLimit_le_atomEnvelope n bound)

theorem secondFieldEqualsExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    (secondFieldEqualsExpr (n := n) (bound := bound) row value).nodeCount ≤
      atomEnvelope n bound :=
  (secondFieldEqualsExpr_nodeCount_le row value).trans
    (fieldLimit_le_atomEnvelope n bound)

theorem firstFieldLessExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ) (hupper : upper ≤ n + bound + 1) :
    (firstFieldLessExpr (n := n) (bound := bound) row upper).nodeCount ≤
      atomEnvelope n bound := by
  have hraw :
      (firstFieldLessExpr (n := n) (bound := bound) row upper).nodeCount ≤
        upper * (3 * boundedCircuitFieldLimit n bound + 1 + 1) + 1 := by
    refine nodeCount_any_map_range_le upper _
      (3 * boundedCircuitFieldLimit n bound + 1) ?_
    intro i
    exact firstFieldEqualsExpr_nodeCount_le row i
  refine hraw.trans ?_
  unfold atomEnvelope
  have hmul :
      upper * (3 * boundedCircuitFieldLimit n bound + 1 + 1) ≤
        (n + bound + 1) * (3 * boundedCircuitFieldLimit n bound + 1 + 1) :=
    Nat.mul_le_mul_right _ hupper
  omega

theorem secondFieldLessExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ) (hupper : upper ≤ n + bound + 1) :
    (secondFieldLessExpr (n := n) (bound := bound) row upper).nodeCount ≤
      atomEnvelope n bound := by
  have hraw :
      (secondFieldLessExpr (n := n) (bound := bound) row upper).nodeCount ≤
        upper * (3 * boundedCircuitFieldLimit n bound + 1 + 1) + 1 := by
    refine nodeCount_any_map_range_le upper _
      (3 * boundedCircuitFieldLimit n bound + 1) ?_
    intro i
    exact secondFieldEqualsExpr_nodeCount_le row i
  refine hraw.trans ?_
  unfold atomEnvelope
  have hmul :
      upper * (3 * boundedCircuitFieldLimit n bound + 1 + 1) ≤
        (n + bound + 1) * (3 * boundedCircuitFieldLimit n bound + 1 + 1) :=
    Nat.mul_le_mul_right _ hupper
  omega

theorem constantAddressSelectionExpr_le_atomEnvelope {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n) :
    (constantAddressSelectionExpr (n := n) (bound := bound) row
      address).nodeCount ≤ atomEnvelope n bound := by
  have hraw :
      (constantAddressSelectionExpr (n := n) (bound := bound) row
        address).nodeCount ≤
        n * (3 * boundedCircuitFieldLimit n bound + 1 + 1) + 1 := by
    refine nodeCount_any_ofFn_le _ (3 * boundedCircuitFieldLimit n bound + 1) ?_
    intro index
    split
    · exact firstFieldEqualsExpr_nodeCount_le row index.val
    · simp [BoolExpr.nodeCount]
  refine hraw.trans ?_
  unfold atomEnvelope
  have hmul :
      n * (3 * boundedCircuitFieldLimit n bound + 1 + 1) ≤
        (n + bound + 1) * (3 * boundedCircuitFieldLimit n bound + 1 + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## §3 Row and grammar envelopes -/

/-- Envelope for one described DAG row predicate. -/
def rowEnvelope (n bound : ℕ) : ℕ :=
  16 * atomEnvelope n bound + 64

theorem nodeRowExpr_le {n bound : ℕ} (row : Fin (bound + 1)) :
    (nodeRowExpr (n := n) (bound := bound) row).nodeCount ≤
      rowEnvelope n bound := by
  have hrow : row.val ≤ n + bound + 1 := by
    have := row.isLt
    omega
  have hn : n ≤ n + bound + 1 := by omega
  have ht0 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  have ht1 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 1
  have ht2 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 2
  have ht3 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 3
  have ht4 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 4
  have hf0 :=
    firstFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  have hf1 :=
    firstFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 1
  have hs0 :=
    secondFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  have hlessN :=
    firstFieldLessExpr_le_atomEnvelope (n := n) (bound := bound) row n hn
  have hlessRow :=
    firstFieldLessExpr_le_atomEnvelope (n := n) (bound := bound) row row.val
      hrow
  have hsecondLessRow :=
    secondFieldLessExpr_le_atomEnvelope (n := n) (bound := bound) row row.val
      hrow
  unfold rowEnvelope
  simp only [nodeRowExpr, BoolExpr.any, BoolExpr.all, BoolExpr.nodeCount]
  omega

theorem outputRowExpr_le {n bound : ℕ} (row : Fin (bound + 1)) :
    (outputRowExpr (n := n) (bound := bound) row).nodeCount ≤
      rowEnvelope n bound := by
  have hrow : row.val ≤ n + bound + 1 := by
    have := row.isLt
    omega
  have ht5 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 5
  have hlessRow :=
    firstFieldLessExpr_le_atomEnvelope (n := n) (bound := bound) row row.val
      hrow
  have hs0 :=
    secondFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  unfold rowEnvelope
  simp only [outputRowExpr, BoolExpr.all, BoolExpr.nodeCount]
  omega

theorem paddingRowExpr_le {n bound : ℕ} (row : Fin (bound + 1)) :
    (paddingRowExpr (n := n) (bound := bound) row).nodeCount ≤
      rowEnvelope n bound := by
  have ht6 := tagEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 6
  have hf0 :=
    firstFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  have hs0 :=
    secondFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 0
  unfold rowEnvelope
  simp only [paddingRowExpr, BoolExpr.all, BoolExpr.nodeCount]
  omega

/-- Envelope for the fixed-count grammar predicate. -/
def grammarEnvelope (n bound : ℕ) : ℕ :=
  (bound + 1) * (rowEnvelope n bound + 1) + 1

theorem fixedCountGrammarExpr_le {n bound : ℕ} (count : Fin bound) :
    (fixedCountGrammarExpr (n := n) (bound := bound) count).nodeCount ≤
      grammarEnvelope n bound := by
  have hcount := count.isLt
  have hmem :
      ∀ expression ∈
          (countNodeRows (n := n) (bound := bound) count ++
            outputRowExpr (n := n) (bound := bound)
                ⟨count.val + 1, by omega⟩ ::
              countPaddingRows (n := n) (bound := bound) count),
        expression.nodeCount ≤ rowEnvelope n bound := by
    intro expression hexpression
    rcases List.mem_append.mp hexpression with hnode | htail
    · simp only [countNodeRows, List.mem_ofFn] at hnode
      obtain ⟨index, rfl⟩ := hnode
      exact nodeRowExpr_le _
    · rcases List.mem_cons.mp htail with rfl | hpadding
      · exact outputRowExpr_le _
      · simp only [countPaddingRows, List.mem_ofFn] at hpadding
        obtain ⟨offset, rfl⟩ := hpadding
        exact paddingRowExpr_le _
  have hlength :
      (countNodeRows (n := n) (bound := bound) count ++
        outputRowExpr (n := n) (bound := bound)
            ⟨count.val + 1, by omega⟩ ::
          countPaddingRows (n := n) (bound := bound) count).length =
        bound + 1 := by
    simp only [List.length_append, List.length_cons, countNodeRows,
      countPaddingRows, List.length_ofFn]
    omega
  have hbound :=
    BoolExpr.nodeCount_all_le
      (countNodeRows (n := n) (bound := bound) count ++
        outputRowExpr (n := n) (bound := bound)
            ⟨count.val + 1, by omega⟩ ::
          countPaddingRows (n := n) (bound := bound) count)
      (rowEnvelope n bound) hmem
  rw [hlength] at hbound
  exact hbound

/-! ## §4 The universal-evaluator envelopes -/

theorem guardedConditionsNodeCount_le {n : ℕ} (conditions : List (BoolExpr n))
    (envelope : ℕ)
    (h : ∀ expression ∈ conditions, expression.nodeCount ≤ envelope) :
    guardedConditionsNodeCount conditions ≤
      conditions.length * (envelope + 2) + 1 := by
  induction conditions with
  | nil => simp [guardedConditionsNodeCount]
  | cons condition rest ih =>
      have hhead := h condition (by simp)
      have htail := ih fun expression hexpression =>
        h expression (by simp [hexpression])
      simp only [guardedConditionsNodeCount, List.length_cons]
      refine (Nat.add_le_add (Nat.add_le_add_right hhead 2) htail).trans
        (le_of_eq ?_)
      ring

theorem fieldSelectionNodeCount_le {n bound : ℕ}
    (fieldEquals : Fin (bound + 1) → ℕ → BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (count envelope : ℕ)
    (h : ∀ value, (fieldEquals row value).nodeCount ≤ envelope) :
    fieldSelectionNodeCount fieldEquals row count ≤
      count * (envelope + 2) + 1 := by
  have hmem :
      ∀ expression ∈
          List.ofFn (fun index : Fin count => fieldEquals row index.val),
        expression.nodeCount ≤ envelope := by
    intro expression hexpression
    simp only [List.mem_ofFn] at hexpression
    obtain ⟨index, rfl⟩ := hexpression
    exact h index.val
  have hbound := guardedConditionsNodeCount_le _ envelope hmem
  simpa [fieldSelectionNodeCount] using hbound

theorem tagSelectionNodeCount_le {n bound : ℕ} (row : Fin (bound + 1)) :
    tagSelectionNodeCount (n := n) (bound := bound) row ≤
      5 * (atomEnvelope n bound + 2) + 1 := by
  have hmem :
      ∀ expression ∈
          ([tagEqualsExpr (n := n) (bound := bound) row 0,
            tagEqualsExpr (n := n) (bound := bound) row 1,
            tagEqualsExpr (n := n) (bound := bound) row 2,
            tagEqualsExpr (n := n) (bound := bound) row 3,
            tagEqualsExpr (n := n) (bound := bound) row 4] :
            List (BoolExpr (descriptionWidth n bound))),
        expression.nodeCount ≤ atomEnvelope n bound := by
    intro expression hexpression
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hexpression
    rcases hexpression with rfl | rfl | rfl | rfl | rfl <;>
      exact tagEqualsExpr_le_atomEnvelope row _
  have hbound := guardedConditionsNodeCount_le _ (atomEnvelope n bound) hmem
  simpa [tagSelectionNodeCount] using hbound

/-- Envelope for one universal-evaluator node, uniform over the prior count. -/
def nodeEnvelope (n bound : ℕ) : ℕ :=
  2 * (bound * (atomEnvelope n bound + 2) + 1) +
    2 * atomEnvelope n bound + 3 + (5 * (atomEnvelope n bound + 2) + 1)

theorem universalNodeNodeCount_le {n bound : ℕ} (row : Fin (bound + 1))
    (address : BitInput n) (priorCount : ℕ) (hprior : priorCount ≤ bound) :
    universalNodeNodeCount (n := n) (bound := bound) row address priorCount ≤
      nodeEnvelope n bound := by
  have hfirst :=
    fieldSelectionNodeCount_le (firstFieldEqualsExpr (n := n) (bound := bound))
      row priorCount (atomEnvelope n bound) fun value =>
        firstFieldEqualsExpr_le_atomEnvelope row value
  have hsecond :=
    fieldSelectionNodeCount_le (secondFieldEqualsExpr (n := n) (bound := bound))
      row priorCount (atomEnvelope n bound) fun value =>
        secondFieldEqualsExpr_le_atomEnvelope row value
  have hconstant :=
    firstFieldEqualsExpr_le_atomEnvelope (n := n) (bound := bound) row 1
  have haddress :=
    constantAddressSelectionExpr_le_atomEnvelope (n := n) (bound := bound) row
      address
  have htag := tagSelectionNodeCount_le (n := n) (bound := bound) row
  have hmono :
      priorCount * (atomEnvelope n bound + 2) ≤
        bound * (atomEnvelope n bound + 2) :=
    Nat.mul_le_mul_right _ hprior
  unfold universalNodeNodeCount nodeEnvelope
  omega

theorem universalNodesNodeCount_le {n bound : ℕ} (address : BitInput n) :
    ∀ (count : ℕ) (hcount : count ≤ bound),
      universalNodesNodeCount (bound := bound) address count hcount ≤
        count * nodeEnvelope n bound := by
  intro count
  induction count with
  | zero =>
      intro _
      simp [universalNodesNodeCount]
  | succ previous ih =>
      intro hcount
      have hrec := ih (by omega)
      have hnode :=
        universalNodeNodeCount_le (n := n) (bound := bound)
          ⟨previous, by omega⟩ address previous (by omega)
      change universalNodesNodeCount (bound := bound) address previous _ +
          universalNodeNodeCount (n := n) (bound := bound)
            ⟨previous, by omega⟩ address previous ≤ _
      refine (Nat.add_le_add hrec hnode).trans (le_of_eq ?_)
      ring

/-- Envelope for one universal output column. -/
def outputEnvelope (n bound : ℕ) : ℕ :=
  bound * nodeEnvelope n bound + (bound * (atomEnvelope n bound + 2) + 1)

theorem universalOutputNodeCount_le {n bound : ℕ} (address : BitInput n)
    (count : ℕ) (hcount : count ≤ bound) :
    universalOutputNodeCount (bound := bound) address count hcount ≤
      outputEnvelope n bound := by
  have hnodes := universalNodesNodeCount_le (n := n) (bound := bound) address
    count hcount
  have hfield :=
    fieldSelectionNodeCount_le (firstFieldEqualsExpr (n := n) (bound := bound))
      ⟨count, by omega⟩ count (atomEnvelope n bound) fun value =>
        firstFieldEqualsExpr_le_atomEnvelope _ value
  have hmonoNode : count * nodeEnvelope n bound ≤ bound * nodeEnvelope n bound :=
    Nat.mul_le_mul_right _ hcount
  have hmonoField :
      count * (atomEnvelope n bound + 2) ≤
        bound * (atomEnvelope n bound + 2) :=
    Nat.mul_le_mul_right _ hcount
  unfold universalOutputNodeCount outputEnvelope
  omega

/-! ## §5 The gate budget, assembled -/

/-- Envelope for one compiled verifier row. -/
def rowBudgetEnvelope (width bound queryCount clauseCount : ℕ) : ℕ :=
  outputEnvelope width bound * queryCount + (6 * clauseCount + 1)

/-- Envelope for one fixed-count block. -/
def fixedCountEnvelope (width bound queryCount clauseCount : ℕ) : ℕ :=
  grammarEnvelope width bound +
    ((rowBudgetEnvelope width bound queryCount clauseCount + 1) * 2 ^ width +
      1) + 1

/-- **Envelope for the whole C.12 structural gate budget.** -/
def structuralGateEnvelope (width bound queryCount clauseCount : ℕ) : ℕ :=
  (fixedCountEnvelope width bound queryCount clauseCount + 2) * bound + 1

theorem verifierRowNodeCount_envelope
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) (clauseCount : ℕ)
    (hclauses :
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    verifierRowNodeCount (bound := bound) pcp input count hcount randomness ≤
      rowBudgetEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n)
        clauseCount :=
  verifierRowNodeCount_le pcp input count hcount randomness
    (outputEnvelope (pcp.nativeWidth n) bound) clauseCount
    (fun address => universalOutputNodeCount_le address count hcount) hclauses

theorem fixedCountNodeCount_envelope
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : Fin bound) (clauseCount : ℕ)
    (hclauses : ∀ randomness : BitInput (pcp.nativeWidth n),
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    fixedCountNodeCount (bound := bound) pcp input count ≤
      fixedCountEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n)
        clauseCount :=
  fixedCountNodeCount_le pcp input count
    (grammarEnvelope (pcp.nativeWidth n) bound)
    (rowBudgetEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n) clauseCount)
    (fixedCountGrammarExpr_le count)
    (fun randomness =>
      verifierRowNodeCount_envelope pcp input (count.val + 1) (by omega)
        randomness clauseCount (hclauses randomness))

/-- **The C.12 structural gate budget is polynomial in the padded shape.**
Nothing in the four roots bounded this above before; every prior theorem about
it is an exact `compile*_addedNodes` equality. -/
theorem boundedOracleStructuralGateBudget_envelope
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound clauseCount : ℕ)
    (hclauses : ∀ randomness : BitInput (pcp.nativeWidth n),
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    boundedOracleStructuralGateBudget pcp input bound ≤
      structuralGateEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n)
        clauseCount :=
  boundedOracleStructuralGateBudget_le pcp input bound _
    (fun count => fixedCountNodeCount_envelope pcp input count clauseCount
      hclauses)

/-- The formula-atom schedule's length, enveloped. -/
theorem boundedOracleStructuralFormulaAtoms_length_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound clauseCount : ℕ)
    (hclauses : ∀ randomness : BitInput (pcp.nativeWidth n),
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    (boundedOracleStructuralFormulaAtoms pcp input bound).length ≤
      descriptionWidth (pcp.nativeWidth n) bound +
        structuralGateEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n)
          clauseCount + 1 := by
  have hgate :=
    boundedOracleStructuralGateBudget_envelope pcp input bound clauseCount
      hclauses
  rw [boundedOracleStructuralFormulaAtoms_length]
  omega

/-! ## §6 The register width of one formula atom -/

theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_mono_right hle)

theorem one_le_natBitLength (value : ℕ) : 1 ≤ natBitLength value := by
  unfold natBitLength
  omega

/-- The register unit every atom of a circuit's formula schedule is measured
in: the width of the largest address the schedule can name. -/
def widthUnit (inputArity limit : ℕ) : ℕ :=
  natBitLength (inputArity + limit + 4)

theorem three_le_widthUnit (inputArity limit : ℕ) :
    3 ≤ widthUnit inputArity limit := by
  have hmono : natBitLength 4 ≤ widthUnit inputArity limit :=
    natBitLength_mono (by omega)
  have hfour : natBitLength 4 = 3 := by decide
  omega

theorem natBitLength_le_widthUnit {inputArity limit value : ℕ}
    (hvalue : value ≤ inputArity + limit + 4) :
    natBitLength value ≤ widthUnit inputArity limit :=
  natBitLength_mono hvalue

theorem wellFormedAt_mono {n : ℕ} {node : BooleanNode n} {small large : ℕ}
    (h : node.WellFormedAt small) (hle : small ≤ large) :
    node.WellFormedAt large := by
  cases node with
  | const _ => trivial
  | input _ => trivial
  | not child => exact lt_of_lt_of_le h hle
  | and left right =>
      exact ⟨lt_of_lt_of_le h.1 hle, lt_of_lt_of_le h.2 hle⟩
  | or left right =>
      exact ⟨lt_of_lt_of_le h.1 hle, lt_of_lt_of_le h.2 hle⟩

theorem rawCircuitNodeCode_bits_le {n : ℕ} (node : BooleanNode n) (limit : ℕ)
    (hwf : node.WellFormedAt limit) :
    natBitLength (rawCircuitNodeCode node) ≤ 4 * widthUnit n limit := by
  have hthree := three_le_widthUnit n limit
  cases node with
  | const value =>
      have hpair := pairCodeBits_le 0 value.toNat
      have hzero : natBitLength 0 = 1 := by decide
      have htoNat : natBitLength value.toNat ≤ 1 := by
        cases value <;> decide
      simp only [rawCircuitNodeCode]
      omega
  | input source =>
      have hpair := pairCodeBits_le 1 source.val
      have hone : natBitLength 1 = 1 := by decide
      have hsource : natBitLength source.val ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by have := source.isLt; omega)
      simp only [rawCircuitNodeCode]
      omega
  | not child =>
      have hchild : child < limit := hwf
      have hpair := pairCodeBits_le 2 (n + child)
      have htwo : natBitLength 2 = 2 := by decide
      have hvalue : natBitLength (n + child) ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by omega)
      simp only [rawCircuitNodeCode]
      omega
  | and left right =>
      have hleft : left < limit := hwf.1
      have hright : right < limit := hwf.2
      have hinner := pairCodeBits_le (n + left) (n + right)
      have hleftBits : natBitLength (n + left) ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by omega)
      have hrightBits : natBitLength (n + right) ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by omega)
      have hpair := pairCodeBits_le 3 (Nat.pair (n + left) (n + right))
      have hthreeBits : natBitLength 3 = 2 := by decide
      simp only [rawCircuitNodeCode]
      omega
  | or left right =>
      have hleft : left < limit := hwf.1
      have hright : right < limit := hwf.2
      have hinner := pairCodeBits_le (n + left) (n + right)
      have hleftBits : natBitLength (n + left) ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by omega)
      have hrightBits : natBitLength (n + right) ≤ widthUnit n limit :=
        natBitLength_le_widthUnit (by omega)
      have hpair := pairCodeBits_le 4 (Nat.pair (n + left) (n + right))
      have hfourBits : natBitLength 4 = 3 := by decide
      simp only [rawCircuitNodeCode]
      omega

theorem nodeAtom_bits_le {n : ℕ} (index : ℕ) (node : BooleanNode n)
    (limit : ℕ) (hindex : index ≤ limit) (hwf : node.WellFormedAt limit) :
    natBitLength (circuitInputFormulaClauseNodeAtom index node) ≤
      32 * widthUnit n limit := by
  have hthree := three_le_widthUnit n limit
  have hcode := rawCircuitNodeCode_bits_le node limit hwf
  have hgate : natBitLength (n + index) ≤ widthUnit n limit :=
    natBitLength_le_widthUnit (by omega)
  have hrequest :=
    pairCodeBits_le (circuitInputGateVariable n index) (rawCircuitNodeCode node)
  have hgate' : circuitInputGateVariable n index = n + index := rfl
  rw [hgate'] at hrequest
  have htagged :=
    pairCodeBits_le 1 (circuitInputClauseRequest index node)
  have hone : natBitLength 1 = 1 := by decide
  have houter :=
    pairCodeBits_le n (Nat.pair 1 (circuitInputClauseRequest index node))
  have hn : natBitLength n ≤ widthUnit n limit :=
    natBitLength_le_widthUnit (by omega)
  have hrequestUnfold :
      circuitInputClauseRequest index node =
        Nat.pair (n + index) (rawCircuitNodeCode node) := rfl
  rw [hrequestUnfold] at htagged houter
  simp only [circuitInputFormulaClauseNodeAtom, hrequestUnfold]
  omega

theorem tautologyAtom_bits_le (inputArity index limit : ℕ)
    (hindex : index ≤ limit) (harity : inputArity ≤ limit) :
    natBitLength
        (circuitInputFormulaClauseTautologyAtom inputArity index) ≤
      32 * widthUnit inputArity limit := by
  have hthree := three_le_widthUnit inputArity limit
  have hinner := pairCodeBits_le 0 index
  have hzero : natBitLength 0 = 1 := by decide
  have hindexBits : natBitLength index ≤ widthUnit inputArity limit :=
    natBitLength_le_widthUnit (by omega)
  have houter := pairCodeBits_le inputArity (Nat.pair 0 index)
  have harityBits : natBitLength inputArity ≤ widthUnit inputArity limit :=
    natBitLength_le_widthUnit (by omega)
  simp only [circuitInputFormulaClauseTautologyAtom]
  omega

theorem nodeAtomsFrom_bits_le {n : ℕ} (limit : ℕ) :
    ∀ (nodes : List (BooleanNode n)) (start : ℕ),
      start + nodes.length ≤ limit →
      (∀ node ∈ nodes, node.WellFormedAt limit) →
      ∀ value ∈ circuitInputFormulaNodeAtomsFrom start nodes,
        natBitLength value ≤ 32 * widthUnit n limit := by
  intro nodes
  induction nodes with
  | nil =>
      intro start _ _ value hvalue
      simp [circuitInputFormulaNodeAtomsFrom] at hvalue
  | cons node rest ih =>
      intro start hstart hwf value hvalue
      simp only [circuitInputFormulaNodeAtomsFrom, List.mem_cons] at hvalue
      rcases hvalue with rfl | htail
      · refine nodeAtom_bits_le start node limit (by simp at hstart; omega) ?_
        exact hwf node (by simp)
      · refine ih (start + 1) (by simp at hstart; omega) ?_ value htail
        intro item hitem
        exact hwf item (by simp [hitem])

theorem circuitInputFormulaAtoms_bits_le {n : ℕ} (circuit : BooleanCircuit n) :
    ∀ value ∈ circuitInputFormulaAtoms circuit,
      natBitLength value ≤ 32 * widthUnit n (n + circuit.size) := by
  have hnodesWellFormed :
      ∀ node ∈ circuit.nodes, node.WellFormedAt (n + circuit.size) := by
    intro node hnode
    obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hnode
    have hwf := circuit.wellFormed ⟨index, hindex⟩
    rw [List.get_eq_getElem] at hwf
    exact wellFormedAt_mono hwf (by
      have : index < circuit.nodes.length := hindex
      simp only [BooleanCircuit.size]
      omega)
  intro value hvalue
  simp only [circuitInputFormulaAtoms, List.mem_append, List.mem_singleton]
    at hvalue
  rcases hvalue with (htautology | hnode) | hfinal
  · obtain ⟨index, hindexMem, rfl⟩ := List.mem_map.mp htautology
    have hindex : index < n := List.mem_range.mp hindexMem
    exact tautologyAtom_bits_le n index (n + circuit.size) (by omega) (by omega)
  · refine nodeAtomsFrom_bits_le (n + circuit.size) circuit.nodes 0 ?_
      hnodesWellFormed value hnode
    simp only [BooleanCircuit.size] at *
    omega
  · subst hfinal
    refine nodeAtom_bits_le circuit.output.val _ (n + circuit.size) ?_ trivial
    have := circuit.output.isLt
    simp only [BooleanCircuit.size]
    omega

/-! ## §7 The balanced atom code's width -/

theorem widthUnit_mono {arity small large : ℕ} (hle : small ≤ large) :
    widthUnit arity small ≤ widthUnit arity large :=
  natBitLength_mono (by omega)

theorem natBitLength_encodeBalancedList_structuralFormulaAtoms_le
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound clauseCount : ℕ)
    (hclauses : ∀ randomness : BitInput (pcp.nativeWidth n),
      (pcp.decision input randomness).clauses.length ≤ clauseCount) :
    natBitLength
        (encodeBalancedList
          (boundedOracleStructuralFormulaAtoms pcp input bound)) ≤
      16 *
          (descriptionWidth (pcp.nativeWidth n) bound +
            structuralGateEnvelope (pcp.nativeWidth n) bound
              (pcp.queryCount n) clauseCount + 1 + 1) ^ 2 *
        (32 *
          widthUnit (descriptionWidth (pcp.nativeWidth n) bound)
            (descriptionWidth (pcp.nativeWidth n) bound +
              structuralGateEnvelope (pcp.nativeWidth n) bound
                (pcp.queryCount n) clauseCount)) := by
  have hcircuit := boundedOracleStructuralFormulaAtoms_eq pcp input bound
  have hsizeEq :
      (boundedOracleVerifierCircuit pcp input bound).size =
        boundedOracleStructuralGateBudget pcp input bound :=
    boundedOracleVerifierCircuit_size pcp input bound
  have hgate :=
    boundedOracleStructuralGateBudget_envelope pcp input bound clauseCount
      hclauses
  have hlen :=
    boundedOracleStructuralFormulaAtoms_length_le pcp input bound clauseCount
      hclauses
  have hwidth :
      ∀ value ∈ boundedOracleStructuralFormulaAtoms pcp input bound,
        natBitLength value ≤
          32 *
            widthUnit (descriptionWidth (pcp.nativeWidth n) bound)
              (descriptionWidth (pcp.nativeWidth n) bound +
                structuralGateEnvelope (pcp.nativeWidth n) bound
                  (pcp.queryCount n) clauseCount) := by
    intro value hvalue
    rw [hcircuit] at hvalue
    refine (circuitInputFormulaAtoms_bits_le
      (boundedOracleVerifierCircuit pcp input bound) value hvalue).trans ?_
    exact Nat.mul_le_mul_left 32 (widthUnit_mono (by omega))
  have hunit :=
    three_le_widthUnit (descriptionWidth (pcp.nativeWidth n) bound)
      (descriptionWidth (pcp.nativeWidth n) bound +
        structuralGateEnvelope (pcp.nativeWidth n) bound (pcp.queryCount n)
          clauseCount)
  have hquad :=
    natBitLength_encodeBalancedList_le_quadratic
      (boundedOracleStructuralFormulaAtoms pcp input bound)
      (32 *
        widthUnit (descriptionWidth (pcp.nativeWidth n) bound)
          (descriptionWidth (pcp.nativeWidth n) bound +
            structuralGateEnvelope (pcp.nativeWidth n) bound
              (pcp.queryCount n) clauseCount))
      (by omega) hwidth
  exact hquad.trans
    (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by omega) 2)))

end NearCubicWires.R1Leaf56StructuralGateBudgetEnvelope
