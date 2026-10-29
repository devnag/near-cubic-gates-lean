import SourceAdapters.Proximity.HonestBlocks
import SourceAdapters.Proximity.TargetLengths

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": an explicit finite honest auxiliary assignment. The search
has exactly 2^(q + predicateNodeBound q + 1) candidates, independent of the
source circuit size. This supplies a computable output specification, not an
ordinary-machine realization or a bit-time clock.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
open NearCubicGates.Published.CW19Proximity

def blockVariableBound (q : ℕ) : ℕ := q + predicateNodeBound q + 1

theorem predicateBlock_indices {q : ℕ} (predicate : BitInput q → Bool)
    (clause : EncodedClause) (hc : clause ∈ predicateBlock predicate)
    (literal : EncodedLiteral) (hl : literal ∈ clause) : literal.2 < blockVariableBound q := by
  obtain hc | hc := List.mem_append.mp hc
  · have ha := List.all_eq_true.mp (circuitInputFormula_indices_lt (predicateCircuit predicate)) clause hc
    have hb := List.all_eq_true.mp ha literal hl
    have hs := predicateCircuit_size predicate
    simp only [decide_eq_true_eq] at hb
    change literal.2 < q + predicateNodeBound q + 1
    change literal.2 < q + (predicateCircuit predicate).size at hb
    change (predicateCircuit predicate).size ≤ predicateNodeBound q at hs
    omega
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hc
    have hs := predicateCircuit_size predicate
    simp only [circuitInputTautology, triple, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;>
      simp only [positive, negative, blockVariableBound] <;>
      change q + (predicateCircuit predicate).size < q + predicateNodeBound q + 1 <;>
      change (predicateCircuit predicate).size ≤ predicateNodeBound q at hs <;> omega

theorem formulaEval_agree (formula : EncodedCNF) (left right : ℕ → Bool)
    (h : ∀ clause ∈ formula, ∀ literal ∈ clause, left literal.2 = right literal.2) :
    formulaEval left formula = formulaEval right formula := by
  have hclause (clause : EncodedClause)
      (hl : ∀ literal ∈ clause, left literal.2 = right literal.2) :
      clauseEval left clause = clauseEval right clause := by
    induction clause with
    | nil => rfl
    | cons literal rest ih =>
      have hhead := hl literal (by simp)
      have htail := ih (fun item hi => hl item (by simp [hi]))
      simp only [clauseEval, List.any_cons] at htail ⊢
      simp only [literalEval, hhead, htail]
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
    have hhead := hclause clause (h clause (by simp))
    have htail := ih (fun item hi => h item (by simp [hi]))
    simp only [formulaEval, List.all_cons] at htail ⊢
    rw [hhead, htail]

def blockCandidateGood {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q)
    (candidate : BitInput (blockVariableBound q)) : Bool :=
  decide (recoveredCircuitInput (finiteProofOracle candidate) = input) &&
    formulaEval (finiteProofOracle candidate) (predicateBlock predicate)

/-- The first satisfying bounded assignment, defaulting to zero on rejecting rows. -/
def canonicalBlockAssignment {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q) : ℕ → Bool :=
  finiteProofOracle (((QueryFormula.assignments (blockVariableBound q)).find?
    (blockCandidateGood predicate input)).getD (fun _ => false))

theorem canonicalBlockAssignment_spec {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q)
    (haccept : predicate input = true) :
    recoveredCircuitInput (canonicalBlockAssignment predicate input) = input ∧
      formulaEval (canonicalBlockAssignment predicate input) (predicateBlock predicate) = true := by
  obtain ⟨assignment, hinput, hformula⟩ := (predicateBlock_iff predicate input).mp haccept
  let candidate : BitInput (blockVariableBound q) := fun i => assignment i.val
  have hagree (address : ℕ) (haddress : address < blockVariableBound q) :
      finiteProofOracle candidate address = assignment address := by
    simp [finiteProofOracle, haddress, candidate]
  have hcandidateInput : recoveredCircuitInput (finiteProofOracle candidate) = input := by
    rw [← hinput]
    funext i
    exact hagree i.val (by have hi := i.isLt; unfold blockVariableBound; omega)
  have hcandidateFormula : formulaEval (finiteProofOracle candidate) (predicateBlock predicate) = true := by
    rw [formulaEval_agree _ _ assignment]
    · exact hformula
    · intro clause hc literal hl
      exact hagree literal.2 (predicateBlock_indices predicate clause hc literal hl)
  have hgood : blockCandidateGood predicate input candidate = true := by
    simp [blockCandidateGood, hcandidateInput, hcandidateFormula]
  have hmem := QueryFormula.mem_assignments candidate
  unfold canonicalBlockAssignment
  cases hf : (QueryFormula.assignments (blockVariableBound q)).find?
      (blockCandidateGood predicate input) with
  | none =>
    have hn := List.find?_eq_none.mp hf candidate hmem
    exact False.elim (hn hgood)
  | some selected =>
    have hs := List.find?_some hf
    simpa only [blockCandidateGood, Bool.and_eq_true, decide_eq_true_eq, Option.getD_some] using hs

theorem canonicalBlockAssignment_candidate_count (q : ℕ) :
    (QueryFormula.assignments (blockVariableBound q)).length = 2 ^ (q + predicateNodeBound q + 1) := by
  simp [QueryFormula.assignments, blockVariableBound]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": canonical row auxiliaries interleave with the old proof. -/
def canonicalClauseProof {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : ℕ → Bool :=
  combineProof proof (fun row index =>
    if h : row < 2 ^ V.randomBits then
      canonicalBlockAssignment (rowPredicate V ⟨row, h⟩)
        (fun j => oracleValue input proof ((padQueries V).query ⟨row, h⟩ j)) (q + index)
    else false)

theorem canonicalClauseProof_complete {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool)
    (honest : ∀ coins, V.accepts input proof coins = true) :
    ∀ coins, (clauseVerifier V).accepts input (canonicalClauseProof V input proof) coins = true := by
  let answers (coins : Fin (2 ^ V.randomBits)) : BitInput q :=
    fun j => oracleValue input proof ((padQueries V).query coins j)
  have hrows (coins : Fin (2 ^ V.randomBits)) :=
    canonicalBlockAssignment_spec (rowPredicate V coins) (answers coins)
      (by change (padQueries V).accepts input proof coins = true
          rw [padQueries_accepts]; exact honest coins)
  have hold : originalProof (canonicalClauseProof V input proof) = proof := by
    funext address
    simp only [originalProof, canonicalClauseProof, combineProof_even]
  have hlocal (coins : Fin (2 ^ V.randomBits)) :
      localAssignment V input (canonicalClauseProof V input proof) coins =
        canonicalBlockAssignment (rowPredicate V coins) (answers coins) := by
    funext address
    by_cases ha : address < q
    · simp only [localAssignment, localAddress, dif_pos ha, renamed_oracle, hold]
      exact (congrFun (hrows coins).1 ⟨address, ha⟩).symm
    · have hsum : q + (address - q) = address := by omega
      simp [localAssignment, localAddress, ha, oracleValue, canonicalClauseProof,
        combineProof_odd, coins.isLt, hsum, answers]
  intro coins
  let pair := splitBinaryCoins V.randomBits (predicateBlockBits q) coins
  have hcoins : (splitBinaryCoins V.randomBits (predicateBlockBits q)).symm pair = coins :=
    Equiv.symm_apply_apply _ _
  rw [← hcoins, clauseVerifier_accepts, hlocal]
  exact List.all_eq_true.mp (hrows pair.1).2 _ (List.get_mem _ _)

open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

/-- The accepted input has the same bits and evaluation in the flat source model. -/
def sourceAcceptedInput (p : AcceptedCircuitInput) : AcceptedSourceInput :=
  ⟨sourceCircuit p.1, ⟨p.2.val, p.2.property⟩⟩

def trimmedCanonicalProof {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : BitInput (trimVerifier (clauseVerifier V)).proofBits :=
  restrictProof (clauseVerifier V) (canonicalClauseProof V input proof)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": exact honest output function with bounded finite auxiliaries. -/
def convertedHonest {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ)
    (sourceHonest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (p : AcceptedCircuitInput) : BitInput (convertedVerifier V p.1).proofBits :=
  trimmedCanonicalProof (V (sourceCircuit p.1)) p.2.val
    (finiteProofOracle (sourceHonest (sourceAcceptedInput p)))

theorem convertedHonest_complete {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ)
    (sourceHonest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (hcomplete : ∀ p coins, (V p.1).accepts p.2.val
      (finiteProofOracle (sourceHonest p)) coins = true) :
    ∀ (p : AcceptedCircuitInput) coins, (convertedVerifier V p.1).accepts p.2.val
      (convertedHonest V proofLength sourceHonest p) coins = true := by
  intro p coins
  exact trim_perfect_completeness _ _ _
    (canonicalClauseProof_complete _ _ _ (hcomplete (sourceAcceptedInput p))) coins

/-- Output length only: Q04 still requires the actual ordinary writer. -/
theorem convertedHonest_word_input_bound {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ)
    (sourceHonest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) :
    ∃ K e : ℕ, ∀ p : AcceptedCircuitInput,
      (List.ofFn (convertedHonest V proofLength sourceHonest p)).length ≤
        K * ((acceptedCircuitInputWord p).length + 1) ^ e := by
  refine ⟨3 * (28 ^ a * predicateBlockSize q) * 2 ^ (2 * a), 2 * a, fun p => ?_⟩
  have hsize := (convertedVerifier_size V a hr p.1).1
  have hinput : p.1.word.length ≤ (acceptedCircuitInputWord p).length := by
    simp [acceptedCircuitInputWord]
  have hnodes := (target_nodes_le_word p.1).trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hinput 1))
  simp only [List.length_ofFn]
  calc
    (convertedVerifier V p.1).proofBits ≤
        (3 * (28 ^ a * predicateBlockSize q)) * (p.1.m + 1) ^ (2 * a) := hsize
    _ ≤ (3 * (28 ^ a * predicateBlockSize q)) *
        (2 * ((acceptedCircuitInputWord p).length + 1)) ^ (2 * a) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnodes _)
    _ = _ := by rw [mul_pow]; ring

end NearCubicGates.Adapters.Proximity
