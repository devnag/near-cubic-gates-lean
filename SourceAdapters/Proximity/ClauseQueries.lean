import SourceAdapters.Proximity.VerifierModel
import SourceAdapters.Proximity.OracleDomain
import SourceAdapters.Proximity.UniformBlocks
import SourceAdapters.Proximity.BlockSoundness
import Mathlib.Data.Nat.Pairing

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces": assemble exact-three-query clauses from the uniform
blocks. Original proof coordinates occupy even natural addresses; auxiliary
coordinates occupy odd addresses indexed by (old coins, local variable).
This avoids assuming an efficiently computable source proof-length bound.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
open NearCubicGates.Published.CW19Proximity

def blockClause {q : ℕ} (predicate : BitInput q → Bool) (j : Fin (predicateBlockSize q)) :
    EncodedClause :=
  (predicateBlock predicate).get ⟨j.val, by rw [predicateBlock_length]; exact j.isLt⟩

theorem blockClause_length {q : ℕ} (predicate : BitInput q → Bool)
    (j : Fin (predicateBlockSize q)) : (blockClause predicate j).length = 3 :=
  predicateBlock_three predicate _ (List.get_mem _ _)

def blockLiteral {q : ℕ} (predicate : BitInput q → Bool)
    (j : Fin (predicateBlockSize q)) (k : Fin 3) : EncodedLiteral :=
  (blockClause predicate j).get ⟨k.val, by rw [blockClause_length]; exact k.isLt⟩

theorem blockLiteral_list {q : ℕ} (predicate : BitInput q → Bool)
    (j : Fin (predicateBlockSize q)) : List.ofFn (blockLiteral predicate j) = blockClause predicate j := by
  apply List.ext_getElem
  · simp [blockClause_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, blockLiteral, List.get_eq_getElem]

def rowPredicate {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) : BitInput q → Bool :=
  (padQueries V).decision coins

def originalProof (proof : ℕ → Bool) : ℕ → Bool := fun address => proof (2 * address)

def renamedAddress {n : ℕ} : QueryAddress n → QueryAddress n
  | .inl i => .inl i
  | .inr address => .inr (2 * address)

def localAddress {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (localIndex : ℕ) : QueryAddress n :=
  if h : localIndex < q then renamedAddress ((padQueries V).query coins ⟨localIndex, h⟩)
  else .inr (2 * Nat.pair coins.val (localIndex - q) + 1)

def localAssignment {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : ℕ → Bool :=
  fun localIndex => oracleValue input proof (localAddress V coins localIndex)

def rowAnswers {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : BitInput q :=
  fun j => oracleValue input (originalProof proof) ((padQueries V).query coins j)

theorem renamed_oracle {n : ℕ} (input : BitInput n) (proof : ℕ → Bool) (address : QueryAddress n) :
    oracleValue input proof (renamedAddress address) = oracleValue input (originalProof proof) address := by
  cases address <;> rfl

theorem localAssignment_input {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) :
    recoveredCircuitInput (localAssignment V input proof coins) = rowAnswers V input proof coins := by
  funext j
  simp [recoveredCircuitInput, localAssignment, localAddress, j.isLt, rowAnswers, renamed_oracle]

theorem rowPredicate_value {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) :
    rowPredicate V coins (rowAnswers V input proof coins) =
      V.accepts input (originalProof proof) coins :=
  padQueries_accepts V input (originalProof proof) coins

def translatedLiteral {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (literal : EncodedLiteral) : SignedQuery n :=
  ⟨localAddress V coins literal.2, !literal.1⟩

theorem translatedLiteral_eval {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits))
    (literal : EncodedLiteral) :
    (translatedLiteral V coins literal).eval input proof =
      literalEval (localAssignment V input proof coins) literal := by
  cases h : literal.1 <;> simp [translatedLiteral, SignedQuery.eval, literalEval, localAssignment, h]

def clauseVerifier {n q : ℕ} (V : NonadaptiveVerifier n q) : ThreeQueryVerifier n where
  randomBits := V.randomBits + predicateBlockBits q
  clause := fun coins k =>
    let pair := splitBinaryCoins V.randomBits (predicateBlockBits q) coins
    translatedLiteral V pair.1 (blockLiteral (rowPredicate V pair.1) pair.2 k)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a binary coin selects precisely one padded three-literal clause. -/
theorem clauseVerifier_accepts {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin (predicateBlockSize q)) :
    (clauseVerifier V).accepts input proof
        ((splitBinaryCoins V.randomBits (predicateBlockBits q)).symm (coins, j)) =
      clauseEval (localAssignment V input proof coins) (blockClause (rowPredicate V coins) j) := by
  simp only [ThreeQueryVerifier.accepts, clauseVerifier, Equiv.apply_symm_apply,
    translatedLiteral_eval]
  change (List.ofFn ((literalEval (localAssignment V input proof coins)) ∘
    blockLiteral (rowPredicate V coins) j)).any id = _
  rw [← List.map_ofFn, blockLiteral_list]
  simp only [clauseEval, List.any_map, Function.id_comp]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": every rejected original row has a rejected selected clause. -/
theorem clauseVerifier_rejects {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits))
    (h : V.accepts input (originalProof proof) coins = false) :
    ∃ j : Fin (predicateBlockSize q),
      (clauseVerifier V).accepts input proof
        ((splitBinaryCoins V.randomBits (predicateBlockBits q)).symm (coins, j)) = false := by
  obtain ⟨clause, hmem, hfalse⟩ := predicateBlock_rejects (rowPredicate V coins)
    (rowAnswers V input proof coins) (by rw [rowPredicate_value]; exact h)
    (localAssignment V input proof coins) (localAssignment_input V input proof coins)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
  let j : Fin (predicateBlockSize q) := ⟨i.val, by rw [← predicateBlock_length (rowPredicate V coins)]; exact i.isLt⟩
  refine ⟨j, ?_⟩
  rw [clauseVerifier_accepts]
  exact hfalse

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the assembled verifier has the exact constant rejection loss. -/
theorem clauseVerifier_soundness {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (s : ℝ) (hsound : ∀ proof : ℕ → Bool, V.fraction input proof ≤ s) :
    ∀ proof : ℕ → Bool, (clauseVerifier V).fraction input proof ≤
      1 - (1 - s) / predicateBlockSize q := by
  classical
  intro proof
  let e := splitBinaryCoins V.randomBits (predicateBlockBits q)
  let fresh : Fin (2 ^ V.randomBits) × Fin (predicateBlockSize q) → Bool :=
    fun pair => (clauseVerifier V).accepts input proof (e.symm pair)
  have hg := block_soundness (by positivity : 0 < 2 ^ V.randomBits)
    (by unfold predicateBlockSize; positivity)
    (fun coins => V.accepts input (originalProof proof) coins) fresh
    (clauseVerifier_rejects V input proof) s
    (by simpa only [NonadaptiveVerifier.fraction, Nat.cast_pow, Nat.cast_ofNat]
      using hsound (originalProof proof))
  have hc : (Finset.univ.filter fun coins => (clauseVerifier V).accepts input proof coins = true).card =
      (Finset.univ.filter fun pair => fresh pair = true).card := by
    apply Finset.card_equiv e
    intro coins
    constructor
    · intro h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [fresh]
      rw [Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp h).2
    · intro h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have htrue := (Finset.mem_filter.mp h).2
      dsimp only [fresh] at htrue
      rwa [Equiv.symm_apply_apply] at htrue
  unfold ThreeQueryVerifier.fraction
  rw [hc]
  simpa only [clauseVerifier, predicateBlockSize, pow_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using hg

end NearCubicGates.Adapters.Proximity
