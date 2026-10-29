import SourceAdapters.Proximity.VerifierModel
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
Q03, `app:sources`, "Uniform three-query PCPP and code interfaces". The source proof is an oracle on natural addresses.
Only its queried coordinates are retained, ordered by their natural addresses.
Restriction and extension preserve every coin outcome. No efficient evaluator
for an arbitrary source proof is assumed.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP
open scoped BigOperators

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a query contributes one proof address or none. -/
def proofAddressSet {n : ℕ} (query : SignedQuery n) : Finset ℕ :=
  match query.address with
  | .inl _ => ∅
  | .inr address => {address}

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": enumerate all coins and all three positions, then deduplicate. -/
def usedProofAddresses {n : ℕ} (V : ThreeQueryVerifier n) : Finset ℕ :=
  Finset.univ.biUnion fun coins =>
    Finset.univ.biUnion fun j => proofAddressSet (V.clause coins j)

theorem queried_proof_mem {n : ℕ} (V : ThreeQueryVerifier n)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) (address : ℕ)
    (h : (V.clause coins j).address = .inr address) :
    address ∈ usedProofAddresses V := by
  apply Finset.mem_biUnion.mpr
  refine ⟨coins, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  exact ⟨j, Finset.mem_univ _, by simp [proofAddressSet, h]⟩

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": duplicates and input-only clauses can only reduce this bound. -/
theorem usedProofAddresses_card_le {n : ℕ} (V : ThreeQueryVerifier n) :
    (usedProofAddresses V).card ≤ 3 * 2 ^ V.randomBits := by
  have hsingle (query : SignedQuery n) : (proofAddressSet query).card ≤ 1 := by
    cases h : query.address <;> simp [proofAddressSet, h]
  calc
    (usedProofAddresses V).card ≤
        ∑ coins : Fin (2 ^ V.randomBits),
          (Finset.univ.biUnion fun j => proofAddressSet (V.clause coins j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _coins : Fin (2 ^ V.randomBits), ∑ _j : Fin 3, 1 := by
      apply Finset.sum_le_sum
      intro coins _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => hsingle _)
    _ = 3 * 2 ^ V.randomBits := by simp [Nat.mul_comm]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the dense proof numbering follows increasing source addresses. -/
def denseAddress {n : ℕ} (V : ThreeQueryVerifier n)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    Fin (n + (usedProofAddresses V).card) :=
  match h : (V.clause coins j).address with
  | .inl i => Fin.castAdd _ i
  | .inr address => Fin.natAdd n
      (((usedProofAddresses V).orderIsoOfFin rfl).symm
        ⟨address, queried_proof_mem V coins j address h⟩)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": restrict the oracle at the enumerated distinct addresses. -/
def restrictProof {n : ℕ} (V : ThreeQueryVerifier n) (proof : ℕ → Bool) :
    BitInput (usedProofAddresses V).card :=
  fun i => proof (((usedProofAddresses V).orderIsoOfFin rfl) i).val

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": extend every trimmed proof; unused positions receive `false`. -/
def extendProof {n : ℕ} (V : ThreeQueryVerifier n)
    (proof : BitInput (usedProofAddresses V).card) : ℕ → Bool :=
  fun address => if h : address ∈ usedProofAddresses V then
    proof (((usedProofAddresses V).orderIsoOfFin rfl).symm ⟨address, h⟩)
  else false

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": extension is defined even for an empty retained address set. -/
theorem restrict_extend {n : ℕ} (V : ThreeQueryVerifier n)
    (proof : BitInput (usedProofAddresses V).card) :
    restrictProof V (extendProof V proof) = proof := by
  funext i
  dsimp only [restrictProof, extendProof]
  rw [dif_pos (((usedProofAddresses V).orderIsoOfFin rfl) i).property]
  change proof (((usedProofAddresses V).orderIsoOfFin rfl).symm
    (((usedProofAddresses V).orderIsoOfFin rfl) i)) = proof i
  rw [OrderIso.symm_apply_apply]

theorem denseAddress_restrict {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    Fin.addCases input (restrictProof V proof) (denseAddress V coins j) =
      oracleValue input proof (V.clause coins j).address := by
  unfold denseAddress
  split
  next i h => simp [oracleValue, h]
  next address h =>
    simp only [Fin.addCases_right, restrictProof, OrderIso.apply_symm_apply]
    simp [oracleValue, h]

theorem denseAddress_extend {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : BitInput (usedProofAddresses V).card)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    Fin.addCases input proof (denseAddress V coins j) =
      oracleValue input (extendProof V proof) (V.clause coins j).address := by
  unfold denseAddress
  split
  next i h => simp [oracleValue, h]
  next address h =>
    simp [h, oracleValue, extendProof, queried_proof_mem V coins j address h]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the target three-literal object after dense relabeling. -/
def trimVerifier {n : ℕ} (V : ThreeQueryVerifier n) : RawThreeQueryPCPP n where
  proofBits := (usedProofAddresses V).card
  randomBits := V.randomBits
  clause := fun coins j => if (V.clause coins j).negated then
    .negative (denseAddress V coins j) else .positive (denseAddress V coins j)

theorem trimmed_literal_restrict {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    ((trimVerifier V).clause coins j).eval (Fin.addCases input (restrictProof V proof)) =
      (V.clause coins j).eval input proof := by
  simp only [trimVerifier, SignedQuery.eval]
  split <;> simp [Literal.eval, denseAddress_restrict]

theorem trimmed_literal_extend {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : BitInput (usedProofAddresses V).card)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    ((trimVerifier V).clause coins j).eval (Fin.addCases input proof) =
      (V.clause coins j).eval input (extendProof V proof) := by
  simp only [trimVerifier, SignedQuery.eval]
  split <;> simp [Literal.eval, denseAddress_extend]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": restriction preserves each verifier outcome. -/
theorem trim_accepts_restrict {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) :
    (trimVerifier V).accepts input (restrictProof V proof) coins =
      V.accepts input proof coins := by
  simp only [RawThreeQueryPCPP.accepts, ThreeQueryVerifier.accepts, trimmed_literal_restrict]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": arbitrary trimmed proofs extend with the same outcome. -/
theorem trim_accepts_extend {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : BitInput (usedProofAddresses V).card)
    (coins : Fin (2 ^ V.randomBits)) :
    (trimVerifier V).accepts input proof coins =
      V.accepts input (extendProof V proof) coins := by
  simp only [RawThreeQueryPCPP.accepts, ThreeQueryVerifier.accepts, trimmed_literal_extend]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": exact probabilities are unchanged by restriction. -/
theorem trim_fraction_restrict {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool) :
    (trimVerifier V).fraction input (restrictProof V proof) = V.fraction input proof := by
  simp only [RawThreeQueryPCPP.fraction, ThreeQueryVerifier.fraction, trim_accepts_restrict]
  rfl

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": exact probabilities are unchanged for every extended proof. -/
theorem trim_fraction_extend {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : BitInput (usedProofAddresses V).card) :
    (trimVerifier V).fraction input proof = V.fraction input (extendProof V proof) := by
  simp only [RawThreeQueryPCPP.fraction, ThreeQueryVerifier.fraction, trim_accepts_extend]
  rfl

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": perfect completeness survives restriction of its honest oracle. -/
theorem trim_perfect_completeness {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool)
    (h : ∀ coins, V.accepts input proof coins = true) :
    ∀ coins, (trimVerifier V).accepts input (restrictProof V proof) coins = true := by
  intro coins
  rw [trim_accepts_restrict]
  exact h coins

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": source soundness applies to the extension of each trimmed proof. -/
theorem trim_soundness {n : ℕ} (V : ThreeQueryVerifier n) (input : BitInput n)
    (s : ℝ) (h : ∀ proof : ℕ → Bool, V.fraction input proof ≤ s) :
    ∀ proof : BitInput (trimVerifier V).proofBits,
      (trimVerifier V).fraction input proof ≤ s := by
  intro proof
  rw [trim_fraction_extend]
  exact h _

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a common polynomial bounds proofs and coins. -/
theorem trim_size_bounds {n m K e : ℕ} (V : ThreeQueryVerifier n)
    (h : 2 ^ V.randomBits ≤ K * (m + 1) ^ e) :
    (trimVerifier V).proofBits ≤ (3 * K) * (m + 1) ^ e ∧
      2 ^ (trimVerifier V).randomBits ≤ (3 * K) * (m + 1) ^ e := by
  constructor
  · exact (usedProofAddresses_card_le V).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 3 h)
  · change 2 ^ V.randomBits ≤ _
    exact h.trans (Nat.mul_le_mul_right _ (by omega))

end NearCubicGates.Adapters.Proximity
