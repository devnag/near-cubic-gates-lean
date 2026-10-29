import NineInputs
import Mathlib.Tactic

/-!
Q02–Q03, `app:sources`, "Uniform three-query PCPP and code interfaces". Source proofs have a finite domain, while the clause
construction and trimming use natural proof addresses. Query bounds prove
that restriction to the source domain changes no outcome. Padding an at-most-q
verifier to a fixed q is explicit; added dummy queries are ignored by decision.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicGates.Published.CW19Proximity

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a query-count upper bound becomes an exact count by ignored padding. -/
def padQueries {n q : ℕ} (V : NonadaptiveVerifier n q) : NonadaptiveVerifier n q where
  randomBits := V.randomBits
  queryCount := fun _ => q
  queryCount_le := fun _ => le_rfl
  query := fun coins j =>
    if h : j.val < V.queryCount coins then V.query coins ⟨j.val, h⟩ else .inr 0
  decision := fun coins answers =>
    V.decision coins (fun j => answers (Fin.castLE (V.queryCount_le coins) j))

theorem padQueries_accepts {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) :
    (padQueries V).accepts input proof coins = V.accepts input proof coins := by
  unfold NonadaptiveVerifier.accepts
  dsimp only [padQueries]
  congr 1
  funext j
  simp only [Fin.val_castLE, j.isLt, ↓reduceDIte]

theorem padQueries_fraction {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) :
    (padQueries V).fraction input proof = V.fraction input proof := by
  simp only [NonadaptiveVerifier.fraction, padQueries_accepts]
  rfl

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": agreement at queried proof coordinates suffices. -/
theorem nonadaptive_congr {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (left right : ℕ → Bool) (coins : Fin (2 ^ V.randomBits))
    (h : ∀ j address, V.query coins j = .inr address → left address = right address) :
    V.accepts input left coins = V.accepts input right coins := by
  unfold NonadaptiveVerifier.accepts
  congr 1
  funext j
  cases hquery : V.query coins j with
  | inl i => rfl
  | inr address => exact h j address hquery

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": an arbitrary oracle restricts to a legal finite source proof. -/
theorem finite_source_accepts {n q length : ℕ} (V : NonadaptiveVerifier n q)
    (hbound : ∀ coins j address, V.query coins j = .inr address → address < length)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) :
    V.accepts input (finiteProofOracle (fun i : Fin length => proof i.val)) coins =
      V.accepts input proof coins := by
  apply nonadaptive_congr
  intro j address hquery
  simp [finiteProofOracle, hbound coins j address hquery]

theorem finite_source_fraction {n q length : ℕ} (V : NonadaptiveVerifier n q)
    (hbound : ∀ coins j address, V.query coins j = .inr address → address < length)
    (input : BitInput n) (proof : ℕ → Bool) :
    V.fraction input (finiteProofOracle (fun i : Fin length => proof i.val)) =
      V.fraction input proof := by
  simp only [NonadaptiveVerifier.fraction, finite_source_accepts V hbound]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": finite-source soundness applies to every natural-address oracle. -/
theorem finite_source_soundness {n q length : ℕ} (V : NonadaptiveVerifier n q)
    (hbound : ∀ coins j address, V.query coins j = .inr address → address < length)
    (input : BitInput n) (s : ℝ)
    (hsound : ∀ proof : BitInput length, V.fraction input (finiteProofOracle proof) ≤ s) :
    ∀ proof : ℕ → Bool, V.fraction input proof ≤ s := by
  intro proof
  rw [← finite_source_fraction V hbound input proof]
  exact hsound _

end NearCubicGates.Adapters.Proximity
