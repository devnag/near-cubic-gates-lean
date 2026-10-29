import SourceAdapters.Proximity.ClauseQueries

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces": combine the old honest oracle with consistent
auxiliary assignments for every old coin string. This proves semantic perfect
completeness. Ordinary time bounds for producing the finite trimmed result
are established separately by the ordinary constructor.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
open NearCubicGates.Published.CW19Proximity

def combineProof (old : ℕ → Bool) (auxiliary : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun address => if address % 2 = 0 then old (address / 2)
    else auxiliary (Nat.unpair (address / 2)).1 (Nat.unpair (address / 2)).2

theorem combineProof_even (old : ℕ → Bool) (auxiliary : ℕ → ℕ → Bool) (address : ℕ) :
    combineProof old auxiliary (2 * address) = old address := by
  have hmod : (2 * address) % 2 = 0 := by omega
  have hdiv : (2 * address) / 2 = address := by omega
  simp [combineProof, hmod, hdiv]

theorem combineProof_odd (old : ℕ → Bool) (auxiliary : ℕ → ℕ → Bool) (row index : ℕ) :
    combineProof old auxiliary (2 * Nat.pair row index + 1) = auxiliary row index := by
  have hmod : (2 * Nat.pair row index + 1) % 2 = 1 := by omega
  have hdiv : (2 * Nat.pair row index + 1) / 2 = Nat.pair row index := by omega
  simp [combineProof, hmod, hdiv]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the source's honest proof extends to every padded clause. -/
theorem clauseVerifier_complete {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool)
    (honest : ∀ coins, V.accepts input proof coins = true) :
    ∃ newProof : ℕ → Bool, ∀ coins, (clauseVerifier V).accepts input newProof coins = true := by
  classical
  let answers (coins : Fin (2 ^ V.randomBits)) : BitInput q :=
    fun j => oracleValue input proof ((padQueries V).query coins j)
  have hrows : ∀ coins : Fin (2 ^ V.randomBits), ∃ assignment : ℕ → Bool,
      recoveredCircuitInput assignment = answers coins ∧
        formulaEval assignment (predicateBlock (rowPredicate V coins)) = true := by
    intro coins
    apply (predicateBlock_iff _ _).mp
    change (padQueries V).accepts input proof coins = true
    rw [padQueries_accepts]
    exact honest coins
  choose assignments hinputs hformulas using hrows
  let auxiliary (row index : ℕ) : Bool :=
    if h : row < 2 ^ V.randomBits then assignments ⟨row, h⟩ (q + index) else false
  let fresh := combineProof proof auxiliary
  have hold : originalProof fresh = proof := by
    funext address
    exact combineProof_even proof auxiliary address
  have hlocal (coins : Fin (2 ^ V.randomBits)) :
      localAssignment V input fresh coins = assignments coins := by
    funext address
    by_cases ha : address < q
    · simp only [localAssignment, localAddress, dif_pos ha, renamed_oracle, hold]
      exact (congrFun (hinputs coins) ⟨address, ha⟩).symm
    · have hsum : q + (address - q) = address := by omega
      simp [localAssignment, localAddress, ha, oracleValue, fresh, combineProof_odd,
        auxiliary, coins.isLt, hsum]
  refine ⟨fresh, fun coins => ?_⟩
  let pair := splitBinaryCoins V.randomBits (predicateBlockBits q) coins
  have hcoins : (splitBinaryCoins V.randomBits (predicateBlockBits q)).symm pair = coins :=
    Equiv.symm_apply_apply _ _
  rw [← hcoins, clauseVerifier_accepts, hlocal]
  exact List.all_eq_true.mp (hformulas pair.1) _ (List.get_mem _ _)

end NearCubicGates.Adapters.Proximity
