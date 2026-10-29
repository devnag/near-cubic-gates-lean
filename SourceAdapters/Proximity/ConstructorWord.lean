import SourceAdapters.Proximity.CoinEnumeration

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact final constructor word,
including headers and coin-major/query-major natWord literal triples. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Published.CW19Proximity

theorem clause_words_eq {n q : ℕ} (V : NonadaptiveVerifier n q) :
    (List.ofFn fun coins : Fin (2 ^ (V.randomBits + predicateBlockBits q)) =>
      (List.ofFn fun j : Fin 3 =>
        (Joins.trimQueryFields ((clauseVerifier V).clause coins j)).flatMap natWord).flatten).flatten =
      SourceCallee.coinWords V (2 ^ V.randomBits) := by
  rw [binaryCoins_ofFn V.randomBits (predicateBlockBits q)]
  simp only [clauseVerifier, Equiv.apply_symm_apply]
  rw [List.flatten_flatten]
  simp only [List.map_ofFn, Function.comp_def]
  rw [coinWords_full]
  congr 1
  apply congrArg List.ofFn
  funext coins
  exact (block_output_enumeration V coins).symm

theorem constructor_word {n q : ℕ} (V : NonadaptiveVerifier n q) :
    Joins.trimRequestWord ⟨n, clauseVerifier V⟩ =
      natWord n ++ natWord (V.randomBits + predicateBlockBits q) ++
        SourceCallee.coinWords V (2 ^ V.randomBits) := by
  unfold Joins.trimRequestWord Joins.trimRequestFields
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← clause_words_eq V]
  congr 1
  simp only [List.flatMap_def, List.map_flatten, List.map_ofFn, Function.comp_def]
  simp only [List.flatten_flatten, List.map_ofFn, Function.comp_def]
  rfl

end NearCubicGates.Adapters.Proximity
