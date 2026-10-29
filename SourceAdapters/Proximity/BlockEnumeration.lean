import SourceAdapters.Proximity.RenderBlock
import Mathlib.Data.List.OfFn

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual flat block stream is
exactly the clause-major/query-major sequence specified by the verifier. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Published.CW19Proximity

theorem blockClauses_list {q : ℕ} (predicate : BitInput q → Bool) :
    List.ofFn (blockClause predicate) = predicateBlock predicate := by
  apply List.ext_getElem
  · simp [predicateBlock_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, blockClause, List.get_eq_getElem]

theorem block_output_enumeration {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) :
    SourceCallee.blockOutputWord V coins =
      (List.ofFn fun j : Fin (predicateBlockSize q) =>
        (List.ofFn fun k : Fin 3 =>
          (Joins.trimQueryFields (translatedLiteral V coins
            (blockLiteral (rowPredicate V coins) j k))).flatMap natWord).flatten).flatten := by
  unfold SourceCallee.blockOutputWord blockLiterals
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  conv_lhs => rw [← blockClauses_list (rowPredicate V coins)]
  simp only [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply, id_eq]
  rw [← blockLiteral_list (rowPredicate V coins) j]
  simp only [List.map_ofFn, Function.comp_def]

end NearCubicGates.Adapters.Proximity
