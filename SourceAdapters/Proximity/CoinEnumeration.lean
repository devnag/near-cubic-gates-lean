import SourceAdapters.Proximity.BlockEnumeration
import SourceAdapters.Proximity.CoinLoop

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": numeric source-coin order followed
by numeric padded-block order is exactly the combined binary coin order. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicGates.Published.CW19Proximity

theorem binaryCoins_ofFn {α : Type} (r k : ℕ) (f : Fin (2 ^ (r + k)) → α) :
    List.ofFn f = (List.ofFn fun i : Fin (2 ^ r) =>
      List.ofFn fun j : Fin (2 ^ k) => f ((splitBinaryCoins r k).symm (i, j))).flatten := by
  rw [List.ofFn_congr (pow_add 2 r k), List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  simp [splitBinaryCoins, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem coinWords_full {n q : ℕ} (V : NonadaptiveVerifier n q) :
    SourceCallee.coinWords V (2 ^ V.randomBits) = (List.ofFn (SourceCallee.blockOutputWord V)).flatten := by
  have hw : (List.range (2 ^ V.randomBits)).map (fun i =>
      if h : i < 2 ^ V.randomBits then SourceCallee.blockOutputWord V ⟨i, h⟩ else []) =
      List.ofFn (SourceCallee.blockOutputWord V) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < 2 ^ V.randomBits := by simpa using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, dif_pos hi']
  rw [SourceCallee.coinWords, List.flatMap_def, hw]

end NearCubicGates.Adapters.Proximity
