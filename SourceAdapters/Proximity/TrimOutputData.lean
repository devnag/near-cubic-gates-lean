import SourceAdapters.Proximity.TrimAddressBounds
import SourceAdapters.Proximity.TrimCollectAction

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact target output in query-table order.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def literalValue {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) : ℕ :=
  2 * (match q.address with
    | .inl i => i.val
    | .inr address => n + (trimSortedAddresses ⟨n, V⟩).idxOf address) + q.negated.toNat

def literalWord {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n) : List Bool :=
  frame (literalValue V q).bits

theorem literalValue_clause {n : ℕ} (V : ThreeQueryVerifier n)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    literalValue V (V.clause coins j) =
      NearCubicWires.RepairSource.literalCode ((trimVerifier V).clause coins j) := by
  rw [trimmed_literalCode, denseAddress_val]
  rfl

theorem trimmedWord_eq {n : ℕ} (V : ThreeQueryVerifier n) :
    (trimVerifier V).word = frame (usedProofAddresses V).card.bits ++
      frame V.randomBits.bits ++ (queries V).flatMap (literalWord V) := by
  simp only [NearCubicGates.PublishedSources.PCPP.RawThreeQueryPCPP.word]
  have hp : (trimVerifier V).proofBits = (usedProofAddresses V).card := rfl
  have hr : (trimVerifier V).randomBits = V.randomBits := rfl
  simp only [hp, hr]
  simp only [queries, literalWord, List.flatMap_def, List.map_flatten,
    List.flatten_flatten, List.map_ofFn, Function.comp_def, literalValue_clause]
  rfl

end NearCubicGates.Adapters.Proximity.Trim
