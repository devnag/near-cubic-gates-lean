import SourceAdapters.Proximity.TrimHonestRowAnswers
import SourceAdapters.Proximity.TrimHonestDictionary
import SourceAdapters.Code.ShiftedBits

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the auxiliary dictionary stores the canonical assignment
at q+i. Its actual row producer therefore shifts the finite table by q and
retains exact false defaults beyond the table's finite length. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Published.CW19Proximity

def auxiliaryValues {n q : ℕ} (V : NonadaptiveVerifier n q) (input : BitInput n)
    (proof : ℕ → Bool) (rows : ℕ) : List Bool :=
  (auxKeys rows (blockVariableBound q)).map (canonicalClauseProof V input proof)

theorem auxiliary_values_succ {n q : ℕ} (V : NonadaptiveVerifier n q) (input : BitInput n)
    (proof : ℕ → Bool) (rows : ℕ) :
    auxiliaryValues V input proof (rows + 1) = auxiliaryValues V input proof rows ++
      (rowKeys (blockVariableBound q) rows).map (canonicalClauseProof V input proof) := by
  simp only [auxiliaryValues, auxKeys_succ, List.map_append]

theorem row_values_shifted {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (input : BitInput n) (proof : BitInput N) :
    (rowKeys (blockVariableBound q) coins.val).map
        (canonicalClauseProof V input (finiteProofOracle proof)) =
      Code.ShiftedBits.shifted
        (List.ofFn fun i : Fin (blockVariableBound q) =>
          canonicalBlockAssignment (rowPredicate V coins) (rowAnswers V coins input proof) i.val)
        q (blockVariableBound q) := by
  simp only [rowKeys, Code.ShiftedBits.shifted, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, canonicalClauseProof, combineProof_odd,
    dif_pos coins.isLt, canonical_word_lookup]
  rfl

end NearCubicGates.Adapters.Proximity.TrimHonest
