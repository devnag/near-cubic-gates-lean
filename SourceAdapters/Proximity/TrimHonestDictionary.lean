import SourceAdapters.Proximity.TrimHonestData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": finite key lookup agrees with every odd canonical proof
address; omitted keys have exact false semantics, not approximate truncation. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Published.CW19Proximity

theorem canonical_outside {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (address : ℕ)
    (hodd : address % 2 ≠ 0)
    (hmissing : address ∉ auxKeys (2 ^ V.randomBits) (blockVariableBound q)) :
    canonicalClauseProof V input proof address = false := by
  let row := (Nat.unpair (address / 2)).1
  let index := (Nat.unpair (address / 2)).2
  have heq : 2 * Nat.pair row index + 1 = address := by
    dsimp [row, index]
    rw [Nat.pair_unpair]
    have hm := Nat.mod_lt address (by decide : 0 < 2)
    omega
  rw [← heq]
  simp only [canonicalClauseProof, combineProof_odd]
  split
  next hr =>
    have hi : blockVariableBound q ≤ index := by
      by_contra h
      exact hmissing ((mem_auxKeys _ _ _).mpr ⟨row, hr, index, by omega, heq⟩)
    exact canonical_zero _ _ _ (by omega)
  next => rfl

def auxValues {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : List Bool :=
  (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).map (canonicalClauseProof V input proof)

theorem lookup_map (keys : List ℕ) (f : ℕ → Bool) (address : ℕ) (h : address ∈ keys) :
    (keys.map f).getD (keys.idxOf address) false = f address := by
  have hi := List.idxOf_lt_length_iff.mpr h
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_idxOf]

theorem auxiliary_lookup {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (address : ℕ) (hodd : address % 2 ≠ 0) :
    (auxValues V input proof).getD
      ((auxKeys (2 ^ V.randomBits) (blockVariableBound q)).idxOf address) false =
      canonicalClauseProof V input proof address := by
  by_cases hm : address ∈ auxKeys (2 ^ V.randomBits) (blockVariableBound q)
  · exact lookup_map _ _ _ hm
  · rw [canonical_outside V input proof address hodd hm, List.idxOf_eq_length hm]
    apply List.getD_eq_default
    simp [auxValues]

end NearCubicGates.Adapters.Proximity.TrimHonest
