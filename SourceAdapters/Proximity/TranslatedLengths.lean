import SourceAdapters.Proximity.AddressLengths
import SourceAdapters.Proximity.CanonicalHonest

/-!
Q03/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": every pre-trimming proof label, including the odd
auxiliary labels introduced by Appendix A, has polynomial bit length.
This is the width prerequisite for a paid comparison/sorting program; the
comparison/sorting program itself is not supplied by a numerical bound.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity

theorem double_bits_length (value : ℕ) : (2 * value).bits.length ≤ value.bits.length + 1 := by
  simp only [Nat.size_eq_bits_len]
  by_cases hzero : value = 0
  · simp [hzero]
  · have h := Nat.size_shiftLeft hzero 1
    simpa [Nat.shiftLeft_eq_mul_pow, Nat.mul_comm] using h.le

theorem padded_address_width {n q : ℕ} (V : NonadaptiveVerifier n q) (A : ℕ)
    (hquery : ∀ coins j address, V.query coins j = .inr address → address.bits.length ≤ A)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin q) (address : ℕ)
    (haddress : (padQueries V).query coins j = .inr address) : address.bits.length ≤ A := by
  dsimp only [padQueries] at haddress
  split at haddress
  · exact hquery coins _ address haddress
  · have hzero : address = 0 := by simpa using haddress.symm
    simp [hzero]

theorem local_address_width {n q : ℕ} (V : NonadaptiveVerifier n q) (A : ℕ)
    (hquery : ∀ coins j address, V.query coins j = .inr address → address.bits.length ≤ A)
    (coins : Fin (2 ^ V.randomBits)) (index : ℕ) (hindex : index < blockVariableBound q)
    (address : ℕ) (haddress : localAddress V coins index = .inr address) :
    address.bits.length ≤ A + 2 * (2 ^ V.randomBits + blockVariableBound q + 1) ^ 2 + 2 := by
  unfold localAddress at haddress
  split at haddress
  next hi =>
    cases hqueryValue : (padQueries V).query coins ⟨index, hi⟩ with
    | inl j => simp [hqueryValue, renamedAddress] at haddress
    | inr old =>
      have ha : address = 2 * old := by simpa [hqueryValue, renamedAddress] using haddress.symm
      subst address
      have hw := padded_address_width V A hquery coins ⟨index, hi⟩ old hqueryValue
      have hd := double_bits_length old
      omega
  next hi =>
    have ha : address = 2 * Nat.pair coins.val (index - q) + 1 := by simpa using haddress.symm
    subst address
    have hc := coins.isLt
    have hp := Nat.pair_lt_max_add_one_sq coins.val (index - q)
    have hm : max coins.val (index - q) + 1 ≤ 2 ^ V.randomBits + blockVariableBound q + 1 := by omega
    have hs := Nat.pow_le_pow_left hm 2
    have hb : (2 * Nat.pair coins.val (index - q) + 1).bits.length ≤
        2 * Nat.pair coins.val (index - q) + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    omega

theorem clause_address_width {n q : ℕ} (V : NonadaptiveVerifier n q) (A : ℕ)
    (hquery : ∀ coins j address, V.query coins j = .inr address → address.bits.length ≤ A)
    (coins : Fin (2 ^ (clauseVerifier V).randomBits)) (j : Fin 3) (address : ℕ)
    (haddress : ((clauseVerifier V).clause coins j).address = .inr address) :
    address.bits.length ≤ A + 2 * (2 ^ V.randomBits + blockVariableBound q + 1) ^ 2 + 2 := by
  let pair := splitBinaryCoins V.randomBits (predicateBlockBits q) coins
  have hi : (blockLiteral (rowPredicate V pair.1) pair.2 j).2 < blockVariableBound q :=
    predicateBlock_indices _ _ (List.get_mem _ _) _ (List.get_mem _ _)
  exact local_address_width V A hquery pair.1 _ hi address haddress

/-- Both renamed source labels and fresh auxiliary labels have polynomial width. -/
theorem clause_address_target_bound {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2))
    (hquery : SourcePolyTime (queryRequestWord (V := V))
      (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2))) :
    ∃ K e : ℕ, ∀ C : Circuit, ∀ coins j address,
      ((clauseVerifier (V (sourceCircuit C))).clause coins j).address = .inr address →
        address.bits.length ≤ K * (C.m + 1) ^ e := by
  obtain ⟨K, e, hwidth⟩ := query_address_target_bound V a hr hquery
  let D := 28 ^ a + blockVariableBound q + 1
  refine ⟨K + 2 * D ^ 2 + 2, max e (4 * a), fun C coins j address haddress => ?_⟩
  have hx := clause_address_width (V (sourceCircuit C)) (K * (C.m + 1) ^ e)
    (hwidth C) coins j address haddress
  have hcoins : 2 ^ (V (sourceCircuit C)).randomBits ≤ 28 ^ a * (C.m + 1) ^ (2 * a) := by
    simpa using logarithmic_coin_bound C _ a 0 (hr (sourceCircuit C))
  have hone : 1 ≤ (C.m + 1) ^ (2 * a) := Nat.one_le_pow _ _ (by omega)
  have hb : 2 ^ (V (sourceCircuit C)).randomBits + blockVariableBound q + 1 ≤
      D * (C.m + 1) ^ (2 * a) := by dsimp [D]; nlinarith
  have hsq := Nat.pow_le_pow_left hb 2
  have heq : (D * (C.m + 1) ^ (2 * a)) ^ 2 = D ^ 2 * (C.m + 1) ^ (4 * a) := by ring
  rw [heq] at hsq
  have he := Nat.pow_le_pow_right (by omega : 1 ≤ C.m + 1) (le_max_left e (4 * a))
  have ha := Nat.pow_le_pow_right (by omega : 1 ≤ C.m + 1) (le_max_right e (4 * a))
  have hu : 1 ≤ (C.m + 1) ^ max e (4 * a) := Nat.one_le_pow _ _ (by omega)
  have hke := Nat.mul_le_mul_left K he
  have hda := Nat.mul_le_mul_left (D ^ 2) ha
  nlinarith

end NearCubicGates.Adapters.Proximity
