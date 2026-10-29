import NineInputs

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": mathematical exact-three-query intermediate model used by
the proved clause conversion and trimming. The definitions retain their names
for consumers of the prior model location; no algorithm existence is assumed. -/
set_option autoImplicit false
namespace NearCubicGates.Published.CW19Proximity
open NearCubicWires

/-- Lemma 24(1): "these 3 queried bits or their negations". -/
structure SignedQuery (n : ℕ) where
  address : QueryAddress n
  negated : Bool

/-- Lemma 24(1): "these 3 queried bits or their negations". -/
def SignedQuery.eval {n : ℕ} (query : SignedQuery n)
    (input : BitInput n) (proof : ℕ → Bool) : Bool :=
  if query.negated then !(oracleValue input proof query.address)
  else oracleValue input proof query.address

/-- Lemma 24(1): "Given the random coins, the verifier simply computes an OR
on these 3 queried bits or their negations, and accepts iff the OR is true." -/
structure ThreeQueryVerifier (n : ℕ) where
  randomBits : ℕ
  clause : Fin (2 ^ randomBits) → Fin 3 → SignedQuery n

/-- Lemma 24(1): "accepts iff the OR is true." -/
def ThreeQueryVerifier.accepts {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : Bool :=
  (List.ofFn fun j => (V.clause coins j).eval input proof).any id

/-- Definition 20: "accepts oracle y ◦ π with probability at most s(|x|)." -/
noncomputable def ThreeQueryVerifier.fraction {n : ℕ} (V : ThreeQueryVerifier n)
    (input : BitInput n) (proof : ℕ → Bool) : ℝ :=
  ((Finset.univ.filter fun coins => V.accepts input proof coins = true).card : ℝ) /
    (2 ^ V.randomBits : ℝ)

end NearCubicGates.Published.CW19Proximity
