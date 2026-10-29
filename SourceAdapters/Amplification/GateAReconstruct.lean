import SourceAdapters.Amplification.GateA
import SourceAdapters.Field.BinaryFieldModulus

/-!
# Gate G-A, closing step: the leaf `STV.Theorem29` docks on the rounded code

`gateA_reconstruct` consumes the published statement `STV.Theorem29` (no other hypothesis) and shows that its
hypotheses are met exactly by the rounded parameters: there is one integer `C` (from the leaf's constant `c`,
`c² ≤ C`) such that, for every `n`, `k`, every monic irreducible `q` of degree `tParam C n k`, every truth table
`msg` and every `g` with agreement more than `1/2 + δ` with the code, some slot oracle `f` and some randomized
oracle machine `M` (description, coins and running time at most `K·(m + d + t + 1/δ³)^e`) satisfy
`M^f computes innerPoly` (STV Definition 20). With `innerPoly_recovers`, `M^f` computes the truth table at the
grid points. This is the input of A02 (circuit compilation of `M^f`, `app:sources`, "Full-range amplification interface").

`stvField`: the field is supplied by the fixed X3 join (`firstPrimitive t`, certified, hence irreducible), for
every `t ≥ 1` ("choose a binary extension field").
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset Polynomial NearCubicGates.Published.STV NearCubicWires.WireExponent3_5

/-- The STV field of degree `t`, from the X3 search: monic, irreducible, of degree `t`. -/
theorem stvField (t : ℕ) (ht : 1 ≤ t) :
    (GF.toPoly (GF.firstPrimitive t)).Monic ∧ Irreducible (GF.toPoly (GF.firstPrimitive t)) ∧
      (GF.toPoly (GF.firstPrimitive t)).natDegree = t := by
  have hc := (Field.binaryFieldArithmetic.2.1 t ht).1
  have hm := Field.binaryFieldModulus.1 _ t hc.2.1
  exact ⟨hm.1, (Field.binaryFieldArithmetic.1 _ t hc).1, hm.2.1⟩

/-- **Gate G-A, reconstruction.** From the leaf alone, an adversary with agreement more than `1/2 + δ` with the
rounded code yields a slot oracle and a small randomized oracle machine computing the inner polynomial. -/
theorem gateA_reconstruct (h29 : Theorem29) :
    ∃ (C : ℕ) (K : ℝ) (e : ℕ), ∀ (n k : ℕ) (q : (ZMod 2)[X]) [Fact (Irreducible q)] (hq : q.Monic)
      (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool)
      (g : (Fin ((mParam n k + 1) * tParam C n k) → Bool) → Bool),
      (1 / 2 + dyadicAcc k) * 2 ^ ((mParam n k + 1) * tParam C n k) <
        ((univ.filter fun w => g w = stvEncode C n k hq ht msg w).card : ℝ) →
      ∃ j0 < ⌊1 / dyadicAcc k ^ 2⌋₊, ∃ M : OracleMachine,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤
          K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e ∧
        M.HaltsWithin (fun z => slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (z, u))))
          (K * ((mParam n k : ℝ) + dParam n k + tParam C n k + 1 / dyadicAcc k ^ 3) ^ e) ∧
        M.Computes q (fun z => slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (z, u))))
          (innerPoly C n k q msg) := by
  obtain ⟨c, L, K, e, hc, h⟩ := h29
  refine ⟨⌈c ^ 2⌉₊, K, e, ?_⟩
  intro n k q _ hq ht msg g hg
  obtain ⟨j0, hj0, hagr⟩ := gateA_decoding ⌈c ^ 2⌉₊ n k hq ht msg g hg
  have hcond := thm29_condition c ⌈c ^ 2⌉₊ n k (Nat.le_ceil _)
  obtain ⟨Ms, _, hMs, hrec⟩ := h (tParam ⌈c ^ 2⌉₊ n k) q hq (Fact.out) ht (mParam n k) (dParam n k)
    (dyadicAcc k ^ 3) hcond (fun z => slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (z, u))))
  obtain ⟨M, hM, hcomp⟩ := hrec (innerPoly ⌈c ^ 2⌉₊ n k q msg) (innerPoly_degree _ n k hq ht msg) hagr
  obtain ⟨h1, h2, h3⟩ := hMs M hM
  exact ⟨j0, hj0, M, h1, h2, h3, hcomp⟩

end NearCubicGates.Adapters.Amplification
