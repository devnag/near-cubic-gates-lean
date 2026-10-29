import Proof.Wire_3_5.FinalPassWordMul
import Proof.Wire_3_5.GFRef

/-!
# Join: arithmetic in `𝔽₂[X]/(p)` for an arbitrary modulus of degree `ℓ` (no primitivity certificate)

Complement of the join `Joins/BinaryFieldArithmetic.lean`, whose representation conjunct assumes `GF.PrimitiveCert`,
i.e. a modulus found by the exhaustive primitive search. Consumer: input 6, the field of the succinct-ACSP instance.

Paper sentence: proof of `thm:short-pcp-ours`, Step 2, "Field operations": "The field `F` is represented by an
irreducible polynomial that Shoup's deterministic algorithm finds in `poly(f)` steps [BCGT13, Algorithm 17]. So each
field operation takes `poly(f)` steps." The modulus there comes from BCGT13 Algorithm 17, which promises an
*irreducible* polynomial of degree `ℓ`, not a primitive one. This join therefore assumes only `GF.ModulusOk p ℓ`
(bit `ℓ` set, `p < 2^(ℓ+1)`: monic of degree `ℓ`) for the representation and the machines, and irreducibility only
for the field property.

Which construction serves which field:
* small-bias sets, `lem:small-bias` (field degree `m` with `2^m < 2r/ε`): the exhaustive primitive search of
  `Joins/BinaryFieldArithmetic.lean`, at `300·4^m·(m+1)` steps in place of the paper's `2^m poly(m)` (both are
  `poly(r/ε)`);
* STV rounding, input 8 ("Full-range amplification interface", field degree `t = O(n)`): the same exhaustive search
  (`2^{O(n)}` is allowed there);
* the short-PCP field, input 6 (Step 2, "Field operations", degree `f ≈ log T`): **not** the exhaustive search (it
  would cost `T^{O(1)}`, not `poly(f)`); the modulus comes from BCGT13 Algorithm 17 (Shoup), and this join supplies
  the arithmetic for any such modulus.

Every conjunct is a released theorem (`GF.encEquiv`, `GF.natCard_ref`, `GF.toPoly_monic`, `GF.natDegree_toPoly`,
`GF.rep_xor`, `GF.fmulShift_spec`, `FinalPass.Tm.fmulW_spec`, `mapPass_spec`); the proof is
`Field/BinaryFieldModulus.lean`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The join.** Arithmetic in `F = 𝔽₂[X]/(p)` on `ℓ`-bit words for any modulus of degree `ℓ`. -/
def BinaryFieldModulus : Prop :=
  -- `thm:short-pcp-ours` "represented by an irreducible polynomial": a modulus of degree `ℓ` is monic of degree `ℓ`,
  -- `𝔽₂[X]/(p)` has `2^ℓ` elements and the `ℓ`-bit words enumerate it bijectively.
  (∀ p ℓ : ℕ, GF.ModulusOk p ℓ →
    (GF.toPoly p).Monic ∧ (GF.toPoly p).natDegree = ℓ ∧ Nat.card (AdjoinRoot (GF.toPoly p)) = 2 ^ ℓ ∧
      Function.Bijective (fun a : Fin (2 ^ ℓ) => GF.rep p a.val)) ∧
  -- an irreducible modulus makes `𝔽₂[X]/(p)` a field.
  (∀ p : ℕ, Irreducible (GF.toPoly p) → IsField (AdjoinRoot (GF.toPoly p))) ∧
  -- `thm:short-pcp-ours`, addition: the word XOR is the field sum, computed in place by `mapPass xorOut` in `41ℓ + 3` steps.
  (∀ p a b : ℕ, GF.rep p (a ^^^ b) = GF.rep p a + GF.rep p b) ∧
  (∀ {ns nr : ℕ} (cap : ℕ) (A B : Fin (ns + 1)) (F R : Fin nr), A ≠ B → F ≠ R → ∀ (ℓ a b : ℕ)
    (restA restB : List Bool) (σ : WState ns nr), 1 ≤ cap → 2 * ℓ ≤ cap →
    σ.st A = frameP (binary ℓ a) ++ false :: restA → σ.sh A = 0 →
    σ.st B = frameP (binary ℓ b) ++ restB → σ.sh B = 0 → σ.val F = 0 → σ.val R = 0 →
    WExec cap (mapPass xorOut keepS A B F R) σ
      ((σ.sets A (frameP (binary ℓ (a ^^^ b)) ++ false :: restA)).setv F 0) (41 * ℓ + 3)) ∧
  -- `thm:short-pcp-ours`, multiplication, for any modulus of degree `ℓ`: `fmulW` gives `z < 2^ℓ` with
  -- `rep p z = rep p x · rep p y` within `200·(ℓ+1)²` steps, frame-preserving.
  (∀ {ns nr : ℕ} (cap : ℕ) (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr),
    MulLayout Y ACC ST Pm F G R RY → ∀ (ℓ p x y : ℕ), 1 ≤ ℓ → GF.ModulusOk p ℓ → x < 2 ^ ℓ → y < 2 ^ ℓ →
    2 * ℓ + 2 ≤ cap → ∀ σ : WState ns nr, MulInv Y ACC ST Pm F G R RY ℓ p y 0 x 0 σ →
    ∃ (τ : WState ns nr) (z st : ℕ), WExec cap (fmulW Y ACC ST Pm F G R RY) σ τ (200 * (ℓ + 1) ^ 2) ∧
      MulInv Y ACC ST Pm F G R RY ℓ p y z st 0 τ ∧ z < 2 ^ ℓ ∧ GF.rep p z = GF.rep p x * GF.rep p y ∧
      WFrame (mulS Y ACC ST) (mulR F G R RY) σ τ)

end NearCubicGates.Adapters.Joins
