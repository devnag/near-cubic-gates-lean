import Proof.Wire_3_5.FinalPassWordMul
import Proof.Wire_3_5.GFRef
import Proof.Wire_3_5.GFExists
import Proof.Wire_3_5.PrimAsmModulus

/-!
# Join: arithmetic in `𝔽₂[X]/(p)` as ordinary machines, with correctness in `AdjoinRoot`

Consumers: input 6 (the field of the small-bias construction) and input 8 (the field of the STV encoder).

Paper sentences this join delivers:
* proof of `lem:small-bias`: "Find an irreducible polynomial of degree `m` over `𝔽₂` by exhaustive search, in
  `2^m poly(m)` steps, and identify `𝔽_{2^m}` with `𝔽₂^m`."
* proof of `thm:short-pcp-ours`, Step 2, "Field operations": "The field `F` is represented by an irreducible
  polynomial … So each field operation takes `poly(f)` steps."
* "Full-range amplification interface": "choose a binary extension field, rounding its size up to the required
  scale".

This module states the interface. Its producer is `binaryFieldArithmetic` (`Field/BinaryField.lean`), which proves
every conjunct from the released companion: the representation `GF.rep`, the certificate `GF.PrimitiveCert`, the
search machine `PrimAsm.Modulus.modM`, the XOR pass `FinalPass.Tm.mapPass xorOut` and the shift-and-xor multiplier
`FinalPass.Tm.fmulW` with their step counts.

Representation. A field element is an `ℓ`-bit word `a < 2^ℓ`; it denotes `GF.rep p a = AdjoinRoot.mk (toPoly p)
(toPoly a)`, where `toPoly a = Σ_{a_i = 1} X^i`. A modulus is `p` with bit `ℓ` set and `p < 2^(ℓ+1)`
(`GF.ModulusOk p ℓ`); on machine tapes it is stored as the framed low `ℓ` bits `frame (binary ℓ p)`.

Difference from the paper's sentence: the released exhaustive search tests the *primitivity* certificate (LFSR
period `2^ℓ − 1`), and costs `O(4^ℓ·ℓ)` steps, not `2^ℓ poly(ℓ)`. Both consumers only need `2^{O(ℓ)}`: in
`lem:small-bias` `2^m < 2r/ε`, so `4^m` is still `poly(r/ε)`; in input 8 `2^ℓ = poly(2^n/δ)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The join.** Arithmetic in `F = 𝔽₂[X]/(p)` on `ℓ`-bit words, by ordinary machines with explicit step counts. -/
def BinaryFieldArithmetic : Prop :=
  -- `lem:small-bias` "identify 𝔽_{2^m} with 𝔽₂^m": for a certified modulus of degree `ℓ`, `𝔽₂[X]/(p)` is a field
  -- (`p` irreducible) with `2^ℓ` elements, and the `ℓ`-bit words enumerate it bijectively.
  (∀ p ℓ : ℕ, GF.PrimitiveCert p ℓ →
    Irreducible (GF.toPoly p) ∧ Nat.card (AdjoinRoot (GF.toPoly p)) = 2 ^ ℓ ∧
      Function.Bijective (fun a : Fin (2 ^ ℓ) => GF.rep p a.val)) ∧
  -- `lem:small-bias` "Find an irreducible polynomial of degree m over 𝔽₂ by exhaustive search": the search machine
  -- `modM`, from unary `ℓ` on tape 0, writes the framed low bits of the certified modulus `firstPrimitive ℓ` on
  -- tape 12 within `modCost ℓ ≤ 300·4^ℓ·(ℓ+1)` steps.
  (∀ ℓ : ℕ, 1 ≤ ℓ → GF.PrimitiveCert (GF.firstPrimitive ℓ) ℓ ∧
    ∃ tout : Fin 17 → List Bool,
      ExtDecompositionBatch.Step PrimAsm.Modulus.modM (PrimAsm.Modulus.modCost ℓ) (fun _ => 0)
        (fun i => if i.val = 0 then List.replicate ℓ true else []) (fun _ => 0) tout ∧
      tout 12 = frame (binary ℓ (GF.firstPrimitive ℓ))) ∧
  (∀ ℓ : ℕ, PrimAsm.Modulus.modCost ℓ ≤ 300 * 4 ^ ℓ * (ℓ + 1)) ∧
  -- `thm:short-pcp-ours` "each field operation takes poly(f) steps", addition: the word XOR is the field sum, and the WM
  -- pass `mapPass xorOut` computes it in place in `41ℓ + 3` steps.
  (∀ p a b : ℕ, GF.rep p (a ^^^ b) = GF.rep p a + GF.rep p b) ∧
  (∀ {ns nr : ℕ} (cap : ℕ) (A B : Fin (ns + 1)) (F R : Fin nr), A ≠ B → F ≠ R → ∀ (ℓ a b : ℕ)
    (restA restB : List Bool) (σ : WState ns nr), 1 ≤ cap → 2 * ℓ ≤ cap →
    σ.st A = frameP (binary ℓ a) ++ false :: restA → σ.sh A = 0 →
    σ.st B = frameP (binary ℓ b) ++ restB → σ.sh B = 0 → σ.val F = 0 → σ.val R = 0 →
    WExec cap (mapPass xorOut keepS A B F R) σ
      ((σ.sets A (frameP (binary ℓ (a ^^^ b)) ++ false :: restA)).setv F 0) (41 * ℓ + 3)) ∧
  -- `thm:short-pcp-ours`, multiplication: the WM subroutine `fmulW` turns `ACC = 0, ST = x, Y = y` (and the modulus on `Pm`)
  -- into `ACC = z` with `rep p z = rep p x · rep p y`, within `200·(ℓ+1)²` steps, touching only its own
  -- streams and registers.
  (∀ {ns nr : ℕ} (cap : ℕ) (Y ACC ST Pm : Fin (ns + 1)) (F G R RY : Fin nr),
    MulLayout Y ACC ST Pm F G R RY → ∀ (ℓ p x y : ℕ), 1 ≤ ℓ → GF.ModulusOk p ℓ → x < 2 ^ ℓ → y < 2 ^ ℓ →
    2 * ℓ + 2 ≤ cap → ∀ σ : WState ns nr, MulInv Y ACC ST Pm F G R RY ℓ p y 0 x 0 σ →
    ∃ (τ : WState ns nr) (z st : ℕ), WExec cap (fmulW Y ACC ST Pm F G R RY) σ τ (200 * (ℓ + 1) ^ 2) ∧
      MulInv Y ACC ST Pm F G R RY ℓ p y z st 0 τ ∧ z < 2 ^ ℓ ∧ GF.rep p z = GF.rep p x * GF.rep p y ∧
      WFrame (mulS Y ACC ST) (mulR F G R RY) σ τ)

end NearCubicGates.Adapters.Joins
