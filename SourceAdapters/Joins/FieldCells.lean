import Proof.Gates.Cells.Kit
import Proof.Wire_3_5.GFRef

/-!
# Join FieldCells: arithmetic in `𝔽₂[X]/(p)` as macros of the cell language

**Proved** (`Machines.fieldCells`). Consumers: the single-run verifier's word functions (input 6), the STV
truth-table encoder (input 8) and the mask machine of the amplified verifier (input 6). Shared infrastructure: field
operations on the released cell language `NearCubicGates.Close.Cells` (`Proof/Gates/Cells/Lang.lean`: the programs
`St VV MM`, the semantics `Ex`, the Hoare layer `Hs` of `Cells/Hs.lean`), which a caller turns into an ordinary word
function with `wordFunction_of_lang` (`Proof/Gates/Cells/Run.lean`).

Paper sentences this join delivers:
* proof of `thm:short-pcp-ours`, Step 2, "Field operations": "The field `F` is represented by an irreducible
  polynomial … So each field operation takes `poly(f)` steps" — the four macros below, each with an explicit cost
  polynomial in `ℓ` (cell-language units; `wordFunction_of_lang` charges `O((W+1)²)` machine steps per unit at
  width `W`).
* `lem:small-bias`: "identify `𝔽_{2^m}` with `𝔽₂^m`" — the representation below (that of
  `Joins/BinaryFieldArithmetic.lean` and `Joins/BinaryFieldModulus.lean`).

Representation (as `Joins/BinaryFieldArithmetic.lean`): a field element is a number `a < 2^ℓ` held in one cell
variable; it denotes `GF.rep p a` (`Proof/Wire_3_5/Shared/GF.lean`). The modulus value `p` (`GF.ModulusOk p ℓ`: bit
`ℓ` set, `p < 2^(ℓ+1)`) and the number `2^ℓ` sit in two further variables. The cell width must hold `2^ℓ`:
`ℓ + 1 ≤ C.Wd`.

Scratch variables. Each macro uses a block of consecutive variables `vr s, …, vr (s + k − 1)` (`blk s k`), given by
its base `s`; its operands lie outside the block (`Out s k`). Nested macros use sub-blocks, so callers only choose
`s`. Every macro changes only its output and its block (`Fr a b (z :: blk s k)`) and leaves every non-variable part
of the state unchanged (`b.sh = a.sh`: input position, output, stores, call registers).

Macros (the code is fixed here; the proofs are `ShortPCP/Machines/FieldCellsProof.lean`, theorem
`Machines.fieldCells : FieldCells`):
* `fxorS x y z t s`: `z := (x ⊕ y) mod 2^ℓ` (the field sum on reduced words), block `5`;
* `fmulS x y z t p s`: `z := x·y` (shift-and-xor, the reference `GF.fmulShift`), block `11`;
* `fpowS x e z t p s`: `z := x^e` (square-and-multiply over the bits of `e`), block `16`;
* `finvS x z t p s`: `z := x^(2^ℓ − 2)`, the inverse of `x ≠ 0` when `p` is irreducible, block `18`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

namespace FieldCells

/-- Variable number `i` (taken mod `VV`; the specifications keep `i < VV`). -/
def vr (i : ℕ) : Fin VV := ⟨i % VV, Nat.mod_lt _ (by decide)⟩

/-- The scratch block `vr s, …, vr (s + k − 1)`. -/
def blk (s k : ℕ) : List (Fin VV) := (List.range k).map fun i => vr (s + i)

/-- The variable `x` lies outside the block of `k` variables at `s`. -/
def Out (s k : ℕ) (x : Fin VV) : Prop := x.val < s ∨ s + k ≤ x.val

/-- `bu := u mod 2`, `u := u / 2`. -/
def bitS (u bu : Fin VV) : St VV MM :=
  .seq (.op (.copy bu u)) (.seq (.op (.half u)) (.seq (.op (.sub bu u)) (.op (.sub bu u))))

/-- One pass of the sum: the low bits of `u`, `v`; add the place value `w` to `z` when they differ; `w := 2w`. -/
def xorBody (z : Fin VV) (s : ℕ) : St VV MM :=
  .seq (bitS (vr s) (vr (s + 3))) (.seq (bitS (vr (s + 1)) (vr (s + 4)))
    (.seq (.ite (.eq (vr (s + 3)) (vr (s + 4))) (.op (.zero (vr (s + 3)))) (.op (.add z (vr (s + 2)))))
      (.op (.shl (vr (s + 2))))))

/-- **Sum.** `z := (x ⊕ y) mod t` for `t = 2^ℓ` (`u, v, w, bu, bv` = block `s … s+4`). -/
def fxorS (x y z t : Fin VV) (s : ℕ) : St VV MM :=
  .seq (.op (.copy (vr s) x)) (.seq (.op (.copy (vr (s + 1)) y)) (.seq (.op (.zero z))
    (.seq (.op (.zero (vr (s + 2)))) (.seq (.op (.inc (vr (s + 2))))
      (.loop (.lt (vr (s + 2)) t) (xorBody z s))))))

/-- One pass of the product (one step `GF.mulStep`): bit `i` of `y` adds the shifted `x` to `z`, then the shifted
`x` is multiplied by `X` (`GF.lfsr`: shift, and xor the modulus when bit `ℓ` appears). -/
def mulBody (z t p : Fin VV) (s : ℕ) : St VV MM :=
  .seq (bitS (vr (s + 1)) (vr (s + 3)))
    (.seq (.ite (.eq (vr (s + 3)) (vr (s + 4))) (.op (.zero (vr (s + 5))))
        (.seq (fxorS z (vr s) (vr (s + 5)) t (s + 6)) (.op (.copy z (vr (s + 5))))))
      (.seq (.op (.shl (vr s)))
        (.seq (.ite (.lt (vr s) t) (.op (.zero (vr (s + 5))))
            (.seq (fxorS (vr s) p (vr (s + 5)) t (s + 6)) (.op (.copy (vr s) (vr (s + 5))))))
          (.op (.shl (vr (s + 2)))))))

/-- **Product.** `z := x·y` in `𝔽₂[X]/(p)` (`a, v, w, bit, zero, tmp` = block `s … s+5`, the sum at `s+6`). -/
def fmulS (x y z t p : Fin VV) (s : ℕ) : St VV MM :=
  .seq (.op (.copy (vr s) x)) (.seq (.op (.copy (vr (s + 1)) y)) (.seq (.op (.zero z))
    (.seq (.op (.zero (vr (s + 4)))) (.seq (.op (.zero (vr (s + 2)))) (.seq (.op (.inc (vr (s + 2))))
      (.loop (.lt (vr (s + 2)) t) (mulBody z t p s)))))))

/-- One pass of the power: the low bit of the exponent multiplies `z` by the base; the base is squared. -/
def powBody (z t p : Fin VV) (s : ℕ) : St VV MM :=
  .seq (bitS (vr (s + 1)) (vr (s + 2)))
    (.seq (.ite (.eq (vr (s + 2)) (vr (s + 3))) (.op (.zero (vr (s + 4))))
        (.seq (fmulS z (vr s) (vr (s + 4)) t p (s + 5)) (.op (.copy z (vr (s + 4))))))
      (.seq (fmulS (vr s) (vr s) (vr (s + 4)) t p (s + 5)) (.op (.copy (vr s) (vr (s + 4))))))

/-- **Power.** `z := x^e` (`base, exponent, bit, zero, tmp` = block `s … s+4`, the product at `s+5`). -/
def fpowS (x e z t p : Fin VV) (s : ℕ) : St VV MM :=
  .seq (.op (.copy (vr s) x)) (.seq (.op (.copy (vr (s + 1)) e)) (.seq (.op (.zero (vr (s + 3))))
    (.seq (.op (.zero z)) (.seq (.op (.inc z))
      (.loop (.lt (vr (s + 3)) (vr (s + 1))) (powBody z t p s))))))

/-- **Inverse.** `z := x^(2^ℓ − 2)` (`e, 2` = block `s, s+1`, the power at `s+2`). -/
def finvS (x z t p : Fin VV) (s : ℕ) : St VV MM :=
  .seq (.op (.copy (vr s) t)) (.seq (.op (.zero (vr (s + 1)))) (.seq (.op (.inc (vr (s + 1))))
    (.seq (.op (.inc (vr (s + 1)))) (.seq (.op (.sub (vr s) (vr (s + 1)))) (fpowS x (vr s) z t p (s + 2))))))

/-- Cost of the sum (cell-language units). -/
def xorCost (ℓ : ℕ) : ℕ := 22 * ℓ + 12

/-- Cost of the product. -/
def mulCost (ℓ : ℕ) : ℕ := ℓ * (2 * xorCost ℓ + 21) + 14

/-- Cost of the power, by the bit length of the exponent. -/
def powCost (ℓ e : ℕ) : ℕ := Nat.size e * (2 * mulCost ℓ + 16) + 12

/-- Cost of the inverse. -/
def invCost (ℓ : ℕ) : ℕ := ℓ * (2 * mulCost ℓ + 16) + 24

end FieldCells

open FieldCells

/-- **Join FieldCells.** The four field macros meet their specifications in the cell semantics, with costs
polynomial in `ℓ` (`thm:short-pcp-ours`, Step 2, "Field operations"). -/
def FieldCells : Prop :=
  -- "Field operations", the sum: `z = (x ⊕ y) mod 2^ℓ` (the field sum `GF.rep_xor` on words `< 2^ℓ`)
  (∀ (C : Ctx) (x y z t : Fin VV) (s ℓ : ℕ) (a : DS VV MM), s + 5 ≤ VV → Out s 5 x → Out s 5 y → Out s 5 z →
    Out s 5 t → z ≠ x → z ≠ y → z ≠ t → a.env t = 2 ^ ℓ → ℓ + 1 ≤ C.Wd →
    Hs C (fxorS x y z t s) a (xorCost ℓ)
      (fun b => b.env z = (a.env x ^^^ a.env y) % 2 ^ ℓ ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 5))) ∧
  -- "Field operations", the product: `z = fmulShift p ℓ x y`, the word of `rep x · rep y`
  (∀ (C : Ctx) (x y z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM), s + 11 ≤ VV → Out s 11 x → Out s 11 y →
    Out s 11 z → Out s 11 t → Out s 11 p → z ≠ x → z ≠ y → z ≠ t → z ≠ p → a.env t = 2 ^ ℓ → a.env p = pv →
    GF.ModulusOk pv ℓ → ℓ + 1 ≤ C.Wd → a.env x < 2 ^ ℓ → a.env y < 2 ^ ℓ →
    Hs C (fmulS x y z t p s) a (mulCost ℓ)
      (fun b => b.env z = GF2.fmulShift pv ℓ (a.env x) (a.env y) ∧ b.env z < 2 ^ ℓ ∧
        GF.rep pv (b.env z) = GF.rep pv (a.env x) * GF.rep pv (a.env y) ∧ b.sh = a.sh ∧ Fr a b (z :: blk s 11))) ∧
  -- "Field operations", the power: `rep z = (rep x)^e`, cost by the bit length of `e`
  (∀ (C : Ctx) (x e z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM), s + 16 ≤ VV → Out s 16 x → Out s 16 e →
    Out s 16 z → Out s 16 t → Out s 16 p → z ≠ x → z ≠ e → z ≠ t → z ≠ p → a.env t = 2 ^ ℓ → a.env p = pv →
    GF.ModulusOk pv ℓ → 1 ≤ ℓ → ℓ + 1 ≤ C.Wd → a.env x < 2 ^ ℓ →
    Hs C (fpowS x e z t p s) a (powCost ℓ (a.env e))
      (fun b => b.env z < 2 ^ ℓ ∧ GF.rep pv (b.env z) = GF.rep pv (a.env x) ^ a.env e ∧ b.sh = a.sh ∧
        Fr a b (z :: blk s 16))) ∧
  -- "Field operations", the inverse: `rep z = (rep x)^(2^ℓ − 2)`, so `rep z · rep x = 1` for `x ≠ 0` when `p` is
  -- irreducible ("represented by an irreducible polynomial")
  (∀ (C : Ctx) (x z t p : Fin VV) (s ℓ pv : ℕ) (a : DS VV MM), s + 18 ≤ VV → Out s 18 x → Out s 18 z →
    Out s 18 t → Out s 18 p → z ≠ x → z ≠ t → z ≠ p → a.env t = 2 ^ ℓ → a.env p = pv →
    GF.ModulusOk pv ℓ → 1 ≤ ℓ → ℓ + 1 ≤ C.Wd → a.env x < 2 ^ ℓ →
    Hs C (finvS x z t p s) a (invCost ℓ)
      (fun b => b.env z < 2 ^ ℓ ∧ GF.rep pv (b.env z) = GF.rep pv (a.env x) ^ (2 ^ ℓ - 2) ∧
        (Irreducible (GF.toPoly pv) → a.env x ≠ 0 → GF.rep pv (b.env z) * GF.rep pv (a.env x) = 1) ∧
        b.sh = a.sh ∧ Fr a b (z :: blk s 18))) ∧
  -- "Field operations", "poly(f) steps": the cost polynomials
  (∀ ℓ : ℕ, xorCost ℓ ≤ 34 * (ℓ + 1) ∧ mulCost ℓ ≤ 100 * (ℓ + 1) ^ 2 ∧
    invCost ℓ ≤ 250 * (ℓ + 1) ^ 3 ∧ ∀ e, powCost ℓ e ≤ 250 * (Nat.size e + 1) * (ℓ + 1) ^ 2)

end NearCubicGates.Adapters.Joins
