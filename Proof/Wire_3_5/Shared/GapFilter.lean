import Proof.Supplier.SupplierWalk
import Proof.Supplier.SupplierToeplitzCore
import Proof.Wire_3_5.Shared.GF

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk

structure GapParams where
  /-- `M`: the filter is applied to vectors `Z` of at most `len` coordinates -/
  len : ℕ
  /-- `U`: the cap -/
  cap : ℕ
  /-- the endpoint error is `ε = 2^{-errExp}` -/
  errExp : ℕ

namespace GapParams
variable (P : GapParams)

def prefixBits : ℕ := Nat.clog 2 (32 * P.cap)

def labelBits : ℕ := max P.prefixBits (Nat.clog 2 P.len)

def fieldBits : ℕ := Nat.clog 2 P.len + 4

theorem fieldBits_ne_zero : P.fieldBits ≠ 0 := by unfold fieldBits; omega

def walkLen : ℕ := 2 * (P.errExp / 4) + 1

/-- The number of seeds of one copy of the selected parity: a Toeplitz seed (`2·rank − 1` diagonal bits and a
`rank`-bit translation) and two field elements `u, v`. -/
def copySize : ℕ :=
  2 ^ P.labelBits * 2 ^ (P.labelBits - 1) * 2 ^ P.labelBits * (2 ^ P.fieldBits * 2 ^ P.fieldBits)

def baseSize : ℕ := P.copySize ^ 128

instance instNeZeroBaseSize : NeZero P.baseSize := ⟨by unfold baseSize copySize; positivity⟩

end GapParams

/-- The field operations the construction uses: multiplication, one, and the `𝔽₂`-valued trace (as a `Bool`).
The seed instantiates them with `GaloisField 2 m`; the executable twin with a computable field. -/
structure BiasOps (K : Type) where
  mul : K → K → K
  one : K
  tr : K → Bool

/-- `v^k` by repeated multiplication. -/
def BiasOps.pow {K : Type} (o : BiasOps K) (v : K) : ℕ → K
  | 0 => o.one
  | k + 1 => o.mul (o.pow v k) v

/-- The seed of one copy of the selected parity: the Toeplitz seed of the inclusion bits and `(u, v) ∈ 𝕂²`. -/
abbrev CopySeed (P : GapParams) (K : Type) : Type := ToeplitzSeed P.labelBits × K × K

abbrev BaseSeed (P : GapParams) (K : Type) : Type := Fin 128 → CopySeed P K

/-- The label of coordinate `i` (its binary expansion), distinct for distinct `i < 2^rank`. -/
def coordLabel (rank i : ℕ) : SupplierToeplitzCore.BitVec rank := fun j => if i.testBit j.val then 1 else 0

def selected (P : GapParams) (h : ToeplitzSeed P.labelBits) (i : ℕ) : Bool :=
  decide (∀ j : Fin P.labelBits, j.val < P.prefixBits → toeplitzHash (coordLabel P.labelBits i) h j = 0)

/-- The selected active coordinates: `Z_i = 1` and `H_i = 1`. -/
def selectedActive (P : GapParams) (h : ToeplitzSeed P.labelBits) (Z : List Bool) : Finset ℕ :=
  (Finset.range Z.length).filter fun i => Z.getD i false = true ∧ selected P h i = true

def biasBit {K : Type} (o : BiasOps K) (u v : K) (i : ℕ) : Bool := o.tr (o.mul u (o.pow v (i + 1)))

def copyParity (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (Z : List Bool) : Bool :=
  decide (Odd ((selectedActive P c.1 Z).filter fun i => biasBit o c.2.1 c.2.2 i = true).card)

def baseFilter (P : GapParams) {K : Type} (o : BiasOps K) (s : BaseSeed P K) (Z : List Bool) : Bool :=
  decide ((Finset.univ.filter fun j : Fin 128 => copyParity P o (s j) Z = true).card ≤ 32)

/-- The seeds of one copy, enumerated: `Fin copySize ≃ CopySeed`, from a coordinate map of the field. -/
def copyEquiv (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K) :
    Fin P.copySize ≃ CopySeed P K :=
  finProdFinEquiv.symm.trans <|
    Equiv.prodCongr
      (finProdFinEquiv.symm.trans <|
        Equiv.prodCongr
          (finProdFinEquiv.symm.trans <|
            Equiv.prodCongr (finFunctionFinEquiv.symm : Fin (2 ^ P.labelBits) ≃ (Fin P.labelBits → Fin 2))
              (finFunctionFinEquiv.symm : Fin (2 ^ (P.labelBits - 1)) ≃ (Fin (P.labelBits - 1) → Fin 2)))
          (finFunctionFinEquiv.symm : Fin (2 ^ P.labelBits) ≃ (Fin P.labelBits → Fin 2)))
      (finProdFinEquiv.symm.trans (Equiv.prodCongr kEq kEq))

/-- The base seeds, enumerated: `Fin baseSize ≃ BaseSeed`. -/
def baseEquiv (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K) :
    Fin P.baseSize ≃ BaseSeed P K :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin 128)) (copyEquiv P kEq))

/-- The base seed at a walk vertex: its first coordinate, decoded (the second coordinate is padding). -/
def vertexSeed (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (v : MargulisVertex P.baseSize) : BaseSeed P K :=
  baseEquiv P kEq ((ZMod.finEquiv P.baseSize).symm v.1)

def gapFilterWith (P : GapParams) {K : Type} (o : BiasOps K) (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (e : MargulisWalkSample P.baseSize P.walkLen) (Z : List Bool) : Bool :=
  concreteMajorityFailure (fun v => baseFilter P o (vertexSeed P kEq v) Z) e

noncomputable def galoisOps (m : ℕ) : BiasOps (GaloisField 2 m) where
  mul := (· * ·)
  one := 1
  tr := fun x => decide (Algebra.trace (ZMod 2) (GaloisField 2 m) x = 1)

noncomputable def galoisEquiv (m : ℕ) (hm : m ≠ 0) : Fin (2 ^ m) ≃ GaloisField 2 m :=
  if hc : GF.PrimitiveCert (GF.firstPrimitive m) m then
    (GF.encEquiv (GF.firstPrimitive m) m hc.2.1).trans (GF.refAlgEquivGalois (GF.firstPrimitive m) m hc).toEquiv
  else (Finite.equivFinOfCardEq (GaloisField.card 2 m hm)).symm

/-- **The seed space** `e` of the regular filter: a powered Margulis walk sample over the base seeds. -/
abbrev GapSeed (P : GapParams) : Type := MargulisWalkSample P.baseSize P.walkLen

instance (P : GapParams) : Fintype (GapSeed P) := inferInstanceAs (Fintype (MargulisWalkSample _ _))

instance (P : GapParams) : Nonempty (GapSeed P) := ⟨⟨(0, 0), fun _ _ => 0⟩⟩

noncomputable def gapFilter (P : GapParams) (e : GapSeed P) (Z : List Bool) : Bool :=
  gapFilterWith P (galoisOps P.fieldBits) (galoisEquiv P.fieldBits P.fieldBits_ne_zero) e Z

end NearCubicWires.WireExponent3_5.Filters
