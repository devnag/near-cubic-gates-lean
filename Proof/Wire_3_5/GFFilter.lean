import Proof.Wire_3_5.GFExists
import Proof.Wire_3_5.Shared.GapFilter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierWalk
open NearCubicWires.SourceInterfaces

/-! ## Transport along a map that commutes with the field operations -/

section Transport
variable {K K' : Type} (o : BiasOps K) (o' : BiasOps K') (f : K → K')
  (hmul : ∀ a b, f (o.mul a b) = o'.mul (f a) (f b)) (hone : f o.one = o'.one) (htr : ∀ a, o'.tr (f a) = o.tr a)
include hmul hone

theorem pow_transport (v : K) : ∀ k, f (o.pow v k) = o'.pow (f v) k
  | 0 => hone
  | k + 1 => by simp only [BiasOps.pow]; rw [hmul, pow_transport v k]

include htr

theorem biasBit_transport (u v : K) (i : ℕ) : biasBit o' (f u) (f v) i = biasBit o u v i := by
  unfold biasBit
  rw [← pow_transport o o' f hmul hone v, ← hmul, htr]

theorem copyParity_transport (P : GapParams) (c : CopySeed P K) (Z : List Bool) :
    copyParity P o' (c.1, f c.2.1, f c.2.2) Z = copyParity P o c Z := by
  unfold copyParity
  simp only [biasBit_transport o o' f hmul hone htr]

theorem baseFilter_transport (P : GapParams) (s : BaseSeed P K) (Z : List Bool) :
    baseFilter P o' (fun j => ((s j).1, f (s j).2.1, f (s j).2.2)) Z = baseFilter P o s Z := by
  unfold baseFilter
  simp only [copyParity_transport o o' f hmul hone htr]

end Transport

theorem vertexSeed_transport {K K' : Type} (P : GapParams) (kEq : Fin (2 ^ P.fieldBits) ≃ K) (f : K ≃ K')
    (v : MargulisVertex P.baseSize) (j : Fin 128) :
    vertexSeed P (kEq.trans f) v j =
      ((vertexSeed P kEq v j).1, f (vertexSeed P kEq v j).2.1, f (vertexSeed P kEq v j).2.2) := rfl

/-- **The filter is transported by any bijection commuting with multiplication, one and the trace bit.** -/
theorem gapFilterWith_transport {K K' : Type} (P : GapParams) (o : BiasOps K) (o' : BiasOps K') (f : K ≃ K')
    (hmul : ∀ a b, f (o.mul a b) = o'.mul (f a) (f b)) (hone : f o.one = o'.one) (htr : ∀ a, o'.tr (f a) = o.tr a)
    (kEq : Fin (2 ^ P.fieldBits) ≃ K) (e : MargulisWalkSample P.baseSize P.walkLen) (Z : List Bool) :
    gapFilterWith P o' (kEq.trans f) e Z = gapFilterWith P o kEq e Z := by
  unfold gapFilterWith
  congr 1
  funext v
  have : vertexSeed P (kEq.trans f) v = fun j =>
      ((vertexSeed P kEq v j).1, f (vertexSeed P kEq v j).2.1, f (vertexSeed P kEq v j).2.2) := by
    funext j; exact vertexSeed_transport P kEq f v j
  rw [this]
  exact baseFilter_transport o o' f hmul hone htr P _ Z

/-! ## The three instances -/

/-- **The machine's field operations on `ℓ`-bit vectors**: the shift-and-xor product, one, and the masked-parity trace
bit `⟨τ, a⟩` (the refs of `WireExponent3_5GF2Refs`). -/
def bitOps (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : BiasOps (Fin (2 ^ ℓ)) where
  mul a b := ⟨fmulShift p ℓ a b, (fmulShift_spec p ℓ a b hc.2.1 a.isLt b.isLt).1⟩
  one := ⟨1, Nat.one_lt_two_pow (by have := hc.1; omega)⟩
  tr a := decide (parityMasked (tau p ℓ) a ℓ = 1)

/-- The certified field's operations, with the absolute trace. -/
noncomputable def refOps (p : ℕ) : BiasOps (AdjoinRoot (toPoly p)) where
  mul := (· * ·)
  one := 1
  tr x := decide (refTrace p x = 1)

theorem zmod2_val_eq_one (t : ZMod 2) : t.val = 1 ↔ t = 1 :=
  ⟨fun h => by rw [← ZMod.natCast_zmod_val t, h]; rfl, fun h => by rw [h]; rfl⟩

/-- **The bit-level filter is the certified field's filter** under the coordinate map `encEquiv`. -/
theorem gapFilterWith_bits_eq_ref (P : GapParams) (p : ℕ) (hc : PrimitiveCert p P.fieldBits)
    (e : MargulisWalkSample P.baseSize P.walkLen) (Z : List Bool) :
    gapFilterWith P (bitOps p P.fieldBits hc) (Equiv.refl _) e Z =
      gapFilterWith P (refOps p) (encEquiv p P.fieldBits hc.2.1) e Z := by
  rw [← gapFilterWith_transport P (bitOps p P.fieldBits hc) (refOps p) (encEquiv p P.fieldBits hc.2.1)]
  · rfl
  · intro a b
    exact (fmulShift_spec p P.fieldBits a b hc.2.1 a.isLt b.isLt).2
  · exact rep_one p
  · intro a
    show decide (refTrace p (rep p a) = 1) = decide (parityMasked (tau p P.fieldBits) a P.fieldBits = 1)
    rw [decide_eq_decide, trace_masked p P.fieldBits a hc a.isLt, zmod2_val_eq_one]
    rfl

/-- **The certified field's filter is the `GaloisField` filter** under the algebra isomorphism `refAlgEquivGalois`
(the absolute trace is invariant under algebra isomorphisms). -/
theorem gapFilterWith_ref_eq_galois (P : GapParams) (p : ℕ) (hc : PrimitiveCert p P.fieldBits)
    (kEq : Fin (2 ^ P.fieldBits) ≃ AdjoinRoot (toPoly p)) (e : MargulisWalkSample P.baseSize P.walkLen)
    (Z : List Bool) :
    gapFilterWith P (refOps p) kEq e Z =
      gapFilterWith P (galoisOps P.fieldBits) (kEq.trans (refAlgEquivGalois p P.fieldBits hc).toEquiv) e Z := by
  rw [gapFilterWith_transport P (refOps p) (galoisOps P.fieldBits) (refAlgEquivGalois p P.fieldBits hc).toEquiv]
  · intro a b
    exact map_mul (refAlgEquivGalois p P.fieldBits hc) a b
  · exact map_one (refAlgEquivGalois p P.fieldBits hc)
  · intro a
    show decide (Algebra.trace (ZMod 2) (GaloisField 2 P.fieldBits) (refAlgEquivGalois p P.fieldBits hc a) = 1) =
      decide (refTrace p a = 1)
    rw [Algebra.trace_eq_of_algEquiv]
    rfl

/-- **The machine's bit-level filter is the `GaloisField` filter** with the coordinate map
`encEquiv ≫ refAlgEquivGalois` (for any certified modulus, e.g. `firstPrimitive`). -/
theorem gapFilterWith_bits_eq_galois (P : GapParams) (p : ℕ) (hc : PrimitiveCert p P.fieldBits)
    (e : MargulisWalkSample P.baseSize P.walkLen) (Z : List Bool) :
    gapFilterWith P (bitOps p P.fieldBits hc) (Equiv.refl _) e Z =
      gapFilterWith P (galoisOps P.fieldBits)
        ((encEquiv p P.fieldBits hc.2.1).trans (refAlgEquivGalois p P.fieldBits hc).toEquiv) e Z := by
  rw [gapFilterWith_bits_eq_ref, gapFilterWith_ref_eq_galois]

theorem one_le_fieldBits (P : GapParams) : 1 ≤ P.fieldBits := by unfold GapParams.fieldBits; omega

/-- The search's modulus is certified at the filter's field size. -/
theorem firstPrimitive_fieldBits (P : GapParams) : PrimitiveCert (firstPrimitive P.fieldBits) P.fieldBits :=
  firstPrimitive_cert _ (one_le_fieldBits P)

end NearCubicWires.WireExponent3_5.GF
