import Proof.Wire_3_5.PrimitiveFused
import Proof.Wire_3_5.GFFilter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive

def filterBits (P : GapParams) (e : GapSeed P) (Z : List Bool) : Bool :=
  gapFilterWith P (GF.bitOps (GF.firstPrimitive P.fieldBits) P.fieldBits (GF.firstPrimitive_fieldBits P))
    (Equiv.refl _) e Z

/-- The seed's regular filter is the bit-level filter (the seed's `Checks/GapFilterBits`). -/
theorem gapFilter_eq_filterBits (P : GapParams) (e : GapSeed P) (Z : List Bool) :
    gapFilter P e Z = filterBits P e Z := by
  have hg : galoisEquiv P.fieldBits P.fieldBits_ne_zero =
      (GF.encEquiv (GF.firstPrimitive P.fieldBits) P.fieldBits (GF.firstPrimitive_fieldBits P).2.1).trans
        (GF.refAlgEquivGalois (GF.firstPrimitive P.fieldBits) P.fieldBits (GF.firstPrimitive_fieldBits P)).toEquiv := by
    unfold galoisEquiv
    exact dif_pos (GF.firstPrimitive_fieldBits P)
  have h := GF.gapFilterWith_bits_eq_galois P _ (GF.firstPrimitive_fieldBits P) e Z
  unfold filterBits gapFilter
  rw [h, hg]

/-- **The call's mask at the bit level**: the product of the named carriers' bit-level filters at the translation. -/
def maskBits (P : StarParams) (σ : P.Translation) (carriers : List (Carrier P.n)) (FP : GapParams) (e : GapSeed FP)
    (x : BitInput P.n) : Bool :=
  carriers.all fun X => filterBits FP e (inputResidualBits P σ X x)

theorem symMask_eq_maskBits (P : StarParams) (σ : P.Translation) (carriers : List (Carrier P.n)) (FP : GapParams) :
    symMask P σ carriers FP = maskBits P σ carriers FP := by
  funext e x
  exact congrArg carriers.all (funext fun X => gapFilter_eq_filterBits FP e _)

/-! ## A determined indexing of the live halves -/

/-- `Option (Fin b) ≃ Fin (b+1)`: `none ↦ 0`, `some i ↦ i+1` (a block without an error, or its erroneous coordinate). -/
def optionFinEquiv (b : ℕ) : Option (Fin b) ≃ Fin (b + 1) where
  toFun o := match o with
    | none => 0
    | some i => i.succ
  invFun k := if h : (k : ℕ) = 0 then none else some ⟨k - 1, by have := k.isLt; omega⟩
  left_inv o := by
    cases o with
    | none => simp
    | some i => simp [Fin.succ]
  right_inv k := by
    by_cases h : (k : ℕ) = 0
    · simp only [h, dif_pos]; ext; simp [h]
    · simp only [h, dif_neg, not_false_eq_true]; ext; simp; omega

/-- **The live halves as mixed-radix codes**: `P.Errors ≃ Fin ((b+1)^{r/2})` (determined, no choice). -/
def errorsEquiv (P : StarParams) : P.Errors ≃ Fin ((P.b + 1) ^ (P.r / 2)) :=
  (Equiv.piCongrRight fun _ => optionFinEquiv P.b).trans finFunctionFinEquiv

end NearCubicWires.WireExponent3_5.FinalPass
