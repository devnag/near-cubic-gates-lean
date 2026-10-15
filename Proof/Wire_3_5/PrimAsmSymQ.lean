import Proof.Wire_3_5.PrimAsmPlan

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymQ
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces NearCubicWires.SupplierPipeline

/-- The list's walk length at error exponent `D·L + 5`: `2⌊(DL+5)/4⌋ + 1`. -/
def listWalk (D L : ℕ) : ℕ := 2 * ((D * L + 5) / 4) + 1

/-- The exponent of two in `|GapSeed × FlatSeed|`. -/
def symE (FP : GapParams) (D M B L : ℕ) : ℕ :=
  FP.seedBits + 2 * SupplierWalkBridge.toeplitzWalkSideBits (BaseListParams.rank ⟨M, B⟩) + 160 * (listWalk D L - 1)

/-- `Π_j (m_j+1)²`. -/
def prodSq (ms : List ℕ) : ℕ := (ms.map fun m => (m + 1) ^ 2).prod

/-- `Π_j (6m_j+2)`. -/
def prodMod (ms : List ℕ) : ℕ := (ms.map fun m => 6 * m + 2).prod

/-- **The SYM sample count as a formula.** -/
def symQval (D kh n : ℕ) (FP : GapParams) (M B L : ℕ) (ms : List ℕ) : ℕ :=
  Sampler.sampleCount kh D n (2 ^ symE FP D M B L * prodSq ms * (2 * prodSq ms * prodMod ms) ^ 2 + 1)

theorem prod_ofFn_eq {a : ℕ} (f : Fin a → ℕ) : ∏ j, f j = (List.ofFn f).prod := by
  rw [List.prod_ofFn]

theorem side_eq (P : FlatListParams) :
    P.side * P.side * (16 ^ 40) ^ (P.walkLen - 1) =
      2 ^ (2 * SupplierWalkBridge.toeplitzWalkSideBits P.base.rank + 160 * (P.walkLen - 1)) := by
  unfold FlatListParams.side
  rw [pow_add, show (16 : ℕ) ^ 40 = 2 ^ 160 by norm_num, ← pow_mul, two_mul, pow_add]

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **`Q` at a SYM call**: the sample count is the formula at the call's numbers. -/
theorem symCount_eq (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) :
    SeedFix.symCount I hs Cs carriers =
      symQval I.D (SeedFix.callKh (I.starParams n hs)) n (I.filterParams .sym n) (∑ i, (Cs i).bottomCount)
        (carriers.length * (4096 * B.capOf .sym n)) (Nat.clog 2 (n + 2))
        (List.ofFn fun i => (Cs i).bottomCount) := by
  unfold SeedFix.symCount symQval
  congr 1
  rw [Fintype.card_prod, Fintype.card_prod, card_gapSeed, FlatListParams.card_flatSeed, card_symState, side_eq]
  unfold SeedFix.symMassNat symE prodSq prodMod
  rw [prod_ofFn_eq, prod_ofFn_eq]
  have hm : ∀ j, symM (I.starParams n hs) Cs j = (Cs j).bottomCount := fun _ => rfl
  simp only [hm, symModulus, List.map_ofFn, Function.comp_def]
  have hw : (Primitive.symListParams I n a Cs carriers).walkLen - 1 = listWalk I.D (Nat.clog 2 (n + 2)) - 1 := rfl
  have hr : (Primitive.symListParams I n a Cs carriers).base.rank =
      BaseListParams.rank ⟨∑ i, (Cs i).bottomCount, carriers.length * (4096 * B.capOf .sym n)⟩ := rfl
  rw [hw, hr, pow_add, pow_add]
  ring

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.SymQ
