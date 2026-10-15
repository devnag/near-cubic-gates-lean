import Proof.Wire_3_5.PrimAsmPlan
import Proof.Wire_3_5.FinalPassMajMain

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Primitive NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

variable (l : Literals)

/-- The machine family the final pass must supply at one call family. -/
noncomputable abbrev FinalPassBlocks (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : Type :=
  { W : WordBlocks {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}
      (fun r => r.1.word ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
      (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
      (fun r => c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n)) // ∀ r, W.exitH r = fun _ => 0 }

noncomputable def finalPassLeaf_of (E₅ : ℕ → Envelope) (CD₅ : ℕ → ℕ) (c₅ : (fe : ℕ) → GateFree l → ℕ)
    (W : ∀ (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ fe) F.E → CD₅ fe ≤ F.CD →
      ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FinalPassBlocks l F (E₅ fe) (c₅ fe F) kclk coef A a ha) :
    FinalPassLeaf l :=
  fun fe => ⟨E₅ fe, CD₅ fe, fun F hF hE hCD => ⟨c₅ fe F, fun kclk coef A a ha =>
    (W fe F hF hE hCD kclk coef A a ha).1.toRewound (W fe F hF hE hCD kclk coef A a ha).2⟩⟩

end NearCubicWires.WireExponent3_5.FinalPass.Top
