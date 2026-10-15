import Proof.Wire_3_5.PrimAsmPlan

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Compose
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- The glue's constant: the composed run's overhead per input symbol and per step of the two machines. -/
def glueK : ℕ := 1000

/-- **The glue**: two rewound word functions `w ↦ s` (within `b₄`) and `w ++ s ↦ o` (within `b₅`) compose to one ordinary
word function `w ↦ o` within every budget `B ≥ glueK·(|w| + b₄ + b₅ + 1)`. -/
def Glue : Type 1 :=
  ∀ {Req : Type} (w s o : Req → List Bool) (b4 b5 B : Req → ℕ),
    RepairOrdinary.RewoundWordFunction Req w s b4 →
    RepairOrdinary.RewoundWordFunction Req (fun r => w r ++ s r) o b5 →
    (∀ r, glueK * ((w r).length + b4 r + b5 r + 1) ≤ B r) →
    RepairSource.OrdinaryWordFunction Req w o B

/-- **The budget at every call**, for a coefficient rule `cg`. -/
def EnvFor (cg : ℕ → ℕ → ℕ) : Prop :=
  ∀ (l : Literals) (F : GateFree l) (E₄ E₅ : Envelope) (c₄ c₅ : ℕ), ClassLE E₄ F.E → ClassLE E₅ F.E →
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), cg c₄ c₅ ≤ coef →
      ∀ r : {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req},
        glueK * (r.1.word.length +
          c₄ * seedClasses E₄ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
            (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n) +
          c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
            (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n) + 1) ≤
        ((gate0 l F).budget kclk coef A a ha).callBudget r.1.n

/-- A coefficient rule with its budget inequality. -/
def EnvPack : Type := Σ' cg : ℕ → ℕ → ℕ, EnvFor cg

/-- The glue's own class floor: none (the glue's cost is charged to the classes of `F.E` through `cg`). -/
def zeroEnv : Envelope := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **PA.compose**: `ComposeLeaf` for every literal, from the glue and the budget. -/
noncomputable def composeLeaf (glue : Glue) (env : EnvPack) : ∀ l, ComposeLeaf l := fun l =>
  ⟨zeroEnv, env.1, fun F E₄ E₅ c₄ c₅ h4 h5 _ kclk coef A a ha hc s4 s5 =>
    glue (fun r : {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req} => r.1.word) (fun r => seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
      (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
      (fun r => c₄ * seedClasses E₄ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))
      (fun r => c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))
      (fun r => ((gate0 l F).budget kclk coef A a ha).callBudget r.1.n) s4 s5
      (env.2 l F E₄ E₅ c₄ c₅ h4 h5 kclk coef A a ha hc)⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Compose
