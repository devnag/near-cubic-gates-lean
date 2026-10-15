import Proof.Wire_3_5.FinalPassTop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **One phase**: one machine for every request, its per-request cost, and its `Step` from the entry bank
`(H₀ r, A₀ r)` to its exit bank `(H r, A r)`. -/
structure Phase (Req : Type) (t : ℕ) (H₀ : Req → Fin t → ℕ) (A₀ : Req → Fin t → List Bool) where
  s : ℕ
  M : Machine t s
  cost : Req → ℕ
  H : Req → Fin t → ℕ
  A : Req → Fin t → List Bool
  run : ∀ r, Step M (cost r) (H₀ r) (A₀ r) (H r) (A r)

/-- Two phases in sequence: base's `Step.seq` (one paid bridge step). -/
def Phase.seq {Req : Type} {t : ℕ} {H₀ : Req → Fin t → ℕ} {A₀ : Req → Fin t → List Bool}
    (p : Phase Req t H₀ A₀) (q : Phase Req t p.H p.A) : Phase Req t H₀ A₀ :=
  ⟨p.s + q.s, Composition.machine p.M q.M, fun r => p.cost r + 1 + q.cost r, q.H, q.A,
    fun r => Step.seq (p.run r) (q.run r)⟩

section Family
variable (l : Literals) (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The requests of one call family. -/
abbrev FReq : Type := {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}

/-- The final pass's input word: the request's word, then the seed word. -/
noncomputable abbrev fpIn (r : FReq l F kclk coef A a ha) : List Bool :=
  r.1.word ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

/-- The final pass's output word: the printed rational. -/
noncomputable abbrev fpOut (r : FReq l F kclk coef A a ha) : List Bool :=
  ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)

/-- The final pass's budget: `c₅·(pre + mainPass)(E₅)` at the ledger's `(n, kOf n, psiOf n)`. -/
noncomputable abbrev fpBudget (r : FReq l F kclk coef A a ha) : ℕ :=
  c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
    (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n)

/-- The entry bank: the framed input on tape `0`, every other tape blank. -/
noncomputable abbrev fpEntry {t : ℕ} (r : FReq l F kclk coef A a ha) : Fin t → List Bool :=
  fun i => if i.val = 0 then frame (fpIn l F kclk coef A a ha r) else []

/-- **The final pass at one call family, by phases**: the tape count, the output tape, the three phases (each from the
previous one's exit bank), and the output and head facts. The machine does not depend on the envelope. -/
structure FpPhases where
  t : ℕ
  ht : 2 ≤ t
  o : Fin t
  ho : o.val ≠ 0
  front : Phase (FReq l F kclk coef A a ha) t (fun _ _ => 0) (fpEntry l F kclk coef A a ha)
  seeds : Phase (FReq l F kclk coef A a ha) t front.H front.A
  out : Phase (FReq l F kclk coef A a ha) t seeds.H seeds.A
  outH : ∀ r, out.H r = fun _ => 0
  outA : ∀ r, out.A r o = fpOut l F kclk coef A a ha r

/-- The phases' total cost (two bridge steps). -/
def FpPhases.cost (X : FpPhases l F kclk coef A a ha) (r : FReq l F kclk coef A a ha) : ℕ :=
  X.front.cost r + 1 + (X.seeds.cost r + 1 + X.out.cost r)

/-- **The phases composed**, at a budget their cost fits: the machine family `Top.FinalPassBlocks` asks for. -/
noncomputable def FpPhases.blocks (X : FpPhases l F kclk coef A a ha)
    (fits : ∀ r, X.cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r) :
    Top.FinalPassBlocks l F E₅ c₅ kclk coef A a ha :=
  ⟨{ tapeCount := X.t
     stateCount := (X.front.seq (X.seeds.seq X.out)).s
     twoTapes := X.ht
     machine := (X.front.seq (X.seeds.seq X.out)).M
     outputTape := X.o
     outputFresh := X.ho
     cost := (X.front.seq (X.seeds.seq X.out)).cost
     exitH := X.out.H
     exitA := X.out.A
     step := fun r => (X.front.seq (X.seeds.seq X.out)).run r
     exitOut := X.outA
     fits := fits }, X.outH⟩

end Family

/-- **The final pass's plan** (the producer): the floors `E₅`, `CD₅` and the coefficient `c₅` in `FinalPassLeaf`'s
order of choice, the phases at every call family, and the explicit COST RESIDUAL `fits` (the phases' cost within
`c₅·finalClasses E₅ (n, kOf n, psiOf n)`). -/
noncomputable def fpPlan (E₅ : (l : Literals) → ℕ → Envelope) (CD₅ : (l : Literals) → ℕ → ℕ)
    (c₅ : (l : Literals) → (fe : ℕ) → GateFree l → ℕ)
    (phases : (l : Literals) → (F : GateFree l) → (kclk coef A a : ℕ) → (ha : a ≤ kclk + 1) →
      FpPhases l F kclk coef A a ha)
    (fits : ∀ (l : Literals) (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ l fe) F.E →
      CD₅ l fe ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
        (phases l F kclk coef A a ha).cost l F kclk coef A a ha r ≤
          fpBudget l F (E₅ l fe) (c₅ l fe F) kclk coef A a ha r) :
    (l : Literals) → FinalPassLeaf l :=
  fun l => Top.finalPassLeaf_of l (E₅ l) (CD₅ l) (c₅ l) fun fe F hF hE hCD kclk coef A a ha =>
    (phases l F kclk coef A a ha).blocks l F (E₅ l fe) (c₅ l fe F) kclk coef A a ha
      (fits l fe F hF hE hCD kclk coef A a ha)

end NearCubicWires.WireExponent3_5.FinalPass.PlanFP
