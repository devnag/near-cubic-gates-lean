import Proof.Wire_3_5.FinalPassSeamsWS
import Proof.Wire_3_5.FinalPassSeamsFits

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **The front phase on S4's layout** (PA2's composition target): a `Phase` from `fpEntry` whose exit meets
`FrontOut` at `Y`'s words, `Num = 0`, `Den = fpDen` in `W`-bit binary and `Y`'s register lengths, within
`s5Bound Cf Df`. -/
structure FrontPh (Y : SeedsProg2 l F kclk coef A a ha Sw) where
  ph : Phase (FReq l F kclk coef A a ha) Y.t (fun _ _ => 0) (fpEntry l F kclk coef A a ha)
  W : FReq l F kclk coef A a ha → ℕ
  hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r
  out : FrontOut l F kclk coef A a ha Y.wd ![Y.tN, Y.tD] (frontWordsW l F kclk coef A a ha Sw)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) W
    (fun r j => if Y.reg j then Y.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Y.Dc + 1 else 0) ph.H ph.A
  Cf : ℕ
  Df : ℕ
  cost_le : ∀ r, ph.cost r ≤ s5Bound l F kclk coef A a ha Cf Df r

/-- **The front halves' layout inside S4's** (the join the halves are built at): S4's `t, wd, tN, tD, reg, Kc, Dc`
(BridgeT's `SeedsProg2`) with the halves' scratch sets and `S5Lay`'s facts. -/
structure LayExt (Y : SeedsProg2 l F kclk coef A a ha Sw) where
  ht : 1 ≤ Y.t
  thrSc : Fin Y.t → Bool
  coreSc : Fin Y.t → Bool
  wdInj : Function.Injective Y.wd
  hND : Y.tN ≠ Y.tD
  wdN : ∀ k, Y.wd k ≠ Y.tN
  wdD : ∀ k, Y.wd k ≠ Y.tD
  in0 : ∀ k, (Y.wd k).val ≠ 0
  inN : Y.tN.val ≠ 0
  inD : Y.tD.val ≠ 0
  reg0 : Y.reg ⟨0, ht⟩ = true
  thrReg : ∀ j, thrSc j = true → Y.reg j = true
  coreReg : ∀ j, coreSc j = true → Y.reg j = true
  thrOff : ∀ j, thrSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ Y.wd k) ∧ j ≠ Y.tN ∧ j ≠ Y.tD
  coreOff : ∀ j, coreSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ Y.wd k) ∧ j ≠ Y.tN ∧ j ≠ Y.tD
  disj : ∀ j, thrSc j = true → coreSc j = false

variable {l F kclk coef A a ha Sw}

/-- **The halves' `S5Lay`** at S4's layout: its `t, wd, tN, tD, reg, Kc, Dc` ARE BridgeT's (definitionally), so the
core half's `FrontOut` at `(layOf Y E).wd` and S4's register lengths is `SeedsProg2.run`'s hypothesis at `Y`. -/
def layOf (Y : SeedsProg2 l F kclk coef A a ha Sw) (E : LayExt l F kclk coef A a ha Sw Y) : S5Lay Sw.nw :=
  ⟨Y.t, E.ht, Y.wd, Y.tN, Y.tD, Y.reg, Y.Kc, Y.Dc, E.thrSc, E.coreSc, E.wdInj, E.hND, E.wdN, E.wdD, E.in0, E.inN,
    E.inD, E.reg0, E.thrReg, E.coreReg, E.thrOff, E.coreOff, E.disj⟩

/-- **The seeds phase** (`FpPhases.seeds`): BridgeT's machine from the front's exit. -/
noncomputable def seedsPh (Y : SeedsProg2 l F kclk coef A a ha Sw) (fr : FrontPh l F kclk coef A a ha Sw Y) :
    Phase (FReq l F kclk coef A a ha) Y.t fr.ph.H fr.ph.A :=
  ⟨Y.s, Y.M, fun r => seedsShape (seedCount l F kclk coef A a ha r) (Y.tab r) (ptCount l F kclk coef A a ha r)
      (Y.pt r) (Y.ov r), fun _ _ => 0, Y.exitA fr.ph.A fr.W,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).1⟩

/-- The seeds phase's exit meets `NumDenOut` (the denominator's width from the front's `numW`). -/
theorem numDen (Y : SeedsProg2 l F kclk coef A a ha Sw) (fr : FrontPh l F kclk coef A a ha Sw Y) :
    NumDenOut l F kclk coef A a ha Y.tN Y.tD fr.W (seedsPh Y fr).H (seedsPh Y fr).A := by
  refine ⟨fun h => ?_, fun r => rfl, fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.1,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.1,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.2, fun r => ?_⟩
  · have e := fr.out.nmInj (a₁ := 0) (a₂ := 1) (by simpa using h)
    exact absurd e (by decide)
  · simpa using fr.out.numW r 1

theorem two_le_t (Y : SeedsProg2 l F kclk coef A a ha Sw) (fr : FrontPh l F kclk coef A a ha Sw Y) : 2 ≤ Y.t := by
  have hne : Y.tN ≠ Y.tD := (numDen Y fr).ne
  have h1 := Y.tN.isLt
  have h2 := Y.tD.isLt
  have h3 : Y.tN.val ≠ Y.tD.val := fun e => hne (Fin.ext e)
  omega

/-- **The three phases** from the front, BridgeT's seeds machine and X6. -/
noncomputable def phasesOf (Y : SeedsProg2 l F kclk coef A a ha Sw) (fr : FrontPh l F kclk coef A a ha Sw Y)
    (o : Fin Y.t) (ho : o.val ≠ 0) (O : OutMachine Y.t o Y.tN Y.tD) : FpPhases l F kclk coef A a ha where
  t := Y.t
  ht := two_le_t Y fr
  o := o
  ho := ho
  front := fr.ph
  seeds := seedsPh Y fr
  out := O.phase fr.W (seedsPh Y fr).H (seedsPh Y fr).A (numDen Y fr)
  outH := fun r => (O.phase_out fr.W (seedsPh Y fr).H (seedsPh Y fr).A (numDen Y fr) r).1
  outA := fun r => (O.phase_out fr.W (seedsPh Y fr).H (seedsPh Y fr).A (numDen Y fr) r).2

/-- **The phases' cost within the budget** from S6's `FitsRes` at the explicit bounds (`fits_dock`). -/
theorem phasesOf_fits (E₅ : Envelope) (c₅ : ℕ) (Y : SeedsProg2 l F kclk coef A a ha Sw)
    (fr : FrontPh l F kclk coef A a ha Sw Y) (o : Fin Y.t) (ho : o.val ≠ 0) (O : OutMachine Y.t o Y.tN Y.tD)
    (h : FitsRes l F E₅ c₅ kclk coef A a ha (s5Bound l F kclk coef A a ha fr.Cf fr.Df)
      (fun r => seedsShape (seedCount l F kclk coef A a ha r) (s5Bound l F kclk coef A a ha Y.Ct Y.Dt r)
        (ptCount l F kclk coef A a ha r) (Y.Cp * (r.1.n + 1) ^ Y.Dp) (s5Bound l F kclk coef A a ha Y.Co Y.Do r))
      (fun r => O.C * (fr.W r + 1) ^ O.D)) :
    ∀ r, (phasesOf Y fr o ho O).cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r :=
  fits_dock l F E₅ c₅ kclk coef A a ha (phasesOf Y fr o ho O) fr.Cf fr.Df Sw Y O fr.W fr.cost_le
    (fun _ => le_rfl) (fun _ => le_rfl) h

end Family

noncomputable def finalPass_of (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS l F kclk coef A a ha Sw → SeedsProg2 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (ho : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (o l F kclk coef A a ha).val ≠ 0)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha)
        (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN
        (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD)
    (E₅ : (l : Literals) → ℕ → Envelope) (CD₅ : (l : Literals) → ℕ → ℕ)
    (c₅ : (l : Literals) → (fe : ℕ) → GateFree l → ℕ)
    (fits : ∀ (l : Literals) (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ l fe) F.E →
      CD₅ l fe ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
        FitsRes l F (E₅ l fe) (c₅ l fe F) kclk coef A a ha
          (s5Bound l F kclk coef A a ha (front l F kclk coef A a ha).Cf (front l F kclk coef A a ha).Df)
          (fun r => seedsShape (seedCount l F kclk coef A a ha r)
            (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Ct
              (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dt r)
            (ptCount l F kclk coef A a ha r)
            ((bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Cp *
              (r.1.n + 1) ^ (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dp)
            (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Co
              (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Do r))
          (fun r => (O l F kclk coef A a ha).C * ((front l F kclk coef A a ha).W r + 1) ^ (O l F kclk coef A a ha).D)) :
    (l : Literals) → FinalPassLeaf l :=
  fpPlan E₅ CD₅ c₅
    (fun l F kclk coef A a ha => phasesOf (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha))
      (front l F kclk coef A a ha) (o l F kclk coef A a ha) (ho l F kclk coef A a ha) (O l F kclk coef A a ha))
    (fun l fe F hF hE hCD kclk coef A a ha => phasesOf_fits (E₅ l fe) (c₅ l fe F)
      (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)) (front l F kclk coef A a ha) (o l F kclk coef A a ha)
      (ho l F kclk coef A a ha) (O l F kclk coef A a ha) (fits l fe F hF hE hCD kclk coef A a ha))

end NearCubicWires.WireExponent3_5.FinalPass.Assembly
