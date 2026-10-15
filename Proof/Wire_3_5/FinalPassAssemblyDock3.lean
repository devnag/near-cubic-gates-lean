import Proof.Wire_3_5.FinalPassSeamsOut2

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

/-- **The front phase on the seeds phase's layout, v3**: `FrontPh2` at `SeedsProg4`. -/
structure FrontPh3 (Y : SeedsProg4 l F kclk coef A a ha Sw) where
  ph : Phase (FReq l F kclk coef A a ha) Y.t (fun _ _ => 0) (fpEntry l F kclk coef A a ha)
  W : FReq l F kclk coef A a ha → ℕ
  hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r
  out : FrontOut l F kclk coef A a ha Y.wd ![Y.tN, Y.tD] (frontWordsW2 l F kclk coef A a ha Sw)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) W
    (fun r j => if Y.reg j then Y.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Y.Dc + 1 else 0) ph.H ph.A
  Cf : ℕ
  Df : ℕ
  cost_le : ∀ r, ph.cost r ≤ s5Bound l F kclk coef A a ha Cf Df r
  Cw : ℕ
  Dw : ℕ
  W_le : ∀ r, W r ≤ Cw * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dw

/-- **The front halves' layout inside the seeds phase's, v4.** -/
structure LayExt4 (Y : SeedsProg4 l F kclk coef A a ha Sw) where
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

/-- **The halves' `S5Lay`** at the seeds phase's layout, v4. -/
def layOf4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (E : LayExt4 l F kclk coef A a ha Sw Y) : S5Lay Sw.nw :=
  ⟨Y.t, E.ht, Y.wd, Y.tN, Y.tD, Y.reg, Y.Kc, Y.Dc, E.thrSc, E.coreSc, E.wdInj, E.hND, E.wdN, E.wdD, E.in0, E.inN,
    E.inD, E.reg0, E.thrReg, E.coreReg, E.thrOff, E.coreOff, E.disj⟩

/-- **The seeds phase** (`FpPhases.seeds`), v4. -/
noncomputable def seedsPh4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (fr : FrontPh3 l F kclk coef A a ha Sw Y) :
    Phase (FReq l F kclk coef A a ha) Y.t fr.ph.H fr.ph.A :=
  ⟨Y.s, Y.M, fun r => seedsShape (seedCount l F kclk coef A a ha r) (Y.tab r) (ptCount l F kclk coef A a ha r)
      (Y.pt r) (Y.ov r), fun _ _ => 0, Y.exitA fr.ph.A fr.W,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).1⟩

/-- The seeds phase's exit meets `NumDenOut`, v4. -/
theorem numDen4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (fr : FrontPh3 l F kclk coef A a ha Sw Y) :
    NumDenOut l F kclk coef A a ha Y.tN Y.tD fr.W (seedsPh4 Y fr).H (seedsPh4 Y fr).A := by
  refine ⟨fun h => ?_, fun r => rfl, fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.1,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.1,
    fun r => (Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.2.1, fun r => ?_⟩
  · have e := fr.out.nmInj (a₁ := 0) (a₂ := 1) (by simpa using h)
    exact absurd e (by decide)
  · simpa using fr.out.numW r 1

theorem two_le_t4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (fr : FrontPh3 l F kclk coef A a ha Sw Y) : 2 ≤ Y.t := by
  have hne : Y.tN ≠ Y.tD := (numDen4 Y fr).ne
  have h1 := Y.tN.isLt
  have h2 := Y.tD.isLt
  have h3 : Y.tN.val ≠ Y.tD.val := fun e => hne (Fin.ext e)
  omega

/-- **The idle tapes are blank at the seeds phase's exit** (kept by the seeds phase, blank at the front's). -/
theorem out_blank4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (fr : FrontPh3 l F kclk coef A a ha Sw Y) (o : Fin Y.t)
    (sc : Fin Y.t → Bool) (hoI : Y.idle o = true) (hsc : ∀ j, sc j = true → Y.idle j = true) :
    ∀ r, (seedsPh4 Y fr).A r o = [] ∧ ∀ j, sc j = true → (seedsPh4 Y fr).A r j = [] := fun r =>
  ⟨((Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.2.2 o hoI).trans
      (idle_blank l F kclk coef A a ha Sw Y fr.ph.H fr.ph.A fr.W fr.out r o hoI),
    fun j hj => ((Y.run fr.ph.H fr.ph.A fr.W fr.out fr.hW r).2.2.2.2 j (hsc j hj)).trans
      (idle_blank l F kclk coef A a ha Sw Y fr.ph.H fr.ph.A fr.W fr.out r j (hsc j hj))⟩

/-- **The three phases** from the front, the seeds phase and the out machine, v4. -/
noncomputable def phasesOf4 (Y : SeedsProg4 l F kclk coef A a ha Sw) (fr : FrontPh3 l F kclk coef A a ha Sw Y)
    (o : Fin Y.t) (ho : o.val ≠ 0) (sc : Fin Y.t → Bool) (hoI : Y.idle o = true)
    (hsc : ∀ j, sc j = true → Y.idle j = true) (O : OutMachine2 Y.t o Y.tN Y.tD sc) :
    FpPhases l F kclk coef A a ha where
  t := Y.t
  ht := two_le_t4 Y fr
  o := o
  ho := ho
  front := fr.ph
  seeds := seedsPh4 Y fr
  out := O.phase fr.W (seedsPh4 Y fr).H (seedsPh4 Y fr).A (numDen4 Y fr) (out_blank4 Y fr o sc hoI hsc)
  outH := fun r => (O.phase_out fr.W (seedsPh4 Y fr).H (seedsPh4 Y fr).A (numDen4 Y fr) (out_blank4 Y fr o sc hoI hsc)
    r).1
  outA := fun r => (O.phase_out fr.W (seedsPh4 Y fr).H (seedsPh4 Y fr).A (numDen4 Y fr) (out_blank4 Y fr o sc hoI hsc)
    r).2

/-- **The phases' cost within the budget**, v4 (`fits_of`). -/
theorem phasesOf4_fits (E₅ : Envelope) (c₅ : ℕ) (Y : SeedsProg4 l F kclk coef A a ha Sw)
    (fr : FrontPh3 l F kclk coef A a ha Sw Y) (o : Fin Y.t) (ho : o.val ≠ 0) (sc : Fin Y.t → Bool)
    (hoI : Y.idle o = true) (hsc : ∀ j, sc j = true → Y.idle j = true) (O : OutMachine2 Y.t o Y.tN Y.tD sc)
    (h : FitsRes l F E₅ c₅ kclk coef A a ha (s5Bound l F kclk coef A a ha fr.Cf fr.Df)
      (fun r => seedsShape (seedCount l F kclk coef A a ha r) (s5Bound l F kclk coef A a ha Y.Ct Y.Dt r)
        (ptCount l F kclk coef A a ha r) (Y.Cp * (r.1.n + 1) ^ Y.Dp) (s5Bound l F kclk coef A a ha Y.Co Y.Do r))
      (fun r => O.C * (fr.W r + 1) ^ O.D)) :
    ∀ r, (phasesOf4 Y fr o ho sc hoI hsc O).cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r :=
  fits_of l F E₅ c₅ kclk coef A a ha (phasesOf4 Y fr o ho sc hoI hsc O) _ _ _ fr.cost_le
    (fun r => SeedsProg4.cost_le l F kclk coef A a ha Sw Y r) (fun r => O.cost_le (fr.W r)) h

end Family

noncomputable def finalPass_of3 (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (ho : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (o l F kclk coef A a ha).val ≠ 0)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (hoI : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).idle (o l F kclk coef A a ha) = true)
    (hsc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ∀ j, sc l F kclk coef A a ha j = true → (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).idle j = true)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha))
    (E₅ : (l : Literals) → ℕ → Envelope) (CD₅ : (l : Literals) → ℕ → ℕ)
    (c₅ : (l : Literals) → (fe : ℕ) → GateFree l → ℕ)
    (fits : ∀ (l : Literals) (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ l fe) F.E →
      CD₅ l fe ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
        FitsRes l F (E₅ l fe) (c₅ l fe F) kclk coef A a ha
          (s5Bound l F kclk coef A a ha (front l F kclk coef A a ha).Cf (front l F kclk coef A a ha).Df)
          (fun r => seedsShape (seedCount l F kclk coef A a ha r)
            (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Ct (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dt r)
            (ptCount l F kclk coef A a ha r)
            ((bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Cp * (r.1.n + 1) ^ (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dp)
            (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Co (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Do r))
          (fun r => (O l F kclk coef A a ha).C * ((front l F kclk coef A a ha).W r + 1) ^ (O l F kclk coef A a ha).D)) :
    (l : Literals) → FinalPassLeaf l :=
  fpPlan E₅ CD₅ c₅
    (fun l F kclk coef A a ha => phasesOf4 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)) (front l F kclk coef A a ha) (o l F kclk coef A a ha) (ho l F kclk coef A a ha) (sc l F kclk coef A a ha) (hoI l F kclk coef A a ha) (hsc l F kclk coef A a ha)
      (O l F kclk coef A a ha))
    (fun l fe F hF hE hCD kclk coef A a ha => phasesOf4_fits (E₅ l fe) (c₅ l fe F) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)) (front l F kclk coef A a ha) (o l F kclk coef A a ha)
      (ho l F kclk coef A a ha) (sc l F kclk coef A a ha) (hoI l F kclk coef A a ha) (hsc l F kclk coef A a ha) (O l F kclk coef A a ha) (fits l fe F hF hE hCD kclk coef A a ha))

end NearCubicWires.WireExponent3_5.FinalPass.Assembly

