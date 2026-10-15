import Proof.Wire_3_5.FinalPassSeamsFits

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

section Uni
variable (l : Literals)

/-- **Uniform constants of a stage family**, in `FinalPassLeaf`'s order of choice. -/
def StageU (S : (F : GateFree l) → (kclk coef A a : ℕ) → a ≤ kclk + 1 → Type)
    (deg : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ)
    (cf : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ) : Type :=
  ∀ fe : ℕ, Σ D₀ : ℕ, Σ E₀ : Envelope, Σ CD₀ : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E₀ F.E →
    CD₀ ≤ F.CD → Σ C₀ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      { x : S F kclk coef A a ha // deg x ≤ D₀ ∧ cf x ≤ C₀ }

variable {l}

/-- **Two uniform families side by side**: exponents `max`, coefficients `+`, floors `envMax` / `max`. -/
def StageU.pair {S₁ S₂ : (F : GateFree l) → (kclk coef A a : ℕ) → a ≤ kclk + 1 → Type}
    {deg₁ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₁ F kclk coef A a ha → ℕ}
    {cf₁ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₁ F kclk coef A a ha → ℕ}
    {deg₂ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₂ F kclk coef A a ha → ℕ}
    {cf₂ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₂ F kclk coef A a ha → ℕ}
    (U₁ : StageU l S₁ deg₁ cf₁) (U₂ : StageU l S₂ deg₂ cf₂) :
    StageU l (fun F kclk coef A a ha => S₁ F kclk coef A a ha × S₂ F kclk coef A a ha)
      (fun x => max (deg₁ x.1) (deg₂ x.2)) (fun x => cf₁ x.1 + cf₂ x.2) :=
  fun fe =>
    let V₁ := U₁ fe
    let V₂ := U₂ fe
    ⟨max V₁.1 V₂.1, envMax V₁.2.1 V₂.2.1, max V₁.2.2.1 V₂.2.2.1, fun F hF hE hCD =>
      let W₁ := V₁.2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE) (le_trans (le_max_left _ _) hCD)
      let W₂ := V₂.2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE) (le_trans (le_max_right _ _) hCD)
      ⟨W₁.1 + W₂.1, fun kclk coef A a ha =>
        ⟨((W₁.2 kclk coef A a ha).1, (W₂.2 kclk coef A a ha).1),
          max_le_max (W₁.2 kclk coef A a ha).2.1 (W₂.2 kclk coef A a ha).2.1,
          Nat.add_le_add (W₁.2 kclk coef A a ha).2.2 (W₂.2 kclk coef A a ha).2.2⟩⟩⟩

/-- **The instance and its bounds at `fpPlan`'s binders.** -/
theorem StageU.at {S : (F : GateFree l) → (kclk coef A a : ℕ) → a ≤ kclk + 1 → Type}
    {deg : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ}
    {cf : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ}
    (U : StageU l S deg cf) (fe : ℕ) (F : GateFree l) (hF : F.filterErrDeg = fe) (hE : ClassLE (U fe).2.1 F.E)
    (hCD : (U fe).2.2.1 ≤ F.CD) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    deg (((U fe).2.2.2 F hF hE hCD).2 kclk coef A a ha).1 ≤ (U fe).1 ∧
      cf (((U fe).2.2.2 F hF hE hCD).2 kclk coef A a ha).1 ≤ ((U fe).2.2.2 F hF hE hCD).1 :=
  (((U fe).2.2.2 F hF hE hCD).2 kclk coef A a ha).2

end Uni

/-! ## Dock: the seeds phase at uniform constants -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- The seeds phase's exponent: the largest of its three. -/
def seedsDeg (X : SeedsProg2 l F kclk coef A a ha Sw) : ℕ := max X.Dp (max X.Dt X.Do)

/-- The seeds phase's coefficient: the sum of its three. -/
def seedsCf (X : SeedsProg2 l F kclk coef A a ha Sw) : ℕ := X.Cp + X.Ct + X.Co

theorem pow_mono_le (b D D' : ℕ) (hb : 1 ≤ b) (h : D ≤ D') : b ^ D ≤ b ^ D' := Nat.pow_le_pow_right hb h

/-- **The seeds phase's cost at uniform constants** `D₀ ≥ seedsDeg`, `C₀ ≥ seedsCf`. -/
theorem SeedsProg2.cost_le_uni (X : SeedsProg2 l F kclk coef A a ha Sw) (D₀ C₀ : ℕ) (hD : seedsDeg l F kclk coef A a ha Sw X ≤ D₀)
    (hC : seedsCf l F kclk coef A a ha Sw X ≤ C₀) (r : FReq l F kclk coef A a ha) :
    seedsShape (seedCount l F kclk coef A a ha r) (X.tab r) (ptCount l F kclk coef A a ha r) (X.pt r) (X.ov r) ≤
      seedsShape (seedCount l F kclk coef A a ha r) (s5Bound l F kclk coef A a ha C₀ D₀ r)
        (ptCount l F kclk coef A a ha r) (C₀ * (r.1.n + 1) ^ D₀) (s5Bound l F kclk coef A a ha C₀ D₀ r) := by
  unfold seedsDeg at hD
  unfold seedsCf at hC
  have h0 := X.cost_le l F kclk coef A a ha Sw r
  have ht := s5Bound_mono l F kclk coef A a ha X.Ct C₀ X.Dt D₀ (by omega) (by omega) r
  have ho := s5Bound_mono l F kclk coef A a ha X.Co C₀ X.Do D₀ (by omega) (by omega) r
  have hp : X.Cp * (r.1.n + 1) ^ X.Dp ≤ C₀ * (r.1.n + 1) ^ D₀ :=
    Nat.mul_le_mul (by omega) (pow_mono_le (r.1.n + 1) X.Dp D₀ (by omega) (by omega))
  refine le_trans h0 ?_
  unfold seedsShape
  have h1 := Nat.mul_le_mul_left (seedCount l F kclk coef A a ha r) ht
  have h2 := Nat.mul_le_mul_left (ptCount l F kclk coef A a ha r) hp
  omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
