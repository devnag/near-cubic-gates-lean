import Proof.Wire_3_5.UnionSetup
import Proof.Wire_3_5.LiteralSources

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

section Constants
variable (l : Literals)

theorem gap_pos : 0 < (gatePCPP l).completeness - (gatePCPP l).soundness := by
  have := (gatePCPP l).gap; linarith

theorem exists_eps : ∃ ε : ℚ, (0 : ℝ) < ε ∧
    (ε : ℝ) < min 1 (((gatePCPP l).completeness - (gatePCPP l).soundness) / 1000) :=
  exists_rat_btwn (by have := gap_pos l; positivity)

theorem exists_tau : ∃ τ : ℚ, ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 < τ ∧
    (τ : ℝ) < ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 +
      ((gatePCPP l).completeness - (gatePCPP l).soundness) / 10 :=
  exists_rat_btwn (by have := gap_pos l; linarith)

/-- The rational `ε` of the constants. -/
noncomputable def gateEps : ℚ := Classical.choose (exists_eps l)
/-- The rational threshold `τ`. -/
noncomputable def gateTau : ℚ := Classical.choose (exists_tau l)

theorem gateEps_pos : 0 < gateEps l := by
  have := (Classical.choose_spec (exists_eps l)).1
  unfold gateEps; exact_mod_cast this
theorem gateEps_le_one : gateEps l ≤ 1 := by
  have := lt_of_lt_of_le (Classical.choose_spec (exists_eps l)).2 (min_le_left _ _)
  unfold gateEps; exact_mod_cast this.le
theorem gateEps_le_gap : (gateEps l : ℝ) ≤ ((gatePCPP l).completeness - (gatePCPP l).soundness) / 1000 :=
  (lt_of_lt_of_le (Classical.choose_spec (exists_eps l)).2 (min_le_right _ _)).le
theorem gateTau_ge : ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 ≤ (gateTau l : ℝ) :=
  (Classical.choose_spec (exists_tau l)).1.le
theorem gateTau_le : (gateTau l : ℝ) ≤ ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 +
    ((gatePCPP l).completeness - (gatePCPP l).soundness) / 10 :=
  (Classical.choose_spec (exists_tau l)).2.le

/-- **The soundness constants**, explicit: `v₀ = ε²/10⁴`, `ε₀ = v₀/2`, outer error `ε/6`, threshold `τ`. -/
noncomputable def gateParams1 : MaskedSoundnessParameters (gatePCPP l).completeness (gatePCPP l).soundness :=
  unionSoundParams (gatePCPP l).soundnessPositive.le (gateEps l) (gateEps_pos l) (gateEps_le_one l)
    (gateEps_le_gap l) (gateTau l) (gateTau_ge l)

/-- **The completeness constants**, explicit: `ζ = (v₀/10)²`, `δ = v₀/100`, `β = ξ = ε/100`. -/
noncomputable def gateCParams1 : MaskedCompletenessParameters (gateParams1 l) :=
  unionCompleteParams (gatePCPP l).soundnessPositive.le (gateEps l) (gateEps_pos l) (gateEps_le_one l)
    (gateEps_le_gap l) (gateTau l) (gateTau_ge l) (gateTau_le l)

theorem gateZeta_eq : (gateCParams1 l).ζ = ((gateEps l ^ 2 / 10000) / 10) ^ 2 := rfl
theorem gateDelta_eq : (gateCParams1 l).δ = (gateEps l ^ 2 / 10000) / 100 := rfl
theorem gateBeta_eq : (gateCParams1 l).β = gateEps l / 100 := rfl

theorem gateZeta_pos : 0 < (gateCParams1 l).ζ := by
  rw [gateZeta_eq]; have := gateEps_pos l; positivity

theorem gateZeta_lt : (gateCParams1 l).ζ < 1 / 2 := by
  rw [gateZeta_eq]
  have h0 := gateEps_pos l
  have h1 := gateEps_le_one l
  have h2 : gateEps l ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  have h3 : (gateEps l ^ 2 / 10000 / 10) ≤ 1 / 100000 := by
    have : gateEps l ^ 2 / 10000 / 10 = gateEps l ^ 2 / 100000 := by ring
    rw [this]; exact div_le_div_of_nonneg_right h2 (by norm_num)
  have h4 : 0 ≤ gateEps l ^ 2 / 10000 / 10 := by positivity
  nlinarith

theorem gateDelta_pos : 0 < (gateCParams1 l).δ := by
  rw [gateDelta_eq]; have := gateEps_pos l; positivity

/-- `C_δ = ⌈5/δ²⌉` at the explicit `δ`. -/
noncomputable def gateCδ1 : ℕ := ⌈(5 : ℚ) / (gateCParams1 l).δ ^ 2⌉₊

theorem gateCδ1_spec : 5 ≤ ((gateCδ1 l : ℕ) : ℚ) * (gateCParams1 l).δ ^ 2 := by
  have hpos : 0 < (gateCParams1 l).δ ^ 2 := by have := gateDelta_pos l; positivity
  have hc : (5 : ℚ) / (gateCParams1 l).δ ^ 2 ≤ (gateCδ1 l : ℚ) := Nat.le_ceil _
  calc (5 : ℚ) = 5 / (gateCParams1 l).δ ^ 2 * (gateCParams1 l).δ ^ 2 := (div_mul_cancel₀ 5 hpos.ne').symm
    _ ≤ (gateCδ1 l : ℚ) * (gateCParams1 l).δ ^ 2 := by gcongr

theorem gateCδ1_pos : 1 ≤ gateCδ1 l := by
  have h := gateCδ1_spec l
  rcases Nat.eq_zero_or_pos (gateCδ1 l) with h0 | h0
  · rw [h0] at h; norm_num at h
  · exact h0

noncomputable def recOracleDeg : ℕ := 17 * l.eightSources.amplification.stvExponent

end Constants

variable (l : Literals) (G : Split.Gate)

/-- **The pinned union setup `S₁`**: `S₀` with the explicit constants and the oracle degree `17·c_STV`. -/
noncomputable def unionSetupS1 : G.Setup := fun kclk coef A a ha L hL =>
  setupOfResult (G.inputs kclk coef A a ha) L (hierarchyOf hL) (Classical.choose_spec hL)
    (hierarchyPCP l (hierarchyOf hL)).data (paddedWidth l G (hierarchyOf hL)) (fun _ => le_max_left _ _) (gatePCPP l)
    (recOracleDeg l) (gateParams1 l) (gridMassOf (gateCδ1 l) G.row.sp) (fun _ => by unfold gridMassOf; positivity)
    G.row.sp

theorem unionSetupS1_params (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) : (unionSetupS1 l G kclk coef A a ha L hL).params = gateParams1 l := rfl

theorem unionSetupS1_G (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) : (unionSetupS1 l G kclk coef A a ha L hL).G = recOracleDeg l := rfl

/-- The padded width is the ledger's `q(N)` eventually. -/
theorem unionSetupS1_width (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∃ N₀, ∀ N, N₀ ≤ N →
      (unionSetupS1 l G kclk coef A a ha L hL).pcp.nativeWidth N = Ledger.nativeWidth kclk G.Apad N :=
  unionSetupS0_width l G (recOracleDeg l) kclk coef A a ha L hL hApad

end NearCubicWires.WireExponent3_5.Transfer
