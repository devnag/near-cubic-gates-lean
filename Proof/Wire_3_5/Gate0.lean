import Proof.Wire_3_5.Split
import Proof.Wire_3_5.RecoveryLedgerAt

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Transfer

/-- The gate constants only the primitive's assembly can fix. -/
structure GateFree (l : Literals) where
  E : Envelope
  hσ : gateApad l + 1 ≤ E.sigma
  CD : ℕ
  cr : ℕ
  cr_pos : 1 ≤ cr
  filterErrDeg : ℕ
  hG7 : 1 + 2 ≤ filterErrDeg

variable (l : Literals)

/-- `β⁻¹ = ⌈100/ε⌉`. -/
noncomputable def gateBetaInv : ℕ := ⌈(100 : ℚ) / gateEps l⌉₊

noncomputable def gateCap : CapParams := ⟨1, 1, gateBetaInv l, 2⟩

/-- The sparse count `s(q)` and its `s^8 ≤ C_sp L³` witness (`rowBSparse_pow8_le`). -/
noncomputable def gateSp : ℕ → ℕ := rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l)

noncomputable def gateCsp : ℕ := Classical.choose (rowBSparse_pow8_le (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l))

theorem gateSp_le (q : ℕ) : gateSp l q ^ 8 ≤ gateCsp l * Lq q ^ 3 :=
  Classical.choose_spec (rowBSparse_pow8_le (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l)) q

/-- The row-B ledger constants at the gate. -/
noncomputable def gateRow (F : GateFree l) : RowBParams where
  cap := gateCap l
  CD := F.CD
  cr := F.cr
  cr_pos := F.cr_pos
  Csp := gateCsp l
  sp := gateSp l
  sp_le := gateSp_le l

/-- **The concrete gate.** -/
noncomputable def gate0 (F : GateFree l) : Gate where
  E := F.E
  Apad := gateApad l
  hσ := F.hσ
  row := gateRow l F
  D := 1
  D_pos := Nat.one_pos
  kDeg := 2
  descDeg := 26
  nameCount := 2
  carrierDeg := 26
  filterErrDeg := F.filterErrDeg
  hG7 := F.hG7
  alg := Classical.choice l.eightSources.decomposition

theorem one_div_betaInv_le : 1 / ((gateBetaInv l : ℕ) : ℝ) ≤ ((gateCParams1 l).β : ℝ) := by
  have hε : (0 : ℚ) < gateEps l := gateEps_pos l
  have hc : (100 : ℚ) / gateEps l ≤ (gateBetaInv l : ℚ) := Nat.le_ceil _
  have hpos : (0 : ℚ) < 100 / gateEps l := div_pos (by norm_num) hε
  have hb : (0 : ℚ) < (gateBetaInv l : ℚ) := lt_of_lt_of_le hpos hc
  rw [gateBeta_eq]
  have key : (1 : ℚ) / (gateBetaInv l : ℚ) ≤ gateEps l / 100 := by
    rw [div_le_div_iff₀ hb (by norm_num)]
    have := (div_le_iff₀ hε).1 hc
    linarith
  have h := (Rat.cast_le (K := ℝ)).2 key
  push_cast at h ⊢
  exact h

theorem one_le_betaInv : 1 ≤ gateBetaInv l := by
  have hε : (0 : ℚ) < gateEps l := gateEps_pos l
  have h1 : gateEps l ≤ 1 := gateEps_le_one l
  have hc : (100 : ℚ) / gateEps l ≤ (gateBetaInv l : ℚ) := Nat.le_ceil _
  have h100 : (1 : ℚ) ≤ 100 / gateEps l := by
    rw [le_div_iff₀ hε]; linarith
  exact_mod_cast le_trans h100 hc

theorem gateRel_gate0 (F : GateFree l) : GateRel l (gate0 l F) where
  apad := le_refl _
  sp := rfl
  cpar := rfl
  betaInv := one_le_betaInv l
  beta := one_div_betaInv_le l
  aT := le_refl _
  aS := le_refl _
  name := le_refl _
  kdeg := le_refl _
  desc := le_refl _
  carrier := le_refl _

end NearCubicWires.WireExponent3_5.Split
