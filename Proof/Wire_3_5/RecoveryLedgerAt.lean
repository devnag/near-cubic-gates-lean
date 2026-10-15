import Proof.Wire_3_5.RecoveryBudget

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)

structure GateRel (l : Literals) (G : Split.Gate) : Prop where
  apad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad
  sp : G.row.sp = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l)
  cpar : G.row.cap.Cpar = 2
  betaInv : 1 ≤ G.row.cap.betaInv
  beta : 1 / (G.row.cap.betaInv : ℝ) ≤ ((gateCParams1 l).β : ℝ)
  aT : 1 ≤ G.row.cap.aT
  aS : 1 ≤ G.row.cap.aS
  name : 2 ≤ G.nameCount
  kdeg : 2 ≤ G.kDeg
  desc : 26 ≤ G.descDeg
  carrier : 26 ≤ G.carrierDeg

section LedgerAt
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

include hG in
/-- **The Case-2 ledger at one source length** from the per-length facts at `q = q(N)`. -/
noncomputable def ledger_at (P : FusedPrimitive (G.inputs kclk coef A a ha)) (m : Mode) {N : ℕ} (z : BitInput N)
    (oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N))
    (q : ℕ) (hq : ((recSetup l G kclk coef A a ha).request z oracle).arity = q) (hq1 : 1 ≤ q)
    (hstar : Even (rowBr G.row.cr q) ∧ 2 ≤ rowBr G.row.cr q ∧ 4 * rowBr G.row.cr q ≤ q ∧
      Lq q ≤ starWidth (rowBr G.row.cr q) q ∧ starWidth (rowBr G.row.cr q) q ≤ Lq q ^ G.kDeg)
    (hfit : (G.budget kclk coef A a ha).FitsAt q)
    (W : ℕ) (hW : (W : ℝ) ≤ wireCap G.row.cap m q) (hW4 : W + 1 ≤ 2 * (q + 1) ^ 4) (hWq : q ≤ W)
    (hsp : G.row.sp q ≤ q)
    (Ldesc : ℕ) (hLd : Ldesc ≤ (q + 1) ^ 26) (hLd1 : 1 ≤ Ldesc)
    (hξ : 1 / (2 : ℝ) ^ (G.filterErrDeg * Nat.clog 2 (q + 2)) ≤ ((gateCParams1 l).ξ : ℝ))
    (hD : (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(G.D : ℝ)) ≤
      ((gateParams1 l).eps0 : ℝ))
    (Ko Kc : ℕ) (hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko)
    (hcodeC : ∀ C : m.Circuit q, m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc)
    (hbudget : 1 + Ko + (((recSetup l G kclk coef A a ha).pcppOf z oracle).systematicBits +
      ((recSetup l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits) * (G.row.sp q * (4 + Kc)) ≤ N / 16) :
    CaseTwoLedger (recSetup l G kclk coef A a ha) z oracle m P (gateCParams1 l)
      (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) W Ldesc := by
  have hδ := gateDelta_pos l
  have hCδ := gateCδ1_pos l
  have hStar : (G.inputs kclk coef A a ha).StarAt ((recSetup l G kclk coef A a ha).request z oracle).arity := by
    rw [hq]; exact hstar
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hcarr : (q + 1) ^ 26 ≤ (q + 1) ^ G.carrierDeg := Nat.pow_le_pow_right (by omega) hG.carrier
  have hdescd : (q + 1) ^ 26 ≤ (q + 1) ^ G.descDeg := Nat.pow_le_pow_right (by omega) hG.desc
  have h4 : (q + 1) ^ 4 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc' : ∀ C : m.Circuit ((recSetup l G kclk coef A a ha).request z oracle).arity,
      m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc := by
    rw [hq]; exact hcodeC
  exact
  { hA := by
      show _ ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup l G kclk coef A a ha).request z oracle).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact massCap_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hΛ := by
      show 1 ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup l G kclk coef A a ha).request z oracle).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact one_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hs := by
      show 1 ≤ G.row.sp ((recSetup l G kclk coef A a ha).request z oracle).arity
      rw [hq, hG.sp]
      exact one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hsδ := gridMass_hsδ (gateCδ1 l) G.row.sp _ hδ.le (gateCδ1_spec l) _
    hStar := hStar
    hFit := by rw [hq]; exact hfit
    hname := hG.name
    hdesc := by rw [hq]; exact hLd.trans hdescd
    hdescK := by
      show m.descriptionBits (unionConstAtom m _) ≤ _
      rw [unionConstAtom_descriptionBits]
      exact Nat.one_le_pow _ _ (by omega)
    hdescP := fun Sp => by
      show m.descriptionBits (unionParityAtom m _ Sp) ≤ _
      refine (unionParityAtom_descriptionBits_le m _ Sp).trans ?_
      rw [hq]; exact h4.trans hdescd
    hKP := fun Sp => by
      show (m.gates (unionParityAtom m _ Sp)).length ≤ W
      refine (unionParityAtom_gates_length m _ Sp).trans ?_
      rw [hq]; exact hWq
    hlen := by
      rw [hq]
      have h1 : (G.row.sp q + 1) * W ≤ (q + 1) * (2 * (q + 1) ^ 4) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (q + 1) * (2 * (q + 1) ^ 4) ≤ (q + 1) ^ 26 := by
        have e : (q + 1) * (2 * (q + 1) ^ 4) = 2 * (q + 1) ^ 5 := by ring
        have h5 : 2 * (q + 1) ^ 5 ≤ (q + 1) ^ 6 := by
          calc 2 * (q + 1) ^ 5 ≤ (q + 1) * (q + 1) ^ 5 := Nat.mul_le_mul_right _ (by omega)
            _ = (q + 1) ^ 6 := by ring
        have h6 : (q + 1) ^ 6 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      exact (h1.trans h2).trans hcarr
    hbC := by rw [hq]; exact hLd.trans hcarr
    hbP := fun Sp gt hgt => by
      have h1 := unionParityAtom_encodingBits_le m _ Sp gt hgt
      have key : ∀ n : ℕ, 2 * n + 1 ≤ (n + 1) ^ G.carrierDeg := fun n => by
        have h2 : 2 * n + 1 ≤ (n + 1) ^ 2 := by
          calc 2 * n + 1 ≤ n * n + 2 * n + 1 := by omega
            _ = (n + 1) ^ 2 := by ring
        exact h2.trans (Nat.pow_le_pow_right (by omega) (by have := hG.carrier; omega))
      exact h1.trans (key _)
    Cpar := 2
    hCpar := by norm_num
    hwP := fun Sp => by
      have h1 := unionParityAtom_wires_le m ((recSetup l G kclk coef A a ha).request z oracle).arity Sp
      have h2 : (((m.gates (unionParityAtom m _ Sp)).wires : ℕ) : ℝ) ≤
          ((2 * ((recSetup l G kclk coef A a ha).request z oracle).arity ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2
    hcap := by
      have hq1' : 1 ≤ ((recSetup l G kclk coef A a ha).request z oracle).arity := by rw [hq]; exact hq1
      have hW' : (W : ℝ) ≤ wireCap G.row.cap m ((recSetup l G kclk coef A a ha).request z oracle).arity := by
        rw [hq]; exact hW
      have hc := hcap_of G.row.cap m ((G.inputs kclk coef A a ha).starParams _ hStar)
        (G.row.sp ((recSetup l G kclk coef A a ha).request z oracle).arity) W _ hq1' rfl
        hG.betaInv ((gateCParams1 l).β : ℝ) hG.beta hW'
      rw [hG.cpar] at hc
      push_cast at hc
      exact hc
    hξ := by rw [hq]; exact hξ
    hD := by
      show (1 + ((gridMassOf (gateCδ1 l) G.row.sp _ : ℚ) : ℝ)) ^ 4 * _ ≤ _
      rw [hq, hG.sp, gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q]
      exact_mod_cast hD
    Ko := Ko
    Ks := 4
    Kc := Kc
    hO := hO
    hKs := intWord_grid_le
    hcodeC := hc'
    hcodeK := hc' _ (by
      show m.descriptionBits (unionConstAtom m _) ≤ Ldesc
      rw [unionConstAtom_descriptionBits]; exact hLd1)
    hbudget := by
      have e : (recSetup l G kclk coef A a ha).gridSize ((recSetup l G kclk coef A a ha).request z oracle).arity =
          G.row.sp q := by
        show G.row.sp _ = _
        rw [hq]
      rw [e]; exact hbudget }
