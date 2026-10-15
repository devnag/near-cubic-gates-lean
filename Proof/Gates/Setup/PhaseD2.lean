import Proof.Gates.Setup.PhaseD1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val)
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK)

noncomputable section

/-! ## The clause width and the gadget count -/

theorem two_le_pow_add (q d : ℕ) : d < (q + 2) ^ d := by
  calc d < 2 ^ d := Nat.lt_two_pow_self
    _ ≤ (q + 2) ^ d := Nat.pow_le_pow_left (by omega) d

theorem le_pow_clauseWidth (d q : ℕ) : (q + 2) ^ d ≤ 2 ^ clauseWidth d q := Nat.le_pow_clog (by norm_num) _

theorem clauseWidth_eq (d q : ℕ) : clauseWidth d q = ((q + 2) ^ d - 1).size := by
  unfold clauseWidth; exact Recovery.TableSem.clog_eq_size _

/-- `rCL := clauseWidth d q` from `q` in `R 6` (scratch `69 … 75`, `dS`). -/
def clA {ns : ℕ} (d : ℕ) : WMX ns nrW :=
  .seq (.wm (.seq (Codec.dupR (regE 6) 69 dS) (.seq (.inc 69) (.seq (.inc 69) (.inc 70)))))
  (.seq (EncSetup.powW 69 70 71 72 73 d)
  (.seq (WMX.dec 70)
  (.seq (Recovery.HTParts.sizeW 70 74 75 rCL)
  (.wm (WM.clear 69)))))

theorem clA1_exec {ns cap : ℕ} (q : ℕ) (σ : WState ns nrW) (hq : σ.val (regE 6) = q) (z69 : σ.val 69 = 0)
    (z70 : σ.val 70 = 0) (zd : σ.val dS = 0) (hcap : q + 3 ≤ cap) :
    WExec cap (.seq (Codec.dupR (regE 6) 69 dS) (.seq (.inc 69) (.seq (.inc 69) (.inc 70)))) σ
      ((σ.setv 69 (q + 2)).setv 70 1) (18 * q + 3 + 1 + (3 + 1 + (3 + 1 + 3))) := by
  have e1 := Codec.dupR_spec cap (regE 6) 69 dS (by decide) (by decide) (by decide) σ zd (by rw [hq, z69]; omega)
  rw [hq, z69, Nat.zero_add] at e1
  have e2 := WExec.inc (cap := cap) (69 : Fin nrW) (σ.setv 69 q) (by simp; omega)
  have e3 := WExec.inc (cap := cap) (69 : Fin nrW) ((σ.setv 69 q).setv 69 ((σ.setv 69 q).val 69 + 1)) (by simp; omega)
  have e4 := WExec.inc (cap := cap) (70 : Fin nrW) (((σ.setv 69 q).setv 69 ((σ.setv 69 q).val 69 + 1)).setv 69
    (((σ.setv 69 q).setv 69 ((σ.setv 69 q).val 69 + 1)).val 69 + 1))
    (by simp (config := { decide := true }) [Function.update_apply, z70]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
  simp (config := { decide := true }) [LitDecode.setv_setv, Function.update_apply, z70]

theorem clA_exec {ns cap : ℕ} (d q : ℕ) (σ : WState ns nrW) (hq : σ.val (regE 6) = q)
    (hz : ∀ r ∈ ([69, 70, 71, 72, 73, 74, 75, rCL, dS] : List (Fin nrW)), σ.val r = 0)
    (hcap : 3 * (2 ^ clauseWidth d q + q + 2) ^ 2 ≤ cap) :
    WXExec cap (clA d) σ (σ.setv rCL (clauseWidth d q)) (1000 * (2 ^ clauseWidth d q + q + 2) ^ 3) := by
  have z : ∀ r ∈ ([69, 70, 71, 72, 73, 74, 75, rCL, dS] : List (Fin nrW)), σ.val r = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at z
  obtain ⟨z69, z70, z71, z72, z73, z74, z75, zCL, zd⟩ := z
  obtain ⟨V, hV⟩ : ∃ V, V = (q + 2) ^ d := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ clauseWidth d q := ⟨_, rfl⟩
  rw [← hM] at hcap ⊢
  have hVM : V ≤ M := by rw [hV, hM]; exact le_pow_clauseWidth d q
  have hdV : d < V := by rw [hV]; exact two_le_pow_add q d
  have hcls : clauseWidth d q = (V - 1).size := by rw [hV]; exact clauseWidth_eq d q
  have hsize : (V - 1).size ≤ V := Nat.size_le.mpr (by have := Nat.lt_two_pow_self (n := V); omega)
  have hsq : (M + q + 2) ^ 2 ≥ (M + q + 2) := Nat.le_self_pow (by norm_num) _
  have hMM : M * M ≤ (M + q + 2) ^ 2 := by nlinarith
  have hVV : 2 * V + V * V ≤ cap := by nlinarith
  have e1 := clA1_exec (cap := cap) q σ hq z69 z70 zd (by nlinarith)
  set τ := (σ.setv 69 (q + 2)).setv 70 1 with hτ
  have e5 := EncSetup.powW_spec (cap := cap) (X := (69 : Fin nrW)) (Y := 70) (Z := 71) (A2 := 72) (T := 73)
    (by decide) V d τ
    (by simp (config := { decide := true }) [hτ, Function.update_apply, z71])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, z72])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, z73])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, hV])
    (by simp (config := { decide := true }) [hτ, Function.update_apply]) hVV
  have h5 : τ.setv 70 (τ.val 70 * τ.val 69 ^ d) = τ.setv 70 V := by
    simp (config := { decide := true }) [hτ, Function.update_apply, hV]
  rw [h5] at e5
  have e6 := WXExec.dec (cap := cap) (70 : Fin nrW) (τ.setv 70 V) (by simp; nlinarith)
  rw [show (τ.setv 70 V).setv 70 ((τ.setv 70 V).val 70 - 1) = τ.setv 70 (V - 1) by
    simp [LitDecode.setv_setv]] at e6
  have e7 := Recovery.HTParts.sizeW_exec (cap := cap) (X := (70 : Fin nrW)) (H := 74) (B := 75) (C := rCL)
    (by decide) V (by nlinarith) (V - 1) (τ.setv 70 (V - 1)) (by omega) (by simp)
    (by simp (config := { decide := true }) [hτ, Function.update_apply, z74])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, z75])
    (by simp (config := { decide := true }) [hτ, Function.update_apply, zCL]; nlinarith)
  rw [show ((τ.setv 70 (V - 1)).setv 70 0).setv rCL ((τ.setv 70 (V - 1)).val rCL + (V - 1).size) =
    (τ.setv 70 0).setv rCL (V - 1).size by
      simp (config := { decide := true }) [LitDecode.setv_setv, hτ, Function.update_apply, zCL]] at e7
  have e8 := WireExponent3_5.FinalPass.Tm.wclear_spec (cap := cap) (69 : Fin nrW) (q + 2)
    ((τ.setv 70 0).setv rCL (V - 1).size)
    (by simp (config := { decide := true }) [hτ, Function.update_apply])
    (by simp (config := { decide := true }) [hτ, Function.update_apply]; nlinarith)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7 (WXExec.wm e8)))))
    ?_ ?_
  · clear e1 e5 e6 e7 e8
    apply WState.eq <;> try rfl
    funext r
    simp only [hτ, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all (config := { decide := true })
  · simp only [EncSetup.powCost]
    obtain ⟨K, hK⟩ : ∃ K, K = M + q + 2 := ⟨_, rfl⟩
    rw [← hK]
    have hVK : V ≤ K := by omega
    have hdK : d ≤ K := by omega
    have hsK : (V - 1).size ≤ K := by omega
    have hqK : q ≤ K := by omega
    have hK1 : 1 ≤ K := by omega
    have hX : 40 * V * V + 40 * V + 20 ≤ 40 * K * K + 40 * K + 20 := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 40 hVK) hVK
      omega
    have h3 : K * K ≤ K ^ 3 := by
      calc K * K = K ^ 2 := (sq K).symm
        _ ≤ K ^ 3 := Nat.pow_le_pow_right hK1 (by norm_num)
    have h4 : K ≤ K ^ 3 := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 3 := Nat.pow_le_pow_right hK1 (by norm_num)
    have hK3 : K * (K * K) = K ^ 3 := by ring
    have h1 : d * (40 * V * V + 40 * V + 20) ≤ 100 * K ^ 3 := by
      calc d * (40 * V * V + 40 * V + 20) ≤ K * (40 * K * K + 40 * K + 20) := Nat.mul_le_mul hdK hX
        _ = 40 * (K * (K * K)) + 40 * (K * K) + 20 * K := by ring
        _ ≤ 100 * K ^ 3 := by rw [hK3]; omega
    have h2 : (V - 1).size * (12 * V + 30) ≤ 42 * K ^ 3 := by
      calc (V - 1).size * (12 * V + 30) ≤ K * (12 * K + 30) := Nat.mul_le_mul hsK (by omega)
        _ = 12 * (K * K) + 30 * K := by ring
        _ ≤ 42 * K ^ 3 := by omega
    omega

/-- `rM := 2^{rCL}`, `rLC := rM` (scratch `76 … 78`, `dS`). -/
def clB {ns : ℕ} : WMX ns nrW :=
  .seq (.wm (.seq (.inc rM) (Codec.dupR rCL 76 dS)))
  (.seq (ClauseFront.dblW rM 76 77 78)
  (.wm (Codec.dupR rM rLC dS)))

theorem clB_exec {ns cap : ℕ} (cl : ℕ) (σ : WState ns nrW) (hcl : σ.val rCL = cl)
    (hz : ∀ r ∈ ([rM, 76, 77, 78, rLC, dS] : List (Fin nrW)), σ.val r = 0) (hcap : 4 * 2 ^ cl + 4 ≤ cap) :
    WXExec cap clB σ ((σ.setv rM (2 ^ cl)).setv rLC (2 ^ cl)) (100 * (2 ^ cl + 1) ^ 2) := by
  have z : ∀ r ∈ ([rM, 76, 77, 78, rLC, dS] : List (Fin nrW)), σ.val r = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at z
  obtain ⟨zM, z76, z77, z78, zLC, zd⟩ := z
  have hclM : cl < 2 ^ cl := Nat.lt_two_pow_self
  have e1 := WExec.inc (cap := cap) rM σ (by rw [zM]; omega)
  rw [zM, Nat.zero_add] at e1
  have e2 := Codec.dupR_spec cap rCL 76 dS (by decide) (by decide) (by decide) (σ.setv rM 1)
    (by simp (config := { decide := true }) [Function.update_apply, zd])
    (by simp (config := { decide := true }) [Function.update_apply, z76, hcl]; omega)
  rw [show (σ.setv rM 1).setv 76 ((σ.setv rM 1).val 76 + (σ.setv rM 1).val rCL) = (σ.setv rM 1).setv 76 cl by
    simp (config := { decide := true }) [Function.update_apply, z76, hcl]] at e2
  have e3 := ClauseFront.dblW_exec (cap := cap) (M := rM) (K := 76) (Q := 77) (T := 78) (by decide) (2 ^ cl)
    (by omega) cl ((σ.setv rM 1).setv 76 cl) (by simp) (by omega)
    (by simp (config := { decide := true }) [Function.update_apply, z77])
    (by simp (config := { decide := true }) [Function.update_apply, z78])
    (by simp (config := { decide := true }) [Function.update_apply])
  rw [show (((σ.setv rM 1).setv 76 cl).setv 76 0).setv rM (((σ.setv rM 1).setv 76 cl).val rM * 2 ^ cl) =
    σ.setv rM (2 ^ cl) by
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all (config := { decide := true })] at e3
  have e4 := Codec.dupR_spec cap rM rLC dS (by decide) (by decide) (by decide) (σ.setv rM (2 ^ cl))
    (by simp (config := { decide := true }) [Function.update_apply, zd])
    (by simp (config := { decide := true }) [Function.update_apply, zLC]; omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm (WExec.seq e1 e2)) (WXExec.seq e3 (WXExec.wm e4))) ?_ ?_
  · simp (config := { decide := true }) [Function.update_apply, zLC]
  · have h1 : cl * (25 * 2 ^ cl + 10) ≤ 2 ^ cl * (25 * 2 ^ cl + 10) := Nat.mul_le_mul_right _ hclM.le
    have h2 : (2 ^ cl + 1) ^ 2 = 2 ^ cl * 2 ^ cl + 2 * 2 ^ cl + 1 := by ring
    have h3 : 2 ^ cl * (25 * 2 ^ cl + 10) = 25 * (2 ^ cl * 2 ^ cl) + 10 * 2 ^ cl := by ring
    simp (config := { decide := true }) [Function.update_apply]
    omega

end

end NearCubicGates.Close.Setup
