import Proof.Gates.Setup.PhaseC
import Proof.Gates.Recovery.TableSem
import Proof.Gates.WorkerArith.Header
import Proof.Gates.CheckedPCPP.ClauseFront

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

/-! ## Framed binary into a register, head back -/

/-- `X := value w` from `frame w` on `s` (then the head of `s` back at `0`). -/
def binRW {ns : ℕ} (s : Fin (ns + 1)) (X P Q T SC : Fin nrW) : WMX ns nrW :=
  .seq (LitDecode.binW s X P Q T SC) (.wm (WM.rewind s SC))

theorem binRW_exec {ns cap : ℕ} (s : Fin (ns + 1)) {X P Q T SC : Fin nrW} (hR : [X, P, Q, T, SC].Nodup) (w : List Bool)
    (σ : WState ns nrW) (hst : RdEq (σ.st s) (RepairOrdinary.frame w)) (hsh : σ.sh s = 0) (hX : σ.val X = 0)
    (hP : σ.val P = 0) (hQ : σ.val Q = 0) (hT : σ.val T = 0) (hSC : σ.val SC = 0)
    (hcap : 2 * 2 ^ w.length + 2 * w.length + 1 ≤ cap) :
    WXExec cap (binRW s X P Q T SC) σ (σ.setv X (value w)) (LitDecode.binCost w.length + 1 + (5 * (2 * w.length + 1) + 1)) := by
  have hfl := LitDecode.frame_length' w
  have e1 := LitDecode.binW_exec (cap := cap) s hR w [] [] σ (by simpa using hst) (by simpa using hsh) hP hQ hT
    (by rw [hX]; omega) (by rw [hSC, hfl]; omega)
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hR'
  have hXS : X ≠ SC := hR'.1.2.2.2
  set σ1 := ((σ.seth s ([].length + (RepairOrdinary.frame w).length)).setv X (σ.val X + value w)).setv SC
    (σ.val SC + (RepairOrdinary.frame w).length) with hσ1
  have e2 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) s SC ((RepairOrdinary.frame w).length) σ1
    (by simp [hσ1, hSC]) (by simp [hσ1, hSC, hfl]; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.wm e2)) ?_ (by rw [hfl])
  apply WState.eq
  · funext i; simp only [hσ1, WState.seth_sh, WState.setv_sh, Function.update_apply]; split_ifs <;> simp_all
  · rfl
  · funext r; simp only [hσ1, WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

/-! ## A marked `natWord` into a register, head back -/

/-- `rSC := x` from `marks (natWord x) ++ _` on `i` (register `68` = the rewind bound `4x + 6`). -/
def readRW {ns : ℕ} (i : Fin (ns + 1)) : WMX ns nrW :=
  .wm (.seq (WireExponent3_5.PrimAsm.ParseNat.readNatM true i 64 65 rSC 66 67)
    (.seq (Codec.dupR rSC 68 dS) (.seq (Codec.dupR rSC 68 dS) (.seq (Codec.dupR rSC 68 dS) (.seq (Codec.dupR rSC 68 dS)
    (.seq (NodeEmit.incN 68 6) (WM.rewind i 68)))))))

theorem readRW_exec {ns cap : ℕ} (i : Fin (ns + 1)) (x : ℕ) (rest : List Bool) (σ : WState ns nrW)
    (hst : σ.st i = marks (natWord x) ++ rest) (hsh : σ.sh i = 0)
    (hz : ∀ r ∈ ([64, 65, rSC, 66, 67, 68, dS] : List (Fin nrW)), σ.val r = 0)
    (hcap : 4 * x + 2 ^ (natBitLength x + 1) + 10 ≤ cap) :
    WXExec cap (readRW i) σ (σ.setv rSC x) (200 * (x + 2) ^ 2 + 40 * 2 ^ natBitLength x * (x + 3)) := by
  have z : ∀ r ∈ ([64, 65, rSC, 66, 67, 68, dS] : List (Fin nrW)), σ.val r = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at z
  obtain ⟨zf, zc, zv, zp, zt, zR, zd⟩ := z
  have hnb := Codec.natBitLength_le_succ x
  have hpw : 1 ≤ 2 ^ natBitLength x := Nat.one_le_two_pow
  have hpw2 : 2 ^ (natBitLength x + 1) = 2 * 2 ^ natBitLength x := by rw [pow_succ]; ring
  have hwl : (natWord x).length = 2 * natBitLength x + 1 := by simp
  have e1 := WireExponent3_5.PrimAsm.ParseNat.readNatM_spec cap true i 64 65 rSC 66 67 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x [] rest σ
    (by simpa [WireExponent3_5.PrimAsm.ParseNat.enc] using hst) (by simpa using hsh) zf zc zp zt (by rw [zv]; omega)
  set h1 := [].length + WireExponent3_5.PrimAsm.ParseNat.stp true * (natWord x).length with hh1
  have hh1' : h1 = 4 * natBitLength x + 2 := by
    rw [hh1, hwl]; simp [WireExponent3_5.PrimAsm.ParseNat.stp]; ring
  set σ1 := (σ.seth i h1).setv rSC (σ.val rSC + x) with hσ1
  have v1 : σ1.val rSC = x ∧ σ1.val 68 = 0 ∧ σ1.val dS = 0 := by simp (config := { decide := true }) [Function.update_apply, hσ1, zv, zR, zd]
  have e2 := Codec.dupR_spec cap rSC 68 dS (by decide) (by decide) (by decide) σ1 v1.2.2 (by have := v1.1; have := v1.2.1; omega)
  set σ2 := σ1.setv 68 (σ1.val 68 + σ1.val rSC) with hσ2
  have v2 : σ2.val rSC = x ∧ σ2.val 68 = x ∧ σ2.val dS = 0 := by simp (config := { decide := true }) [Function.update_apply, hσ2, v1.1, v1.2.1, v1.2.2]
  have e3 := Codec.dupR_spec cap rSC 68 dS (by decide) (by decide) (by decide) σ2 v2.2.2 (by have := v2.1; have := v2.2.1; omega)
  set σ3 := σ2.setv 68 (σ2.val 68 + σ2.val rSC) with hσ3
  have v3 : σ3.val rSC = x ∧ σ3.val 68 = 2 * x ∧ σ3.val dS = 0 := by
    simp (config := { decide := true }) [Function.update_apply, hσ3, v2.1, v2.2.1, v2.2.2]; ring
  have e4 := Codec.dupR_spec cap rSC 68 dS (by decide) (by decide) (by decide) σ3 v3.2.2 (by have := v3.1; have := v3.2.1; omega)
  set σ4 := σ3.setv 68 (σ3.val 68 + σ3.val rSC) with hσ4
  have v4 : σ4.val rSC = x ∧ σ4.val 68 = 3 * x ∧ σ4.val dS = 0 := by
    simp (config := { decide := true }) [Function.update_apply, hσ4, v3.1, v3.2.1, v3.2.2]; ring
  have e5 := Codec.dupR_spec cap rSC 68 dS (by decide) (by decide) (by decide) σ4 v4.2.2 (by have := v4.1; have := v4.2.1; omega)
  set σ5 := σ4.setv 68 (σ4.val 68 + σ4.val rSC) with hσ5
  have v5 : σ5.val 68 = 4 * x := by simp (config := { decide := true }) [Function.update_apply, hσ5, v4.1, v4.2.1]; ring
  have e6 := NodeEmit.incN_spec (cap := cap) (68 : Fin nrW) 6 σ5 (by rw [v5]; omega)
  set σ6 := σ5.setv 68 (σ5.val 68 + 6) with hσ6
  have v6 : σ6.val 68 = 4 * x + 6 := by simp (config := { decide := true }) [Function.update_apply, hσ6, v5]
  have e7 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) i 68 (4 * x + 6) σ6 v6 (by omega)
  refine WXExec.cast cap (WXExec.wm (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7))))))) ?_ ?_
  · apply WState.eq
    · funext j
      simp only [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with hj
      · subst hj; rw [hsh, hh1']; omega
      · rfl
    · rfl
    · funext r
      simp only [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all (config := { decide := true })
    · rfl
  · rw [v1.1, v2.1, v3.1, v4.1]
    have h1 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (40 * 2 ^ natBitLength x + 40) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (x + 3) * (40 * 2 ^ natBitLength x + 40) = 40 * 2 ^ natBitLength x * (x + 3) + 40 * (x + 3) := by ring
    have h3 : 0 ≤ (x + 2) ^ 2 := Nat.zero_le _
    nlinarith

end

end NearCubicGates.Close.Setup
