import Proof.Gates.OuterM.ARunWalkScan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

/-- The A-run's registers. -/
abbrev nrA : ℕ := 32

/-- The cost of phase A (`L = ν^{G+2}`, `W` the walk's end). -/
def costA (G ν L W : ℕ) : ℕ :=
  (11 * ν + 1) + 1 + ((15 * ν + 1) + 1 + (((G + 2) * (61 * (ν + 1) ^ (G + 2)) + 4) + 1 + ((15 * L + 1) + 1 +
    (3 + 1 + ((14 * (L + 1) + 1) + 1 + ((5 * (L + 1) + 1) + 1 + ((11 * W + 1) + 1 + ((30 * (W + L) + 20) + 1 +
    (2 + 1 + (5 * W + 1))))))))))

/-- The register capacity phase A needs. -/
def capA (G ν : ℕ) : ℕ := 4 * (ν + 1) ^ (G + 2) + 4 * ν + 10

theorem read_replicate_true (ν k : ℕ) : readTapeBit (List.replicate ν true) k = decide (k < ν) := by
  unfold readTapeBit
  by_cases h : k < ν
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

section
variable {ns : ℕ} (hns : 5 ≤ ns)
include hns

local notation "sD" => (⟨0, by omega⟩ : Fin (ns + 1))
local notation "sN" => (⟨1, by omega⟩ : Fin (ns + 1))
local notation "sF" => (⟨2, by omega⟩ : Fin (ns + 1))
local notation "sS" => (⟨3, by omega⟩ : Fin (ns + 1))

/-- Phase A (the guard). -/
def phaseA (G : ℕ) : WMX ns nrA :=
  .seq (.wm (.whs sN (.seq (WM.fwdC sN 0) (.inc 1))))
  (.seq (.wm (spread3 1 2 3 4))
  (.seq (powW 5 6 2 7 8 (G + 2))
  (.seq (.wm (spread3 5 9 10 11))
  (.seq (.wm (.inc 11))
  (.seq (.wm (cpyC sD sS 11 12))
  (.seq (.wm (WM.rewind sS 12))
  (.seq (.wm (walkW sS 13 14))
  (.seq (leW 13 9 15 16 17 18 19)
  (.seq (.wm (flagW 18 sF))
  (.wm (WM.rewind sS 13)))))))))))

/-- **Phase A** (paper v2 §11.4, the guard on `⟨B_src⟩_ν`): the flag `[decide (SrcFits G ν B)]` on stream `2`, the
first `L_ν + 1` cells of the description on stream `3` (head `0`), `ν` in registers `2 3 4`, `L_ν` in register `10`;
streams from `4` on untouched. -/
theorem phaseA_spec (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (cap : ℕ) (σ : WState ns nrA)
    (hD : σ.st sD = PCPPNative.descriptor B) (hDh : σ.sh sD = 0)
    (hN : σ.st sN = List.replicate ν true) (hNh : σ.sh sN = 0)
    (hF : σ.st sF = []) (hFh : σ.sh sF = 0) (hS : σ.st sS = []) (hSh : σ.sh sS = 0)
    (hval : ∀ r, σ.val r = 0) (hcap : capA G ν ≤ cap) :
    ∃ τ, WXExec cap (phaseA hns G) σ τ (costA G ν (Outer.instLength G ν)
        (walkEnd (cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν + 1)) 0)) ∧
      τ.st sD = PCPPNative.descriptor B ∧ τ.st sN = List.replicate ν true ∧
      τ.st sF = [decide (Outer.SrcFits G ν B)] ∧
      τ.st sS = cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν + 1) ∧ τ.sh sS = 0 ∧
      τ.val 2 = ν ∧ τ.val 3 = ν ∧ τ.val 4 = ν ∧ τ.val 10 = Outer.instLength G ν ∧
      (∀ r : Fin nrA, 20 ≤ r.val → τ.val r = 0) ∧ τ.val 5 = 0 ∧ τ.val 6 = 0 ∧ τ.val 7 = 0 ∧ τ.val 8 = 0 ∧
      (∀ i : Fin (ns + 1), 4 ≤ i.val → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) := by
  set L := Outer.instLength G ν with hL
  have hLle : L ≤ (ν + 1) ^ (G + 2) := by rw [hL]; unfold Outer.instLength; exact Nat.pow_le_pow_left (by omega) _
  set d := PCPPNative.descriptor B with hd
  have hD0 : σ.st 0 = d := by simpa using hD
  have hDh0 : σ.sh 0 = 0 := by simpa using hDh
  set Sd := cellsOf d (L + 1) with hSd
  have hSdlen : Sd.length = L + 1 := by simp [Sd, cellsOf]
  set W := walkEnd Sd 0 with hW
  have hWle : W ≤ 2 * (L + 1) + 1 := by have := walkEnd_le Sd 0; rw [hSdlen] at this; omega

  have e1 := wreadU_loop cap sN (0 : Fin nrA) 1 (by decide) ν σ
    (fun k hk => by rw [hN, hNh, read_replicate_true]; simp; omega) (by rw [hN, hNh, read_replicate_true]; simp)
    (by rw [hval]; unfold capA at hcap; omega) (by rw [hval]; unfold capA at hcap; omega)
  set σ1 := ((σ.seth sN (σ.sh sN + ν)).setv 0 (σ.val 0 + ν)).setv 1 (σ.val 1 + ν) with hσ1

  have e2 := spread3_spec cap (1 : Fin nrA) 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ν σ1 (by simp [σ1, hval]) (by simp [σ1, hval]; unfold capA at hcap; omega)
    (by simp [σ1, hval]; unfold capA at hcap; omega) (by simp [σ1, hval]; unfold capA at hcap; omega)
    (by unfold capA at hcap; omega)
  set σ2 := (((σ1.setv 1 0).setv 2 (σ1.val 2 + ν)).setv 3 (σ1.val 3 + ν)).setv 4 (σ1.val 4 + ν) with hσ2

  have e3 := powW_spec cap (5 : Fin nrA) 6 2 7 8 (by decide) ν (G + 2) σ2 (by simp [σ2, σ1, hval])
    (by simp [σ2, σ1, hval]) (by simp [σ2, σ1, hval]) (by simp [σ2, σ1, hval]) (by simp [σ2, σ1, hval])
    (by unfold capA at hcap; omega)
  set σ3 := σ2.setv 5 (ν ^ (G + 2)) with hσ3
  have hL' : ν ^ (G + 2) = L := by rw [hL]; rfl

  have e4 := spread3_spec cap (5 : Fin nrA) 9 10 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) L σ3 (by simp [σ3, hL']) (by simp [σ3, σ2, σ1, hval]; unfold capA at hcap; omega)
    (by simp [σ3, σ2, σ1, hval]; unfold capA at hcap; omega) (by simp [σ3, σ2, σ1, hval]; unfold capA at hcap; omega)
    (by unfold capA at hcap; omega)
  set σ4 := (((σ3.setv 5 0).setv 9 (σ3.val 9 + L)).setv 10 (σ3.val 10 + L)).setv 11 (σ3.val 11 + L) with hσ4
  have e5 := WExec.inc (cap := cap) (11 : Fin nrA) σ4 (by simp [σ4, σ3, σ2, σ1, hval]; unfold capA at hcap; omega)
  set σ5 := σ4.setv 11 (σ4.val 11 + 1) with hσ5

  have e6 := cpyC_spec cap sD sS (11 : Fin nrA) 12 (by simp) (by decide) (L + 1) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, hval]) (by simp [σ5, σ4, σ3, σ2, σ1, hS, hSh])
    (by simp [σ5, σ4, σ3, σ2, σ1, hval]; unfold capA at hcap; omega) (by unfold capA at hcap; omega)
  set σ6 := ((((σ5.sets sS (σ5.st sS ++ List.ofFn fun i : Fin (L + 1) => readTapeBit (σ5.st sD) (σ5.sh sD + i.val))).seth
    sS ((σ5.st sS).length + (L + 1))).seth sD (σ5.sh sD + (L + 1))).setv 12 (σ5.val 12 + (L + 1))).setv 11 0 with hσ6
  have h6S : σ6.st sS = Sd := by
    simp [σ6, σ5, σ4, σ3, σ2, σ1, hS, hD, hDh, hD0, hDh0, Sd, cellsOf, d]
  have e7 := wrewind_spec cap sS (12 : Fin nrA) (L + 1) σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hval])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hval]; unfold capA at hcap; omega)
  set σ7 := (σ6.setv 12 0).seth sS (σ6.sh sS - (L + 1)) with hσ7

  have e8 := walkW_spec cap sS (13 : Fin nrA) 14 (by decide) Sd 0 σ7 (by simp [σ7, h6S])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hS, hSh]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]) (by omega) (by rw [hSdlen]; unfold capA at hcap; omega)
  set σ8 := (σ7.seth sS W).setv 13 W with hσ8

  have e9 := leW_spec cap (13 : Fin nrA) 9 15 16 17 18 19 (by decide) σ8 (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]) (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]) (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]; unfold capA at hcap; omega)
  have h89 : σ8.val 13 = W ∧ σ8.val 9 = L := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  set σ9 := σ8.setv 18 (if σ8.val 13 ≤ σ8.val 9 then 1 else 0) with hσ9

  have e10 := flagW_spec cap (18 : Fin nrA) sF σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hF])
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hFh])
  set σ10 := σ9.sets sF [decide (σ9.val 18 ≠ 0)] with hσ10

  have e11 := wrewind_spec cap sS (13 : Fin nrA) W σ10 (by simp [σ10, σ9, h89.1])
    (by simp [σ10, σ9, h89.1]; unfold capA at hcap; omega)
  set σ11 := (σ10.setv 13 0).seth sS (σ10.sh sS - W) with hσ11
  refine ⟨σ11, ?_, ?_⟩
  · refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
      (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7) (WXExec.seq (WXExec.wm e8)
      (WXExec.seq e9 (WXExec.seq (WXExec.wm e10) (WXExec.wm e11))))))))))) ?_
    rw [h89.1, h89.2]
    unfold costA
    omega
  have hflag : decide (σ9.val 18 ≠ 0) = decide (Outer.SrcFits G ν B) := by
    have hf := fits_iff B L
    simp only [σ9, WState.setv_val, Function.update_self, h89.1, h89.2]
    unfold Outer.SrcFits Outer.srcDescriptor
    by_cases hw : W ≤ L
    · rw [if_pos hw]; simp [← hL]; exact hf.mp hw
    · rw [if_neg hw]; simp [← hL]; by_contra h; exact hw (hf.mpr (by omega))
  refine ⟨by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hD, hD0],
    by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hN],
    by rw [← hflag]; simp [σ11, σ10], by simp [σ11, σ10, σ9, σ8, σ7, h6S], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ11, σ10, σ9, σ8]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · intro r hr
    have hne : ∀ k : Fin nrA, k.val < 20 → r ≠ k := fun k hk h => by subst h; omega
    simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval, hne 0 (by decide),
      hne 1 (by decide), hne 2 (by decide), hne 3 (by decide), hne 4 (by decide), hne 5 (by decide),
      hne 9 (by decide), hne 10 (by decide), hne 11 (by decide), hne 12 (by decide), hne 13 (by decide),
      hne 18 (by decide)]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hval]
  · intro i hi
    have h1 : i ≠ sD := fun h => by rw [h] at hi; simp at hi
    have h2 : i ≠ sN := fun h => by rw [h] at hi; simp at hi
    have h3 : i ≠ sF := fun h => by rw [h] at hi; simp at hi
    have h4 : i ≠ sS := fun h => by rw [h] at hi; simp at hi
    have h1' : i ≠ 0 := fun h => by rw [h] at hi; simp at hi
    simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h1, h2, h3, h4, h1']

end

end NearCubicGates.Close.OuterM
