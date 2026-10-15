import Proof.Gates.OuterM.ARunB

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

/-- The bound on the length of the time word. -/
def bmax (et ct ν : ℕ) : ℕ := (ν + 1) ^ et * (2 * ct) + 3 + ν * 2

/-- The cost of phase C. -/
def costC (et ct ν : ℕ) : ℕ :=
  3 + 1 + ((et * (61 * (ν + 1 + 1) ^ et) + 4) + 1 + (((ν + 1) ^ et * (4 * (2 * ct) + 4) + 1) + 1 + (4 * 3 + 1 +
    ((ν * (4 * 2 + 4) + 1) + 1 + ((11 * bmax et ct ν + 1) + 1 + ((bmax et ct ν * (3 * (0 + bmax et ct ν) + 15) + 1) +
    1 + ((5 * bmax et ct ν + 1) + 1 + (5 * bmax et ct ν + 1))))))))

/-- The register capacity of phase C. -/
def capC (et ct ν : ℕ) : ℕ := 3 * (ν + 2) ^ et + 2 * bmax et ct ν + 10

section PhaseC
variable (pT pA : Program)

/-- Phase C. -/
def phaseC (et ct : ℕ) : WMX (nsL pT pA) nrA :=
  .seq (.wm (.inc 2))
  (.seq (powW 21 6 2 7 8 et)
  (.seq (.wm (mulC 21 22 (2 * ct)))
  (.seq (.wm (incG 22 3))
  (.seq (.wm (mulC 4 22 2))
  (.seq (.wm (spread2 22 23 21))
  (.seq (.wm (scanW (sTB pT pA) 23 24 25))
  (.seq (.wm (WM.rewind (sTB pT pA) 25))
  (.wm (subL 24 21)))))))))

/-- **Phase C**: register `21 := |v.bits|` for the word `v.bits` on the time program's output stream. -/
theorem phaseC_spec (et ct ν v : ℕ) (cap : ℕ) (σ : WState (nsL pT pA) nrA)
    (hst : σ.st (sTB pT pA) = v.bits) (hsh : σ.sh (sTB pT pA) = 0) (h2 : σ.val 2 = ν) (h4 : σ.val 4 = ν)
    (h678 : σ.val 6 = 0 ∧ σ.val 7 = 0 ∧ σ.val 8 = 0)
    (h21 : ∀ r : Fin nrA, 21 ≤ r.val → r.val ≤ 25 → σ.val r = 0)
    (hB : v.bits.length ≤ bmax et ct ν) (hcap : capC et ct ν ≤ cap) :
    ∃ τ, WXExec cap (phaseC pT pA et ct) σ τ (costC et ct ν) ∧ τ.val 21 = v.bits.length ∧
      τ.st (sTB pT pA) = v.bits ∧ τ.sh (sTB pT pA) = 0 ∧
      (∀ i, i ≠ sTB pT pA → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r : Fin nrA, (r.val < 2 ∨ r.val = 3 ∨ (9 ≤ r.val ∧ r.val < 21) ∨ 26 ≤ r.val) → τ.val r = σ.val r) := by
  set Bm := bmax et ct ν with hBm
  have z21 := h21 21 (by decide) (by decide)
  have z22 := h21 22 (by decide) (by decide)
  have z23 := h21 23 (by decide) (by decide)
  have z24 := h21 24 (by decide) (by decide)
  have z25 := h21 25 (by decide) (by decide)
  obtain ⟨z6, z7, z8⟩ := h678
  have hpow : (ν + 1) ^ et ≤ (ν + 2) ^ et := Nat.pow_le_pow_left (by omega) _
  have hBm1 : (ν + 1) ^ et * (2 * ct) + 3 + ν * 2 = Bm := rfl
  have e1 := WExec.inc (cap := cap) (2 : Fin nrA) σ (by rw [h2]; unfold capC at hcap; omega)
  set σ1 := σ.setv 2 (σ.val 2 + 1) with hσ1
  have e2 := powW_spec cap (21 : Fin nrA) 6 2 7 8 (by decide) (ν + 1) et σ1 (by simp [σ1, z21])
    (by simp [σ1, h2]) (by simp [σ1, z6]) (by simp [σ1, z7]) (by simp [σ1, z8])
    (by unfold capC at hcap; rw [show ν + 1 + 1 = ν + 2 by ring]; omega)
  set σ2 := σ1.setv 21 ((ν + 1) ^ et) with hσ2
  have e3 := mulC_spec cap (21 : Fin nrA) 22 (by decide) (2 * ct) ((ν + 1) ^ et) σ2 (by simp [σ2])
    (by simp [σ2, σ1, z22]; unfold capC at hcap; omega) (by unfold capC at hcap; omega)
  set σ3 := (σ2.setv 21 0).setv 22 (σ2.val 22 + (ν + 1) ^ et * (2 * ct)) with hσ3
  have e4 := incG_spec cap (22 : Fin nrA) 3 σ3 (by simp [σ3, σ2, σ1, z22]; unfold capC at hcap; omega)
  set σ4 := σ3.setv 22 (σ3.val 22 + 3) with hσ4
  have e5 := mulC_spec cap (4 : Fin nrA) 22 (by decide) 2 ν σ4 (by simp [σ4, σ3, σ2, σ1, h4])
    (by simp [σ4, σ3, σ2, σ1, z22]; unfold capC at hcap; omega) (by unfold capC at hcap; omega)
  set σ5 := (σ4.setv 4 0).setv 22 (σ4.val 22 + ν * 2) with hσ5
  have h5 : σ5.val 22 = Bm := by simp [σ5, σ4, σ3, σ2, σ1, z22, hBm1]
  have e6 := spread2_spec cap (22 : Fin nrA) 23 21 (by decide) (by decide) (by decide) Bm σ5 h5
    (by simp [σ5, σ4, σ3, σ2, σ1, z23]; unfold capC at hcap; omega)
    (by simp [σ5, σ4, σ3, σ2]; unfold capC at hcap; omega) (by unfold capC at hcap; omega)
  set σ6 := ((σ5.setv 22 0).setv 23 (σ5.val 23 + Bm)).setv 21 (σ5.val 21 + Bm) with hσ6
  have e7 := scanW_spec cap (sTB pT pA) (23 : Fin nrA) 24 25 (by decide) (by decide) (by decide) Bm σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, z23]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, z24]; unfold capC at hcap; omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, z25]; unfold capC at hcap; omega) (by unfold capC at hcap; omega)
  have h6st : σ6.st (sTB pT pA) = v.bits := by simp [σ6, σ5, σ4, σ3, σ2, σ1, hst]
  have h6sh : σ6.sh (sTB pT pA) = 0 := by simp [σ6, σ5, σ4, σ3, σ2, σ1, hsh]
  have h6z : σ6.val 24 = 0 := by simp [σ6, σ5, σ4, σ3, σ2, σ1, z24]
  set Z := (List.ofFn fun i : Fin Bm => readTapeBit (σ6.st (sTB pT pA)) (σ6.sh (sTB pT pA) + i.val)).foldl zstep
    (σ6.val 24) with hZ
  have hZ' : Z = (cellsOf v.bits Bm).foldl zstep 0 := by
    rw [hZ, h6st, h6sh, h6z]; simp [cellsOf]
  have hZle : Z ≤ Bm := by
    have := foldl_zstep_le (cellsOf v.bits Bm) 0
    rw [hZ']; simpa [cellsOf] using this
  set σ7 := (((σ6.seth (sTB pT pA) (σ6.sh (sTB pT pA) + Bm)).setv 25 (σ6.val 25 + Bm)).setv 24 Z).setv 23 0 with hσ7
  have e8 := wrewind_spec cap (sTB pT pA) (25 : Fin nrA) Bm σ7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, z25])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, z25]; unfold capC at hcap; omega)
  set σ8 := (σ7.setv 25 0).seth (sTB pT pA) (σ7.sh (sTB pT pA) - Bm) with hσ8
  have e9 := subL_spec cap (24 : Fin nrA) 21 (by decide) Z σ8 (by simp [σ8, σ7])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, z21]; unfold capC at hcap; omega) (by unfold capC at hcap; omega)
  set σ9 := (σ8.setv 24 0).setv 21 (σ8.val 21 - Z) with hσ9
  have h9 : σ9.val 21 = v.bits.length := by
    have := len_of_trail v Bm hB
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, z21]
    rw [hZ'] at *
    omega
  refine ⟨σ9, ?_, h9, ?_, ?_, ?_, ?_⟩
  · refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.seq (WXExec.wm e4)
      (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7) (WXExec.seq (WXExec.wm e8)
      (WXExec.wm e9))))))))) ?_
    have hv6 : σ6.val 24 = 0 := h6z
    unfold costC
    simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply] at hv6 ⊢
    simp [z24, z23, z21]
    rw [← hBm]
    nlinarith
  · simp [σ9, σ8, σ7, h6st]
  · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hsh]
  · intro i hi
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi]
  · intro r hr
    have hne : ∀ k : Fin nrA, (k.val = 2 ∨ k.val = 4 ∨ (21 ≤ k.val ∧ k.val ≤ 25)) → r ≠ k := fun k hk h => by
      subst h; omega
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne 2 (by decide), hne 4 (by decide),
      hne 21 (by decide), hne 22 (by decide), hne 23 (by decide), hne 24 (by decide), hne 25 (by decide)]

end PhaseC

end NearCubicGates.Close.OuterM
