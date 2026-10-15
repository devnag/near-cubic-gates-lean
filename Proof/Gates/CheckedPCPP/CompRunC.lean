import Proof.Gates.CheckedPCPP.CompRunB

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.Comp

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget
open NearCubicWires.RepairOrdinary.Streaming (marks)

section RunC
variable {t2 : ℕ} (E : LinearCodeFamily) {bud : MessageRequest → ℕ}
  (wf : WordFunction MessageRequest messageWord (fun m => FramedSim.pairs (List.ofFn (E.enc m.1 m.2.val))) bud)
  (t4 t5 : ℕ)

/-- The cost bound of `phaseC`. -/
def costC (q L : ℕ) : ℕ := q * (18 * L + 3 + 8) + 7 * q + 3 + 1 + (5 * (q * L) + 1) + 1 + (18 * q + 3) + 1 +
  (18 * L + 3) + 1 + SupW.supCost q L

theorem runC (q : ℕ) (cap : ℕ)
    (hcap : 2 * (E.length q * ((q + 1) * (2 * q + 3))) + 2 * q * (2 * q + 3) + 16 * q + 24 + 2 * E.length q +
      q * E.length q + 2 * q + 2 * E.length q + 2 ≤ cap)
    (σ : WState (NS t2 wf.program.tapeCount t4 t5) 64)
    (hmat : ∀ p, readTapeBit (σ.st (MAT t2 wf.program.tapeCount t4 t5)) p = matBit E q p)
    (hMATh : σ.sh (MAT t2 wf.program.tapeCount t4 t5) = E.length q * q)
    (h9 : σ.val (descH 9) = q) (h16 : σ.val (descH 16) = E.length q)
    (hSUP : σ.st (SUP t2 wf.program.tapeCount t4 t5) = []) (hSUPh : σ.sh (SUP t2 wf.program.tapeCount t4 t5) = 0)
    (hsg : ∀ i, σ.val (supG i) = 0) (hP2 : σ.val rP2 = 0) (hA2 : σ.val rA2 = 0) (hT : σ.val rT = 0) :
    ∃ τ, WXExec cap (phaseC (t2 := t2) (t4 := t4) (t5 := t5) E wf) σ τ (costC q (E.length q)) ∧
      τ.st (SUP t2 wf.program.tapeCount t4 t5) = RepairOrdinary.frame (CheckedPCPP.supportsWord E q) ∧
      ∀ y, y ≠ SUP t2 wf.program.tapeCount t4 t5 → y ≠ MAT t2 wf.program.tapeCount t4 t5 → τ.st y = σ.st y := by
  -- 14. q·L
  have e14 := mulR_spec cap (A := descH 9) (A2 := rA2) (B := descH 16) (C := rP2) (T := rT) (by decide) σ hA2 hT
    (by rw [hP2, h9, h16]; nlinarith) (by rw [h9]; omega)
  rw [hP2, h9, h16, Nat.zero_add] at e14
  set σ14 := σ.setv rP2 (q * E.length q) with hσ14
  -- 15. rewind the matrix
  have e15 := wrewind_spec (cap := cap) (MAT t2 wf.program.tapeCount t4 t5) rP2 (q * E.length q) σ14 (by simp [hσ14])
    (by simp [hσ14]; nlinarith)
  set σ15 := (σ14.setv rP2 0).seth (MAT t2 wf.program.tapeCount t4 t5)
    (σ14.sh (MAT t2 wf.program.tapeCount t4 t5) - q * E.length q) with hσ15
  -- 16, 17. copy q and L
  have e16 := addR_spec cap (A := descH 9) (B := supG 9) (T := rT) (by rdst) (by rdst) (by rdst) σ15
    (by simp [hσ15, hσ14, Function.update_of_ne (show rT ≠ rP2 by rdst), hT])
    (by simp [hσ15, hσ14, Function.update_of_ne (show supG 9 ≠ rP2 by rdst),
      Function.update_of_ne (show descH 9 ≠ rP2 by rdst), hsg 9, h9]; omega)
  have h15_9 : σ15.val (descH 9) = q := by simp [hσ15, hσ14, Function.update_of_ne (show descH 9 ≠ rP2 by rdst), h9]
  have h15_s9 : σ15.val (supG 9) = 0 := by
    simp [hσ15, hσ14, Function.update_of_ne (show supG 9 ≠ rP2 by rdst), hsg 9]
  rw [h15_9, h15_s9, Nat.zero_add] at e16
  set σ16 := σ15.setv (supG 9) q with hσ16
  have e17 := addR_spec cap (A := descH 16) (B := supG 16) (T := rT) (by rdst) (by rdst) (by rdst) σ16
    (by simp [hσ16, hσ15, hσ14, Function.update_of_ne (show rT ≠ rP2 by rdst),
      Function.update_of_ne (show rT ≠ supG 9 by rdst), hT])
    (by simp [hσ16, hσ15, hσ14, Function.update_of_ne (show supG 16 ≠ rP2 by rdst),
      Function.update_of_ne (show descH 16 ≠ rP2 by rdst), Function.update_of_ne (show supG 16 ≠ supG 9 by rdst),
      Function.update_of_ne (show descH 16 ≠ supG 9 by rdst), hsg 16, h16]; omega)
  have h16_16 : σ16.val (descH 16) = E.length q := by
    simp [hσ16, hσ15, hσ14, Function.update_of_ne (show descH 16 ≠ rP2 by rdst),
      Function.update_of_ne (show descH 16 ≠ supG 9 by rdst), h16]
  have h16_s16 : σ16.val (supG 16) = 0 := by
    simp [hσ16, hσ15, hσ14, Function.update_of_ne (show supG 16 ≠ rP2 by rdst),
      Function.update_of_ne (show supG 16 ≠ supG 9 by rdst), hsg 16]
  rw [h16_16, h16_s16, Nat.zero_add] at e17
  set σ17 := σ16.setv (supG 16) (E.length q) with hσ17
  -- 18. the supports
  have hsv : ∀ i : Fin 18, i ≠ 9 → i ≠ 16 → σ17.val (supG i) = 0 := by
    intro i h9' h16'
    simp [hσ17, hσ16, hσ15, hσ14, Function.update_of_ne (supG.injective.ne h9'),
      Function.update_of_ne (supG.injective.ne h16'), Function.update_of_ne (show supG i ≠ rP2 by rdst), hsg i]
  have hMAT17 : σ17.st (MAT t2 wf.program.tapeCount t4 t5) = σ.st (MAT t2 wf.program.tapeCount t4 t5) := by
    simp [hσ17, hσ16, hσ15, hσ14]
  have hMATh17 : σ17.sh (MAT t2 wf.program.tapeCount t4 t5) = 0 := by
    simp [hσ17, hσ16, hσ15, hσ14, hMATh]; rw [Nat.mul_comm]; simp
  have h0 := SupW.sRowInv_zero supG (SUP t2 wf.program.tapeCount t4 t5) (MAT t2 wf.program.tapeCount t4 t5) E q σ17
    (by simp [hσ17, hσ16, hσ15, hσ14, Function.update_of_ne (show SUP t2 wf.program.tapeCount t4 t5 ≠
      MAT t2 wf.program.tapeCount t4 t5 by dst), hSUP, hSUPh])
    (by simp [hσ17, hσ16, Function.update_of_ne (supG.injective.ne (show (9 : Fin 18) ≠ 16 by decide))])
    (hsv 10 (by decide) (by decide)) (hsv 11 (by decide) (by decide)) (hsv 12 (by decide) (by decide))
    (hsv 15 (by decide) (by decide)) hMATh17
    ⟨fun i hi => by
      rw [ChecksW.Rw_apply]
      exact hsv _ (by intro e; have := congrArg Fin.val e; simp at this; omega)
        (by intro e; have := congrArg Fin.val e; simp at this; omega),
     hsv 8 (by decide) (by decide)⟩
  obtain ⟨τ, e18, hτSUP, hτMAT, hτfr⟩ := SupW.supW_runs cap supG (SUP t2 wf.program.tapeCount t4 t5)
    (MAT t2 wf.program.tapeCount t4 t5) E q σ17 (by dst) (by rw [hMAT17]; exact hmat)
    (by simp [hσ17, hσ16, hσ15, hσ14, Function.update_of_ne (show supG 7 ≠ supG 16 by rdst),
      Function.update_of_ne (show supG 7 ≠ supG 9 by rdst), Function.update_of_ne (show supG 7 ≠ rP2 by rdst),
      hsg 7]; omega)
    h0 (by simp [hσ17]) (hsv 17 (by decide) (by decide))
  refine ⟨τ, WXExec.mono (WXExec.seq e14 (WXExec.seq (WXExec.wm e15) (WXExec.seq e16 (WXExec.seq e17 e18))))
    (by unfold costC; omega), ?_, ?_⟩
  · rw [hτSUP, DescW.frame_eq_marks' (CheckedPCPP.supportsWord E q)]
    simp [hσ17, hσ16, hσ15, hσ14, Function.update_of_ne (show SUP t2 wf.program.tapeCount t4 t5 ≠
      MAT t2 wf.program.tapeCount t4 t5 by dst), hSUP]
  · intro y h1 h2
    rw [hτfr.st (by simp [h1, h2])]
    simp [hσ17, hσ16, hσ15, hσ14, Function.update_of_ne h2]

end RunC

end NearCubicGates.Close.CheckedPCPP.Comp
