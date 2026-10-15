import Proof.Wire_3_5.CompilerMachineEmitCoef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **The coefficient phase**: the magnitude register holds `|c|·2^{k−1}` at width `W`, the sign cells hold the signs
of `v` and `−v`, the entry register's head is on the mask; the other heads are back at cell `0`. -/
theorem coef_phase (Q Wm k U W : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Q) (c : ℤ) (par : Bool)
    (tlRE postQ tRCB RC₀ tz : List Bool) (pk0 sc0 nz0 sv0 snv0 : Bool) (hpost : readTapeBit postQ 0 = false)
    (cap capM : ℕ) (hcapZ : 2 * W + 1 ≤ cap)
    (hfit : c ≠ 0 → (k - 1) + (Nat.bits c.natAbs).length < W)
    (hcapM : coefRawCost Q W (Nat.bits c.natAbs).length ≤ capM) :
    Step coefM (2 * coefRawCost Q W (Nat.bits c.natAbs).length + 2)
      (Fin.addCases (cfH 0 0 0 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (coA (frame (entryWord Q Wm k U) ++ tlRE) (List.replicate Q true ++ postQ) (frame (cbits c) ++ tRCB)
        [par] RC₀ (frame (List.replicate W false) ++ tz) [pk0] [sc0] [nz0] [sv0] [snv0] (List.replicate cap false))
        (fun _ : Fin 1 => List.replicate capM false))
      (Fin.addCases (cfH (2 * Q + 2) 0 0 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (coA (frame (entryWord Q Wm k U) ++ tlRE) (List.replicate Q true ++ postQ) (frame (cbits c) ++ tRCB)
        [par] (overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀) (frame (List.replicate W false) ++ tz)
        [decide (k % 2 = 1)] [decide (c < 0)] [decide (c ≠ 0)]
        [decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1))]
        [decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))] (List.replicate cap false))
        (fun _ : Fin 1 => List.replicate capM false)) := by
  set RE := frame (entryWord Q Wm k U) ++ tlRE
  set CQ := List.replicate Q true ++ postQ
  set RCB := frame (cbits c) ++ tRCB
  set TZ := frame (List.replicate W false) ++ tz
  set LG := List.replicate cap false
  set RCt := overlay (frame (List.replicate W false)) RC₀
  set L := (Nat.bits c.natAbs).length
  set sv := decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1))
  set snv := decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))
  set RCf := overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀
  obtain ⟨rcE, hrcE⟩ : ∃ r : ℕ, r = if c = 0 then 2 * k else 2 * (k - 1) + 2 * L + 1 := ⟨_, rfl⟩
  -- s1: the template into the magnitude register
  have s1 := dockRun (regCopyStep (List.replicate W false) tz RC₀ cap (by simpa using hcapZ)) dZ dZ_inj (cfH 0 0 0 0)
    (coA RE CQ RCB [par] RC₀ TZ [pk0] [sc0] [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [install_dZ, dockH_dZ, List.length_replicate] at s1
  have s1' : Step dZD (2 * (2 * W + 1) + 2) (cfH 0 0 0 0) (coA RE CQ RCB [par] RC₀ TZ [pk0] [sc0] [nz0] [sv0] [snv0] LG)
      (cfH 0 0 0 0) (coA RE CQ RCB [par] RCt TZ [pk0] [sc0] [nz0] [sv0] [snv0] LG) :=
    s1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  -- s2: the parity cell cleared
  have s2 := dockRun (cellStep false pk0) dPK dPK_inj (cfH 0 0 0 0)
    (coA RE CQ RCB [par] RCt TZ [pk0] [sc0] [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_dPK, dockH_dPK] at s2
  have s2' : Step dPKD 1 (cfH 0 0 0 0) (coA RE CQ RCB [par] RCt TZ [pk0] [sc0] [nz0] [sv0] [snv0] LG)
      (cfH 0 0 0 0) (coA RE CQ RCB [par] RCt TZ [false] [sc0] [nz0] [sv0] [snv0] LG) :=
    s2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  -- s3: the size walk
  have s3 := thermo_loop Q Wm k U hk tlRE postQ RCB [par] RCt TZ [sc0] [nz0] [sv0] [snv0] LG hpost
  have s3' : Step (StreamController.machine thermoBodyM 1) (Q * (thermoCost + 2) + 1) (cfH 0 0 0 0)
      (coA RE CQ RCB [par] RCt TZ [false] [sc0] [nz0] [sv0] [snv0] LG) (cfH (2 * Q) Q 0 (2 * k))
      (coA RE CQ RCB [par] RCt TZ [decide (k % 2 = 1)] [sc0] [nz0] [sv0] [snv0] LG) := s3
  set PKc := [decide (k % 2 = 1)]
  -- s4: onto the mask
  have mvRE : ∀ r : ℕ, Step dRED 1 (cfH r Q 0 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG)
      (cfH (r + 1) Q 0 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG) := by
    intro r
    have e := dockRun (moveStep RE r) dRE dRE_inj (cfH r Q 0 (2 * k))
      (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
      (by intro j; fin_cases j; rfl)
    rw [install_dRE, dockH_dRE] at e
    exact e.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  -- s5: the sign and the nonzero bit of the coefficient word
  have m5a := dockRun (moveStep RCB 0) dRCB dRCB_inj (cfH (2 * Q + 2) Q 0 (2 * k))
    (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_dRCB, dockH_dRCB] at m5a
  have m5a' : Step dRCBD 1 (cfH (2 * Q + 2) Q 0 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG)
      (cfH (2 * Q + 2) Q 1 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG) :=
    m5a.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have c5 := dockRun (cpbStep RCB 1 sc0) dSC dSC_inj (cfH (2 * Q + 2) Q 1 (2 * k))
    (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [install_dSC, dockH_dSC, read_cbits1] at c5
  have c5' : Step dSCD 1 (cfH (2 * Q + 2) Q 1 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [sc0] [nz0] [sv0] [snv0] LG)
      (cfH (2 * Q + 2) Q 1 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc [decide (c < 0)] [nz0] [sv0] [snv0] LG) :=
    c5.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  set SCc := [decide (c < 0)]
  have m5b := dockRun (moveStep RCB 1) dRCB dRCB_inj (cfH (2 * Q + 2) Q 1 (2 * k))
    (coA RE CQ RCB [par] RCt TZ PKc SCc [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [install_dRCB, dockH_dRCB] at m5b
  have m5b' : Step dRCBD 1 (cfH (2 * Q + 2) Q 1 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc [nz0] [sv0] [snv0] LG)
      (cfH (2 * Q + 2) Q 2 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc [nz0] [sv0] [snv0] LG) :=
    m5b.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have n5 := dockRun (cpbStep RCB 2 nz0) dNZ dNZ_inj (cfH (2 * Q + 2) Q 2 (2 * k))
    (coA RE CQ RCB [par] RCt TZ PKc SCc [nz0] [sv0] [snv0] LG) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [install_dNZ, dockH_dNZ, read_cbits2] at n5
  have n5' : Step dNZD 1 (cfH (2 * Q + 2) Q 2 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc [nz0] [sv0] [snv0] LG)
      (cfH (2 * Q + 2) Q 2 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc [decide (c ≠ 0)] [sv0] [snv0] LG) :=
    n5.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  set NZc := [decide (c ≠ 0)]
  -- s6: the shifted copy (or nothing when `c = 0`)
  have hbr : Step (branchM 8 shiftCopyM (idle 12)) (shiftCost L + 2) (cfH (2 * Q + 2) Q 2 (2 * k))
      (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) (cfH (2 * Q + 2) Q (2 + 2 * L) rcE)
      (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv0] [snv0] LG) := by
    by_cases hc : c = 0
    · have hL0 : L = 0 := by simp [L, hc, Nat.zero_bits]
      have hRC : RCt = RCf := by simp [RCf, RCt, hc, binary_zero']
      have id := idleStep (cfH (2 * Q + 2) Q 2 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG)
      have id' : Step (idle 12) (shiftCost L) (cfH (2 * Q + 2) Q 2 (2 * k))
          (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) (cfH (2 * Q + 2) Q (2 + 2 * L) rcE)
          (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv0] [snv0] LG) := by
        refine (id.congr ?_ ?_).enlarge (Nat.zero_le _)
        · rw [hL0, hrcE, if_pos hc]
        · rw [hRC]
      exact branch_false (8 : Fin 12) shiftCopyM id' (by simp [coA, cfH, NZc, readTapeBit, hc])
    · have hfit' := hfit hc
      have hrc : rcE = 2 * (k - 1) + 2 * L + 1 := by rw [hrcE, if_neg hc]
      have l1 := dockRun (moveLStep RCt (2 * k - 1)) dRCL dRCL_inj (cfH (2 * Q + 2) Q 2 (2 * k - 1 + 1))
        (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
        (by intro j; fin_cases j; rfl)
      rw [install_dRCL, dockH_dRCL] at l1
      have l1' : Step dRCLD 1 (cfH (2 * Q + 2) Q 2 (2 * k)) (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG)
          (cfH (2 * Q + 2) Q 2 (2 * (k - 1) + 1)) (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) := by
        refine (l1.congr_in ?_ rfl).congr ?_ (by funext i; fin_cases i <;> rfl)
        · funext i; fin_cases i <;> simp [cfH]
          all_goals omega
        · funext i; fin_cases i <;> simp [cfH]
          all_goals omega
      have l2 := dockRun (moveLStep RCt (2 * (k - 1))) dRCL dRCL_inj (cfH (2 * Q + 2) Q 2 (2 * (k - 1) + 1))
        (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) (by intro j; fin_cases j; rfl)
        (by intro j; fin_cases j; rfl)
      rw [install_dRCL, dockH_dRCL] at l2
      have l2' : Step dRCLD 1 (cfH (2 * Q + 2) Q 2 (2 * (k - 1) + 1))
          (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG)
          (cfH (2 * Q + 2) Q 2 (fpre (List.replicate (k - 1) false)).length)
          (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) := by
        refine l2.congr ?_ (by funext i; fin_cases i <;> rfl)
        funext i; fin_cases i <;> simp [cfH, fpre_length]
      have hRCB : RCB = [true, decide (c < 0)] ++ frame (Nat.bits c.natAbs) ++ tRCB := by
        simp [RCB, cbits, frame]
      have cp := copyStep [true, decide (c < 0)] (Nat.bits c.natAbs) tRCB (fpre (List.replicate (k - 1) false)) RCt
      rw [← hRCB, template_prefix W (k - 1) (by omega) RC₀] at cp
      have dc := dockRun cp dCp dCp_inj (cfH (2 * Q + 2) Q 2 (fpre (List.replicate (k - 1) false)).length)
        (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG) (by intro j; fin_cases j <;> rfl)
        (by intro j; fin_cases j <;> rfl)
      rw [install_dCp, dockH_dCp] at dc
      set RCc := overlay (fpre (List.replicate (k - 1) false) ++ frame (Nat.bits c.natAbs)) RCt
      have dc' : Step dCpD (2 * L + 1) (cfH (2 * Q + 2) Q 2 (fpre (List.replicate (k - 1) false)).length)
          (coA RE CQ RCB [par] RCt TZ PKc SCc NZc [sv0] [snv0] LG)
          (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L + 1))
          (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG) := by
        refine dc.congr ?_ (by funext i; fin_cases i <;> rfl)
        funext i; fin_cases i <;> simp [cfH, fpre_length, L]
        all_goals omega
      have l3 := dockRun (moveLStep RCc (2 * (k - 1) + 2 * L)) dRCL dRCL_inj
        (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L + 1)) (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG)
        (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
      rw [install_dRCL, dockH_dRCL] at l3
      have l3' : Step dRCLD 1 (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L + 1))
          (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG) (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L))
          (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG) :=
        l3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
      have p3 := dockRun (putStep true RCc (2 * (k - 1) + 2 * L)) dPut dPut_inj
        (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L)) (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG)
        (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
      rw [install_dPut, dockH_dPut] at p3
      have hfin : writeTapeBit RCc (2 * (k - 1) + 2 * L) true = RCf := by
        have := rc_final W (k - 1) c.natAbs RC₀ hfit'
        exact this
      rw [hfin] at p3
      have p3' : Step dPutD 1 (cfH (2 * Q + 2) Q (2 + 2 * L) (2 * (k - 1) + 2 * L))
          (coA RE CQ RCB [par] RCc TZ PKc SCc NZc [sv0] [snv0] LG) (cfH (2 * Q + 2) Q (2 + 2 * L) rcE)
          (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv0] [snv0] LG) := by
        refine p3.congr ?_ (by funext i; fin_cases i <;> rfl)
        rw [hrc]
        funext i; fin_cases i <;> rfl
      have sc := l1'.seq (l2'.seq (dc'.seq (l3'.seq p3')))
      exact branch_true (8 : Fin 12) (idle 12) sc (by simp [coA, cfH, NZc, readTapeBit, hc])
  -- s7: the sign cells
  have g1 := dockRun (svStep (decide (c ≠ 0)) (decide (c < 0)) par (decide (k % 2 = 1)) sv0) dSV dSV_inj
    (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv0] [snv0] LG)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_dSV, dockH_dSV] at g1
  have g1' : Step dSVD 1 (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv0] [snv0] LG)
      (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv] [snv0] LG) :=
    g1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have g2 := dockRun (snvStep (decide (c ≠ 0)) (decide (c < 0)) par (decide (k % 2 = 1)) snv0) dSNV dSNV_inj
    (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv] [snv0] LG)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_dSNV, dockH_dSNV] at g2
  have g2' : Step dSNVD 1 (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv] [snv0] LG)
      (cfH (2 * Q + 2) Q (2 + 2 * L) rcE) (coA RE CQ RCB [par] RCf TZ PKc SCc NZc [sv] [snv] LG) :=
    g2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  have j := s1'.seq (s2'.seq (s3'.seq ((mvRE (2 * Q)).seq ((mvRE (2 * Q + 1)).seq (m5a'.seq (c5'.seq (m5b'.seq
    (n5'.seq (hbr.seq (g1'.seq g2'))))))))))
  have hm := j.mask coefSel (by intro i _; fin_cases i <;> rfl) (cap := capM)
    (by unfold coefRawCost at hcapM; omega)
  refine ((hm.congr_in ?_ ?_).congr ?_ ?_).enlarge ?_
  rotate_left 4
  · unfold coefRawCost; omega
  all_goals (funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (try fin_cases j) <;> rfl)

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
