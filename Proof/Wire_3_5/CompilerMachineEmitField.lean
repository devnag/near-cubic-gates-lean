import Proof.Wire_3_5.CompilerMachineEmitPad

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def fPadP : Fin 4 → Fin 10 := ![0, 1, 2, 7]
def fPadN : Fin 4 → Fin 10 := ![0, 1, 3, 7]
def fNorm : Fin 6 → Fin 10 := ![2, 3, 4, 5, 6, 7]
def fCW : Fin 1 → Fin 10 := ![8]
def fInc : Fin 4 → Fin 10 := ![2, 1, 9, 7]
def fNorm1 : Fin 6 → Fin 10 := ![9, 3, 4, 5, 6, 7]

theorem fPadP_inj : Function.Injective fPadP := by decide

theorem install_fPadP (A : Fin 10 → List Bool) (v : Fin 4 → List Bool) :
    install fPadP A v = ![v 0, v 1, v 2, A 3, A 4, A 5, A 6, v 3, A 8, A 9] := by
  funext i
  fin_cases i
  · exact install_slot fPadP fPadP_inj A v 0
  · exact install_slot fPadP fPadP_inj A v 1
  · exact install_slot fPadP fPadP_inj A v 2
  · exact install_other fPadP A v 3 (by decide)
  · exact install_other fPadP A v 4 (by decide)
  · exact install_other fPadP A v 5 (by decide)
  · exact install_other fPadP A v 6 (by decide)
  · exact install_slot fPadP fPadP_inj A v 3
  · exact install_other fPadP A v 8 (by decide)
  · exact install_other fPadP A v 9 (by decide)

theorem dockH_fPadP (H : Fin 10 → ℕ) (v : Fin 4 → ℕ) :
    dockH fPadP H v = ![v 0, v 1, v 2, H 3, H 4, H 5, H 6, v 3, H 8, H 9] := by
  funext i
  fin_cases i
  · exact dockH_slot fPadP fPadP_inj H v 0
  · exact dockH_slot fPadP fPadP_inj H v 1
  · exact dockH_slot fPadP fPadP_inj H v 2
  · exact dockH_other fPadP H v 3 (by decide)
  · exact dockH_other fPadP H v 4 (by decide)
  · exact dockH_other fPadP H v 5 (by decide)
  · exact dockH_other fPadP H v 6 (by decide)
  · exact dockH_slot fPadP fPadP_inj H v 3
  · exact dockH_other fPadP H v 8 (by decide)
  · exact dockH_other fPadP H v 9 (by decide)

theorem fPadN_inj : Function.Injective fPadN := by decide

theorem install_fPadN (A : Fin 10 → List Bool) (v : Fin 4 → List Bool) :
    install fPadN A v = ![v 0, v 1, A 2, v 2, A 4, A 5, A 6, v 3, A 8, A 9] := by
  funext i
  fin_cases i
  · exact install_slot fPadN fPadN_inj A v 0
  · exact install_slot fPadN fPadN_inj A v 1
  · exact install_other fPadN A v 2 (by decide)
  · exact install_slot fPadN fPadN_inj A v 2
  · exact install_other fPadN A v 4 (by decide)
  · exact install_other fPadN A v 5 (by decide)
  · exact install_other fPadN A v 6 (by decide)
  · exact install_slot fPadN fPadN_inj A v 3
  · exact install_other fPadN A v 8 (by decide)
  · exact install_other fPadN A v 9 (by decide)

theorem dockH_fPadN (H : Fin 10 → ℕ) (v : Fin 4 → ℕ) :
    dockH fPadN H v = ![v 0, v 1, H 2, v 2, H 4, H 5, H 6, v 3, H 8, H 9] := by
  funext i
  fin_cases i
  · exact dockH_slot fPadN fPadN_inj H v 0
  · exact dockH_slot fPadN fPadN_inj H v 1
  · exact dockH_other fPadN H v 2 (by decide)
  · exact dockH_slot fPadN fPadN_inj H v 2
  · exact dockH_other fPadN H v 4 (by decide)
  · exact dockH_other fPadN H v 5 (by decide)
  · exact dockH_other fPadN H v 6 (by decide)
  · exact dockH_slot fPadN fPadN_inj H v 3
  · exact dockH_other fPadN H v 8 (by decide)
  · exact dockH_other fPadN H v 9 (by decide)

theorem fNorm_inj : Function.Injective fNorm := by decide

theorem install_fNorm (A : Fin 10 → List Bool) (v : Fin 6 → List Bool) :
    install fNorm A v = ![A 0, A 1, v 0, v 1, v 2, v 3, v 4, v 5, A 8, A 9] := by
  funext i
  fin_cases i
  · exact install_other fNorm A v 0 (by decide)
  · exact install_other fNorm A v 1 (by decide)
  · exact install_slot fNorm fNorm_inj A v 0
  · exact install_slot fNorm fNorm_inj A v 1
  · exact install_slot fNorm fNorm_inj A v 2
  · exact install_slot fNorm fNorm_inj A v 3
  · exact install_slot fNorm fNorm_inj A v 4
  · exact install_slot fNorm fNorm_inj A v 5
  · exact install_other fNorm A v 8 (by decide)
  · exact install_other fNorm A v 9 (by decide)

theorem dockH_fNorm (H : Fin 10 → ℕ) (v : Fin 6 → ℕ) :
    dockH fNorm H v = ![H 0, H 1, v 0, v 1, v 2, v 3, v 4, v 5, H 8, H 9] := by
  funext i
  fin_cases i
  · exact dockH_other fNorm H v 0 (by decide)
  · exact dockH_other fNorm H v 1 (by decide)
  · exact dockH_slot fNorm fNorm_inj H v 0
  · exact dockH_slot fNorm fNorm_inj H v 1
  · exact dockH_slot fNorm fNorm_inj H v 2
  · exact dockH_slot fNorm fNorm_inj H v 3
  · exact dockH_slot fNorm fNorm_inj H v 4
  · exact dockH_slot fNorm fNorm_inj H v 5
  · exact dockH_other fNorm H v 8 (by decide)
  · exact dockH_other fNorm H v 9 (by decide)

theorem fCW_inj : Function.Injective fCW := by decide

theorem install_fCW (A : Fin 10 → List Bool) (v : Fin 1 → List Bool) :
    install fCW A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0, A 9] := by
  funext i
  fin_cases i
  · exact install_other fCW A v 0 (by decide)
  · exact install_other fCW A v 1 (by decide)
  · exact install_other fCW A v 2 (by decide)
  · exact install_other fCW A v 3 (by decide)
  · exact install_other fCW A v 4 (by decide)
  · exact install_other fCW A v 5 (by decide)
  · exact install_other fCW A v 6 (by decide)
  · exact install_other fCW A v 7 (by decide)
  · exact install_slot fCW fCW_inj A v 0
  · exact install_other fCW A v 9 (by decide)

theorem dockH_fCW (H : Fin 10 → ℕ) (v : Fin 1 → ℕ) :
    dockH fCW H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 0, H 9] := by
  funext i
  fin_cases i
  · exact dockH_other fCW H v 0 (by decide)
  · exact dockH_other fCW H v 1 (by decide)
  · exact dockH_other fCW H v 2 (by decide)
  · exact dockH_other fCW H v 3 (by decide)
  · exact dockH_other fCW H v 4 (by decide)
  · exact dockH_other fCW H v 5 (by decide)
  · exact dockH_other fCW H v 6 (by decide)
  · exact dockH_other fCW H v 7 (by decide)
  · exact dockH_slot fCW fCW_inj H v 0
  · exact dockH_other fCW H v 9 (by decide)

theorem fInc_inj : Function.Injective fInc := by decide

theorem install_fInc (A : Fin 10 → List Bool) (v : Fin 4 → List Bool) :
    install fInc A v = ![A 0, v 1, v 0, A 3, A 4, A 5, A 6, v 3, A 8, v 2] := by
  funext i
  fin_cases i
  · exact install_other fInc A v 0 (by decide)
  · exact install_slot fInc fInc_inj A v 1
  · exact install_slot fInc fInc_inj A v 0
  · exact install_other fInc A v 3 (by decide)
  · exact install_other fInc A v 4 (by decide)
  · exact install_other fInc A v 5 (by decide)
  · exact install_other fInc A v 6 (by decide)
  · exact install_slot fInc fInc_inj A v 3
  · exact install_other fInc A v 8 (by decide)
  · exact install_slot fInc fInc_inj A v 2

theorem dockH_fInc (H : Fin 10 → ℕ) (v : Fin 4 → ℕ) :
    dockH fInc H v = ![H 0, v 1, v 0, H 3, H 4, H 5, H 6, v 3, H 8, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other fInc H v 0 (by decide)
  · exact dockH_slot fInc fInc_inj H v 1
  · exact dockH_slot fInc fInc_inj H v 0
  · exact dockH_other fInc H v 3 (by decide)
  · exact dockH_other fInc H v 4 (by decide)
  · exact dockH_other fInc H v 5 (by decide)
  · exact dockH_other fInc H v 6 (by decide)
  · exact dockH_slot fInc fInc_inj H v 3
  · exact dockH_other fInc H v 8 (by decide)
  · exact dockH_slot fInc fInc_inj H v 2

theorem fNorm1_inj : Function.Injective fNorm1 := by decide

theorem install_fNorm1 (A : Fin 10 → List Bool) (v : Fin 6 → List Bool) :
    install fNorm1 A v = ![A 0, A 1, A 2, v 1, v 2, v 3, v 4, v 5, A 8, v 0] := by
  funext i
  fin_cases i
  · exact install_other fNorm1 A v 0 (by decide)
  · exact install_other fNorm1 A v 1 (by decide)
  · exact install_other fNorm1 A v 2 (by decide)
  · exact install_slot fNorm1 fNorm1_inj A v 1
  · exact install_slot fNorm1 fNorm1_inj A v 2
  · exact install_slot fNorm1 fNorm1_inj A v 3
  · exact install_slot fNorm1 fNorm1_inj A v 4
  · exact install_slot fNorm1 fNorm1_inj A v 5
  · exact install_other fNorm1 A v 8 (by decide)
  · exact install_slot fNorm1 fNorm1_inj A v 0

theorem dockH_fNorm1 (H : Fin 10 → ℕ) (v : Fin 6 → ℕ) :
    dockH fNorm1 H v = ![H 0, H 1, H 2, v 1, v 2, v 3, v 4, v 5, H 8, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other fNorm1 H v 0 (by decide)
  · exact dockH_other fNorm1 H v 1 (by decide)
  · exact dockH_other fNorm1 H v 2 (by decide)
  · exact dockH_slot fNorm1 fNorm1_inj H v 1
  · exact dockH_slot fNorm1 fNorm1_inj H v 2
  · exact dockH_slot fNorm1 fNorm1_inj H v 3
  · exact dockH_slot fNorm1 fNorm1_inj H v 4
  · exact dockH_slot fNorm1 fNorm1_inj H v 5
  · exact dockH_other fNorm1 H v 8 (by decide)
  · exact dockH_slot fNorm1 fNorm1_inj H v 0

noncomputable def fPadPD := RecoveryFocus.machine fPadP padLoadM
noncomputable def fPadND := RecoveryFocus.machine fPadN padLoadM
noncomputable def fNormD := RecoveryFocus.machine fNorm normM
noncomputable def fCWD := RecoveryFocus.machine fCW moveM
noncomputable def fIncD := RecoveryFocus.machine fInc (zipM addOut addNxt true)
noncomputable def fNorm1D := RecoveryFocus.machine fNorm1 normM
/-- **One field pair**: load P, load N, write the signed field, step the driver. -/
noncomputable def fieldBodyM :=
  Composition.machine fPadPD (Composition.machine fPadND (Composition.machine fNormD fCWD))

/-- The field layout's heads: the stack, the output cursor and the driver move. -/
def fdH (s o c : ℕ) : Fin 10 → ℕ := ![s, 0, 0, 0, 0, 0, o, 0, c, 0]

/-- The field layout's tapes (the comparison cell is `[false]` between fields). -/
def fdA (S1 TZ RP RN RD O LG CW RP1 : List Bool) : Fin 10 → List Bool := ![S1, TZ, RP, RN, RD, [false], O, LG, CW, RP1]

/-- The cost of one field pair. -/
def fieldCost (W L : ℕ) : ℕ := padCost W L + 1 + (padCost W L + 1 + (normCost W + 1 + 1))

theorem value_lt_pow (b : List Bool) (L W : ℕ) (hb : b.length = L) (hLW : L < W) : value b < 2 ^ W :=
  (value_lt b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem field_body (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (q : ℕ) (hq : 2 * q + 1 < bs.length) (stale tz RP RN RD out BW CW RP1 : List Bool) (cw cap : ℕ)
    (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step fieldBodyM (fieldCost W L)
      (fdH (off (bs.map (true :: ·)) (2 * q)) out.length cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) CW RP1)
      (fdH (off (bs.map (true :: ·)) (2 * q + 2))
        (out ++ frame (signMagnitude W ((value (bs.getD (2 * q) []) : ℤ) - value (bs.getD (2 * q + 1) [])))).length
        (cw + 1))
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
        (overlay (frame (binary W (value (bs.getD (2 * q) [])))) RP)
        (overlay (frame (binary W (value (bs.getD (2 * q + 1) [])))) RN)
        (overlay (frame (binary W ((value (bs.getD (2 * q) []) : ℤ) - value (bs.getD (2 * q + 1) [])).natAbs)) RD)
        (overlay (out ++ frame (signMagnitude W ((value (bs.getD (2 * q) []) : ℤ) - value (bs.getD (2 * q + 1) []))))
          BW) (List.replicate cap false) CW RP1) := by
  set rs := bs.map (true :: ·)
  have hr : rs.length = bs.length := by simp [rs]
  have h0 : 2 * q < rs.length := by omega
  have h1 : 2 * q + 1 < rs.length := by omega
  obtain ⟨bP, hbP⟩ : ∃ b, bs.getD (2 * q) [] = b := ⟨_, rfl⟩
  obtain ⟨bN, hbN⟩ : ∃ b, bs.getD (2 * q + 1) [] = b := ⟨_, rfl⟩
  rw [hbP, hbN]
  have eP : bs[2 * q] = bP := by rw [← hbP, List.getD_eq_getElem _ _ (by omega)]
  have eN : bs[2 * q + 1] = bN := by rw [← hbN, List.getD_eq_getElem _ _ (by omega)]
  have hP : rs[2 * q] = true :: bP := by simp [rs, eP]
  have hN : rs[2 * q + 1] = true :: bN := by simp [rs, eN]
  have hPL : bP.length = L := by rw [← eP]; exact hbs _ (List.getElem_mem _)
  have hNL : bN.length = L := by rw [← eN]; exact hbs _ (List.getElem_mem _)
  set x := value bP
  set y := value bN
  have hx : x < 2 ^ W := value_lt_pow bP L W hPL hLW
  have hy : y < 2 ^ W := value_lt_pow bN L W hNL hLW
  set TZ := frame (List.replicate W false) ++ tz
  set ST := streamTape rs stale
  -- load P
  have sP := streamTape_split rs stale (2 * q) h0
  rw [hP] at sP
  have lp := pad_load W ((rs.take (2 * q)).flatMap frame) bP ((rs.drop (2 * q + 1)).flatMap frame ++ false :: stale)
    tz RP cap (by omega) hcap1 (by omega)
  rw [← sP] at lp
  have dp := dockRun lp fPadP fPadP_inj (fdH (off rs (2 * q)) out.length cw)
    (fdA ST TZ RP RN RD (overlay out BW) (List.replicate cap false) CW RP1) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_fPadP, dockH_fPadP] at dp
  have ho1 := off_succ rs (2 * q) h0
  rw [hP] at ho1
  simp only [List.length_cons] at ho1
  have dp' : Step fPadPD (padCost W L) (fdH (off rs (2 * q)) out.length cw)
      (fdA ST TZ RP RN RD (overlay out BW) (List.replicate cap false) CW RP1)
      (fdH (off rs (2 * q + 1)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W x)) RP) RN RD (overlay out BW) (List.replicate cap false) CW RP1) := by
    rw [hPL] at dp
    refine dp.congr ?_ (by funext i; fin_cases i <;> rfl)
    funext i; fin_cases i
    · show off rs (2 * q) + (2 * (L + 1) + 1) = off rs (2 * q + 1)
      rw [ho1, hPL]
    all_goals rfl
  -- load N
  have sN := streamTape_split rs stale (2 * q + 1) h1
  rw [hN] at sN
  have ln := pad_load W ((rs.take (2 * q + 1)).flatMap frame) bN ((rs.drop (2 * q + 1 + 1)).flatMap frame ++ false :: stale)
    tz RN cap (by omega) hcap1 (by omega)
  rw [← sN] at ln
  have dn := dockRun ln fPadN fPadN_inj (fdH (off rs (2 * q + 1)) out.length cw)
    (fdA ST TZ (overlay (frame (binary W x)) RP) RN RD (overlay out BW) (List.replicate cap false) CW RP1)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_fPadN, dockH_fPadN] at dn
  have ho2 := off_succ rs (2 * q + 1) h1
  rw [hN] at ho2
  simp only [List.length_cons] at ho2
  have dn' : Step fPadND (padCost W L) (fdH (off rs (2 * q + 1)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W x)) RP) RN RD (overlay out BW) (List.replicate cap false) CW RP1)
      (fdH (off rs (2 * q + 2)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN) RD (overlay out BW)
        (List.replicate cap false) CW RP1) := by
    rw [hNL] at dn
    refine dn.congr ?_ (by funext i; fin_cases i <;> rfl)
    funext i; fin_cases i
    · show off rs (2 * q + 1) + (2 * (L + 1) + 1) = off rs (2 * q + 2)
      rw [ho2, hNL]
    all_goals rfl
  -- the signed field
  have nm := norm_step W x y hx hy ((overlay (frame (binary W x)) RP).drop (frame (binary W x)).length)
    ((overlay (frame (binary W y)) RN).drop (frame (binary W y)).length) RD out BW cap hcap1
  have dm := dockRun nm fNorm fNorm_inj (fdH (off rs (2 * q + 2)) out.length cw)
    (fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN) RD (overlay out BW)
      (List.replicate cap false) CW RP1) (by intro k; fin_cases k <;> rfl) (by
        intro k; fin_cases k
        · show overlay (frame (binary W x)) RP = frame (binary W x) ++ _
          simp [overlay]
        · show overlay (frame (binary W y)) RN = frame (binary W y) ++ _
          simp [overlay]
        all_goals rfl)
  rw [install_fNorm, dockH_fNorm] at dm
  have dm' : Step fNormD (normCost W) (fdH (off rs (2 * q + 2)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN) RD (overlay out BW)
        (List.replicate cap false) CW RP1)
      (fdH (off rs (2 * q + 2)) (out ++ frame (signMagnitude W ((x : ℤ) - y))).length cw)
      (fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN)
        (overlay (frame (binary W ((x : ℤ) - y).natAbs)) RD) (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW)
        (List.replicate cap false) CW RP1) := by
    refine dm.congr (by funext i; fin_cases i <;> rfl) ?_
    funext i; fin_cases i
    · rfl
    · rfl
    · show frame (binary W x) ++ _ = overlay (frame (binary W x)) RP
      simp [overlay]
    · show frame (binary W y) ++ _ = overlay (frame (binary W y)) RN
      simp [overlay]
    all_goals rfl
  -- the driver
  have mc := dockRun (moveStep CW cw) fCW fCW_inj
    (fdH (off rs (2 * q + 2)) (out ++ frame (signMagnitude W ((x : ℤ) - y))).length cw)
    (fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN)
      (overlay (frame (binary W ((x : ℤ) - y).natAbs)) RD) (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW)
      (List.replicate cap false) CW RP1) (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_fCW, dockH_fCW] at mc
  have mc' := mc.congr (hout' := fdH (off rs (2 * q + 2)) (out ++ frame (signMagnitude W ((x : ℤ) - y))).length (cw + 1))
    (tout' := fdA ST TZ (overlay (frame (binary W x)) RP) (overlay (frame (binary W y)) RN)
      (overlay (frame (binary W ((x : ℤ) - y).natAbs)) RD) (overlay (out ++ frame (signMagnitude W ((x : ℤ) - y))) BW)
      (List.replicate cap false) CW RP1)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact dp'.seq (dn'.seq (dm'.seq mc'))

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
