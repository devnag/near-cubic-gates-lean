import Proof.Wire_3_5.CompilerMachineEmitField

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

/-- A register after `j` loads: its initial content, or the last value over it. -/
def regAt (W : ℕ) (Z : List Bool) (f : ℕ → ℕ) (j : ℕ) : List Bool :=
  if j = 0 then Z else overlay (frame (binary W (f (j - 1)))) Z

theorem regAt_succ (W : ℕ) (Z : List Bool) (f : ℕ → ℕ) (j : ℕ) :
    overlay (frame (binary W (f j))) (regAt W Z f j) = regAt W Z f (j + 1) := by
  cases j with
  | zero => simp [regAt]
  | succ j =>
    simp only [regAt, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    exact overlay_collapse _ _ _ (by simp)

/-- The P part of field pair `q`. -/
def fx (bs : List (List Bool)) (q : ℕ) : ℕ := value (bs.getD (2 * q) [])
/-- The N part of field pair `q`. -/
def fy (bs : List (List Bool)) (q : ℕ) : ℕ := value (bs.getD (2 * q + 1) [])
/-- The signed field `q`. -/
def fz (bs : List (List Bool)) (q : ℕ) : ℤ := (fx bs q : ℤ) - fy bs q

/-- The request's words of the first `j` signed fields. -/
def fieldsWord (W : ℕ) (bs : List (List Bool)) (j : ℕ) : List Bool :=
  (List.range j).flatMap fun q => frame (signMagnitude W (fz bs q))

theorem fieldsWord_succ (W : ℕ) (bs : List (List Bool)) (j : ℕ) :
    fieldsWord W bs (j + 1) = fieldsWord W bs j ++ frame (signMagnitude W (fz bs j)) := by
  simp [fieldsWord, List.range_succ, List.flatMap_append]

/-- **The field loop**: `nf` signed fields written at the output cursor, the stack head on record `2nf`. -/
theorem field_loop (W L nf : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (hnf : 2 * nf ≤ bs.length) (stale tz RP RN RD out BW post RP1 : List Bool) (hpost : readTapeBit post 0 = false)
    (cap : ℕ) (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step (StreamController.machine fieldBodyM 8) (nf * (fieldCost W L + 2) + 1)
      (fdH 0 out.length 0)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) (List.replicate nf true ++ post) RP1)
      (fdH (off (bs.map (true :: ·)) (2 * nf)) (out ++ fieldsWord W bs nf).length nf)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) (regAt W RP (fx bs) nf)
        (regAt W RN (fy bs) nf) (regAt W RD (fun q => (fz bs q).natAbs) nf) (overlay (out ++ fieldsWord W bs nf) BW)
        (List.replicate cap false) (List.replicate nf true ++ post) RP1) := by
  set rs := bs.map (true :: ·)
  let bH : ℕ → Fin 10 → ℕ := fun j => fdH (off rs (2 * j)) (out ++ fieldsWord W bs j).length j
  let bA : ℕ → Fin 10 → List Bool := fun j => fdA (streamTape rs stale) (frame (List.replicate W false) ++ tz)
    (regAt W RP (fx bs) j) (regAt W RN (fy bs) j) (regAt W RD (fun q => (fz bs q).natAbs) j)
    (overlay (out ++ fieldsWord W bs j) BW) (List.replicate cap false) (List.replicate nf true ++ post) RP1
  have hl := onesRun fieldBodyM 8 [] post nf hpost bH bA (fun _ => by simp [bA, fdA]) (fun _ => by simp [bH, fdH])
    (fieldCost W L) (by
      intro j hj
      have b := field_body W L hLW bs hbs j (by omega) stale tz (regAt W RP (fx bs) j) (regAt W RN (fy bs) j)
        (regAt W RD (fun q => (fz bs q).natAbs) j) (out ++ fieldsWord W bs j) BW (List.replicate nf true ++ post) RP1
        j cap hcap1 hcap2
      have hs : (out ++ fieldsWord W bs j) ++ frame (signMagnitude W ((value (bs.getD (2 * j) []) : ℤ) -
          value (bs.getD (2 * j + 1) []))) = out ++ fieldsWord W bs (j + 1) := by
        rw [fieldsWord_succ, List.append_assoc]; rfl
      have e1 : overlay (frame (binary W (value (bs.getD (2 * j) [])))) (regAt W RP (fx bs) j) =
          regAt W RP (fx bs) (j + 1) := regAt_succ W RP (fx bs) j
      have e2 : overlay (frame (binary W (value (bs.getD (2 * j + 1) [])))) (regAt W RN (fy bs) j) =
          regAt W RN (fy bs) (j + 1) := regAt_succ W RN (fy bs) j
      have e3 : overlay (frame (binary W ((value (bs.getD (2 * j) []) : ℤ) - value (bs.getD (2 * j + 1) [])).natAbs))
          (regAt W RD (fun q => (fz bs q).natAbs) j) = regAt W RD (fun q => (fz bs q).natAbs) (j + 1) :=
        regAt_succ W RD (fun q => (fz bs q).natAbs) j
      rw [hs, e1, e2, e3, show 2 * j + 2 = 2 * (j + 1) by ring] at b
      exact b)
  have e0 : bH 0 = fdH 0 out.length 0 := by simp [bH, fdH, fieldsWord, off]
  have a0 : bA 0 = fdA (streamTape rs stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
      (List.replicate cap false) (List.replicate nf true ++ post) RP1 := by simp [bA, regAt, fieldsWord]
  rw [e0, a0] at hl
  exact hl

/-- Load a field pair (P then N). -/
noncomputable def loadsM := Composition.machine fPadPD fPadND

theorem loads_step (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (q : ℕ) (hq : 2 * q + 1 < bs.length) (stale tz RP RN RD O CW RP1 : List Bool) (o cw cap : ℕ)
    (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step loadsM (padCost W L + 1 + padCost W L)
      (fdH (off (bs.map (true :: ·)) (2 * q)) o cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD O
        (List.replicate cap false) CW RP1)
      (fdH (off (bs.map (true :: ·)) (2 * q + 2)) o cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
        (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD O
        (List.replicate cap false) CW RP1) := by
  set rs := bs.map (true :: ·)
  have hr : rs.length = bs.length := by simp [rs]
  have h0 : 2 * q < rs.length := by omega
  have h1 : 2 * q + 1 < rs.length := by omega
  unfold fx fy
  obtain ⟨bP, hbP⟩ : ∃ b, bs.getD (2 * q) [] = b := ⟨_, rfl⟩
  obtain ⟨bN, hbN⟩ : ∃ b, bs.getD (2 * q + 1) [] = b := ⟨_, rfl⟩
  rw [hbP, hbN]
  have eP : bs[2 * q] = bP := by rw [← hbP, List.getD_eq_getElem _ _ (by omega)]
  have eN : bs[2 * q + 1] = bN := by rw [← hbN, List.getD_eq_getElem _ _ (by omega)]
  have hP : rs[2 * q] = true :: bP := by simp [rs, eP]
  have hN : rs[2 * q + 1] = true :: bN := by simp [rs, eN]
  have hPL : bP.length = L := by rw [← eP]; exact hbs _ (List.getElem_mem _)
  have hNL : bN.length = L := by rw [← eN]; exact hbs _ (List.getElem_mem _)
  set TZ := frame (List.replicate W false) ++ tz
  set ST := streamTape rs stale
  have sP := streamTape_split rs stale (2 * q) h0
  rw [hP] at sP
  have lp := pad_load W ((rs.take (2 * q)).flatMap frame) bP ((rs.drop (2 * q + 1)).flatMap frame ++ false :: stale)
    tz RP cap (by omega) hcap1 (by omega)
  rw [← sP] at lp
  have dp := dockRun lp fPadP fPadP_inj (fdH (off rs (2 * q)) o cw)
    (fdA ST TZ RP RN RD O (List.replicate cap false) CW RP1) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
  rw [install_fPadP, dockH_fPadP] at dp
  have ho1 := off_succ rs (2 * q) h0
  rw [hP] at ho1
  simp only [List.length_cons] at ho1
  have dp' : Step fPadPD (padCost W L) (fdH (off rs (2 * q)) o cw)
      (fdA ST TZ RP RN RD O (List.replicate cap false) CW RP1)
      (fdH (off rs (2 * q + 1)) o cw)
      (fdA ST TZ (overlay (frame (binary W (value bP))) RP) RN RD O (List.replicate cap false) CW RP1) := by
    rw [hPL] at dp
    refine dp.congr ?_ (by funext i; fin_cases i <;> rfl)
    funext i; fin_cases i
    · show off rs (2 * q) + (2 * (L + 1) + 1) = off rs (2 * q + 1)
      rw [ho1, hPL]
    all_goals rfl
  have sN := streamTape_split rs stale (2 * q + 1) h1
  rw [hN] at sN
  have ln := pad_load W ((rs.take (2 * q + 1)).flatMap frame) bN ((rs.drop (2 * q + 1 + 1)).flatMap frame ++ false :: stale)
    tz RN cap (by omega) hcap1 (by omega)
  rw [← sN] at ln
  have dn := dockRun ln fPadN fPadN_inj (fdH (off rs (2 * q + 1)) o cw)
    (fdA ST TZ (overlay (frame (binary W (value bP))) RP) RN RD O (List.replicate cap false) CW RP1)
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_fPadN, dockH_fPadN] at dn
  have ho2 := off_succ rs (2 * q + 1) h1
  rw [hN] at ho2
  simp only [List.length_cons] at ho2
  have dn' : Step fPadND (padCost W L) (fdH (off rs (2 * q + 1)) o cw)
      (fdA ST TZ (overlay (frame (binary W (value bP))) RP) RN RD O (List.replicate cap false) CW RP1)
      (fdH (off rs (2 * q + 2)) o cw)
      (fdA ST TZ (overlay (frame (binary W (value bP))) RP) (overlay (frame (binary W (value bN))) RN) RD O
        (List.replicate cap false) CW RP1) := by
    rw [hNL] at dn
    refine dn.congr ?_ (by funext i; fin_cases i <;> rfl)
    funext i; fin_cases i
    · show off rs (2 * q + 1) + (2 * (L + 1) + 1) = off rs (2 * q + 2)
      rw [ho2, hNL]
    all_goals rfl
  exact dp'.seq dn'

/-- The threshold pair of the first cut: load, then the signed field. -/
noncomputable def pair0M := Composition.machine loadsM fNormD
/-- The threshold pair of the successor cut: load, add one to the P part, then the signed field. -/
noncomputable def pair1M := Composition.machine loadsM (Composition.machine fIncD fNorm1D)

theorem fx_lt (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L) (q : ℕ)
    (hq : 2 * q < bs.length) : fx bs q + 1 < 2 ^ W := by
  unfold fx
  rw [List.getD_eq_getElem _ _ hq]
  have h1 := value_lt bs[2 * q]
  rw [hbs _ (List.getElem_mem _)] at h1
  have h2 : 2 ^ L * 2 ≤ 2 ^ W := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) hLW
  omega

theorem fy_lt (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L) (q : ℕ)
    (hq : 2 * q + 1 < bs.length) : fy bs q < 2 ^ W := by
  unfold fy
  exact value_lt_pow _ L W (by rw [List.getD_eq_getElem _ _ hq]; exact hbs _ (List.getElem_mem _)) hLW

theorem pair0_step (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (q : ℕ) (hq : 2 * q + 1 < bs.length) (stale tz RP RN RD out BW CW RP1 : List Bool) (cw cap : ℕ)
    (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step pair0M (padCost W L + 1 + padCost W L + 1 + normCost W)
      (fdH (off (bs.map (true :: ·)) (2 * q)) out.length cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) CW RP1)
      (fdH (off (bs.map (true :: ·)) (2 * q + 2)) (out ++ frame (signMagnitude W (fz bs q))).length cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
        (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN)
        (overlay (frame (binary W (fz bs q).natAbs)) RD) (overlay (out ++ frame (signMagnitude W (fz bs q))) BW)
        (List.replicate cap false) CW RP1) := by
  have l := loads_step W L hLW bs hbs q hq stale tz RP RN RD (overlay out BW) CW RP1 out.length cw cap hcap1 hcap2
  have hx : fx bs q < 2 ^ W := by have := fx_lt W L hLW bs hbs q (by omega); omega
  have hy := fy_lt W L hLW bs hbs q hq
  have nm := norm_step W (fx bs q) (fy bs q) hx hy (RP.drop (frame (binary W (fx bs q))).length)
    (RN.drop (frame (binary W (fy bs q))).length) RD out BW cap hcap1
  have dm := dockRun nm fNorm fNorm_inj (fdH (off (bs.map (true :: ·)) (2 * q + 2)) out.length cw)
    (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
      (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD (overlay out BW)
      (List.replicate cap false) CW RP1) (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_fNorm, dockH_fNorm] at dm
  have dm' := dm.congr (hout' := fdH (off (bs.map (true :: ·)) (2 * q + 2))
      (out ++ frame (signMagnitude W (fz bs q))).length cw)
    (tout' := fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
        (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN)
        (overlay (frame (binary W (fz bs q).natAbs)) RD) (overlay (out ++ frame (signMagnitude W (fz bs q))) BW)
        (List.replicate cap false) CW RP1)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact l.seq dm'

theorem pair1_step (W L : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (q : ℕ) (hq : 2 * q + 1 < bs.length) (stale tz RP RN RD out BW CW RP1 : List Bool) (cw cap : ℕ)
    (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap) :
    Step pair1M (padCost W L + 1 + padCost W L + 1 + ((2 * (2 * W + 1) + 2) + 1 + normCost W))
      (fdH (off (bs.map (true :: ·)) (2 * q)) out.length cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) CW RP1)
      (fdH (off (bs.map (true :: ·)) (2 * q + 2)) (out ++ frame (signMagnitude W (fz bs q + 1))).length cw)
      (fdA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz)
        (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN)
        (overlay (frame (binary W (fz bs q + 1).natAbs)) RD) (overlay (out ++ frame (signMagnitude W (fz bs q + 1))) BW)
        (List.replicate cap false) CW (overlay (frame (binary W (fx bs q + 1))) RP1)) := by
  have l := loads_step W L hLW bs hbs q hq stale tz RP RN RD (overlay out BW) CW RP1 out.length cw cap hcap1 hcap2
  have hx1 := fx_lt W L hLW bs hbs q (by omega)
  have hy := fy_lt W L hLW bs hbs q hq
  set ST := streamTape (bs.map (true :: ·)) stale
  set TZ := frame (List.replicate W false) ++ tz
  have hTZ : TZ = frame (binary W 0) ++ tz := by simp [TZ, binary_zero']
  have z := zipT addOut addNxt true (binary W (fx bs q)) (binary W 0)
    (RP.drop (frame (binary W (fx bs q))).length) tz RP1 (by simp) cap
    (by simp; omega)
  rw [map_add, show fx bs q + 0 + true.toNat = fx bs q + 1 by simp, binary_length] at z
  have dz := dockRun z fInc fInc_inj (fdH (off (bs.map (true :: ·)) (2 * q + 2)) out.length cw)
    (fdA ST TZ (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD (overlay out BW)
      (List.replicate cap false) CW RP1) (by intro k; fin_cases k <;> rfl) (by
        intro k; fin_cases k
        · rfl
        · exact hTZ
        · rfl
        · rfl)
  rw [install_fInc, dockH_fInc] at dz
  set R1 := overlay (frame (binary W (fx bs q + 1))) RP1
  have dz' : Step fIncD (2 * (2 * W + 1) + 2) (fdH (off (bs.map (true :: ·)) (2 * q + 2)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD (overlay out BW)
        (List.replicate cap false) CW RP1)
      (fdH (off (bs.map (true :: ·)) (2 * q + 2)) out.length cw)
      (fdA ST TZ (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD (overlay out BW)
        (List.replicate cap false) CW R1) := by
    refine dz.congr (by funext i; fin_cases i <;> rfl) ?_
    funext i; fin_cases i
    · rfl
    · exact hTZ.symm
    all_goals rfl
  have nm := norm_step W (fx bs q + 1) (fy bs q) hx1 hy (RP1.drop (frame (binary W (fx bs q + 1))).length)
    (RN.drop (frame (binary W (fy bs q))).length) RD out BW cap hcap1
  have dm := dockRun nm fNorm1 fNorm1_inj (fdH (off (bs.map (true :: ·)) (2 * q + 2)) out.length cw)
    (fdA ST TZ (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN) RD (overlay out BW)
      (List.replicate cap false) CW R1) (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_fNorm1, dockH_fNorm1] at dm
  have hz : (((fx bs q + 1 : ℕ) : ℤ) - fy bs q) = fz bs q + 1 := by unfold fz; push_cast; ring
  rw [hz] at dm
  have dm' := dm.congr (hout' := fdH (off (bs.map (true :: ·)) (2 * q + 2))
      (out ++ frame (signMagnitude W (fz bs q + 1))).length cw)
    (tout' := fdA ST TZ (overlay (frame (binary W (fx bs q))) RP) (overlay (frame (binary W (fy bs q))) RN)
        (overlay (frame (binary W (fz bs q + 1).natAbs)) RD) (overlay (out ++ frame (signMagnitude W (fz bs q + 1))) BW)
        (List.replicate cap false) CW R1)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
  exact l.seq (dz'.seq dm')

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
