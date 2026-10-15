import Proof.Wire_3_5.CompilerMachineEmitEntryPre

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **One lifted occurrence** before the reset. -/
noncomputable def entryRaw :=
  Composition.machine eLoadD (Composition.machine eGRD (Composition.machine eS1D (Composition.machine eS2D
    (Composition.machine eCoefD (Composition.machine eLabD (Composition.machine eCut0D (Composition.machine eEvD
      (Composition.machine eCut1D (Composition.machine eEnvD eCntD)))))))))

/-- The heads an occurrence returns to cell `0`: all but the groups', the output's and the count's. -/
def entSel : Fin 29 → Bool :=
  ![false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, false, true, true, true, true, true]

/-- **One lifted occurrence**, the scratch heads reset. -/
noncomputable def entryM := MaskedReset.machine entryRaw entSel

/-- The entry layout's heads: the groups, the output, the count. -/
def enH (g o c : ℕ) : Fin 29 → ℕ :=
  ![g, 0, o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c, 0, 0, 0, 0, 0]

/-- The entry layout's tapes (the comparison cell is `[false]`). -/
def enA (GR PL OUT TZ TS CQ CW RCB RPAR RE S1 S2 RP RN RD RP1 RC PK SC NZ SV SNV CNT LG LGa LGc LGcut LGcoef :
    List Bool) : Fin 29 → List Bool :=
  ![GR, PL, OUT, TZ, TS, CQ, CW, RCB, RPAR, RE, S1, S2, RP, RN, RD, [false], RP1, RC, PK, SC, NZ, SV, SNV, CNT, LG, LGa,
    LGc, LGcut, LGcoef]

/-- **The request's word of one occurrence**: the first cut's weights and `T`, `v`, the successor cut's weights and
`T + 1`, `−v`. -/
def entryWords (W : ℕ) (BS : List (List Bool)) (nf : ℕ) (sv snv : Bool) (mm : ℕ) : List Bool :=
  ((fieldsWord W BS (nf + 1) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1))))
    ++ frame (snv :: binary W mm)

/-- The cost of one occurrence before the reset. -/
def entryCost (Q W Wm h width L cbl : ℕ) : ℕ :=
  (2 * (2 * (Q + Wm + 1) + 1) + 2) + 1 + (1 + 1 + ((1 + 1 + (1 + 1 + (2 * appendCost 0 (2 * (width + width + 1)) 1 + 2)))
    + 1 + ((1 + 1 + (1 + 1 + (2 * appendCost 0 (2 * (width + width + 1)) 1 + 2))) + 1 + ((2 * coefRawCost Q W cbl + 2)
    + 1 + ((Wm * (labelCost (2 * (width + width + 1)) (1 + Wm * h) h + 2) + 1) + 1 + ((2 * cut0Cost W L (width + width) + 2)
    + 1 + (coefEmitCost W + 1 + ((2 * cut1Cost W L (width + width) + 2) + 1 + (coefEmitCost W + 1 + 1)))))))))

theorem entry_start (g o c : ℕ) : ∀ i, entSel i = true → (enH g o c) i = 0 := by
  intro i hi
  fin_cases i <;> simp_all [entSel, enH]

theorem entry_heads (Hf : Fin 29 → ℕ) (g o c : ℕ) (h0 : Hf 0 = g) (h2 : Hf 2 = o) (h23 : Hf 23 = c) :
    (fun i => if entSel i = true then 0 else Hf i) = enH g o c := by
  funext i
  fin_cases i <;> simp [entSel, enH, h0, h2, h23]

/-- `coef_phase` with plain 13-tape vectors (the reset log last). -/
theorem coef_phase_v (Q Wm k U W : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Q) (c : ℤ) (par : Bool)
    (tlRE postQ tRCB RC₀ tz : List Bool) (pk0 sc0 nz0 sv0 snv0 : Bool) (hpost : readTapeBit postQ 0 = false)
    (cap capM : ℕ) (hcapZ : 2 * W + 1 ≤ cap)
    (hfit : c ≠ 0 → (k - 1) + (Nat.bits c.natAbs).length < W)
    (hcapM : coefRawCost Q W (Nat.bits c.natAbs).length ≤ capM) :
    Step coefM (2 * coefRawCost Q W (Nat.bits c.natAbs).length + 2) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (entryWord Q Wm k U) ++ tlRE, List.replicate Q true ++ postQ, frame (cbits c) ++ tRCB,
        [par], RC₀, frame (List.replicate W false) ++ tz, [pk0], [sc0], [nz0], [sv0], [snv0], List.replicate cap false,
        List.replicate capM false]
      ![2 * Q + 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![frame (entryWord Q Wm k U) ++ tlRE, List.replicate Q true ++ postQ, frame (cbits c) ++ tRCB,
        [par], overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, frame (List.replicate W false) ++ tz,
        [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)],
        [decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1))],
        [decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))], List.replicate cap false,
        List.replicate capM false] := by
  have e := coef_phase Q Wm k U W hk1 hk c par tlRE postQ tRCB RC₀ tz pk0 sc0 nz0 sv0 snv0 hpost cap capM hcapZ hfit hcapM
  refine (e.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- **One lifted occurrence** (a union entry of a group): the output gets its request word, the count one more. -/
theorem entry_step (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (k U : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Q) (c : ℤ) (par : Bool)
    (GRpre GRtail tlPL tz tsStale postQ postW tRCB RE₀ S1₀ S2₀ RP₀ RN₀ RD₀ RP1₀ RC₀ out BW CNT₀ : List Bool)
    (pk0 sc0 nz0 sv0 snv0 : Bool) (cnt cap capA capC capCut capCoef capEnt : ℕ)
    (hpostQ : readTapeBit postQ 0 = false) (hpostW : readTapeBit postW 0 = false)
    (hLW : (selAt PC U PC.length).length * h < W)
    (hfit : c ≠ 0 → k - 1 + (Nat.bits c.natAbs).length < W)
    (hcap1 : 2 * W + 1 ≤ cap)
    (hcapL : 2 * ((selAt PC U PC.length).length * h) + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (Q + PC.length + 1) + 1 ≤ cap) (hcapS : appendCost 0 (2 * (width + width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hA2 : skipCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hC : appendCost 0 (2 * (width + width + 1)) (1 + PC.length * h + h) ≤ capC)
    (hcut0 : cut0Cost W ((selAt PC U PC.length).length * h) (width + width) ≤ capCut)
    (hcut1 : cut1Cost W ((selAt PC U PC.length).length * h) (width + width) ≤ capCut)
    (hcoef : coefRawCost Q W (Nat.bits c.natAbs).length ≤ capCoef)
    (hent : entryCost Q W PC.length h width ((selAt PC U PC.length).length * h) (Nat.bits c.natAbs).length ≤ capEnt) :
    Step entryM (2 * entryCost Q W PC.length h width ((selAt PC U PC.length).length * h) (Nat.bits c.natAbs).length + 2)
      (Fin.addCases (enH GRpre.length out.length cnt) (fun _ : Fin 1 => 0))
      (Fin.addCases (enA (GRpre ++ frame (entryWord Q PC.length k U) ++ GRtail)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (overlay out BW)
        (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) [par]
        RE₀ S1₀ S2₀ RP₀ RN₀ RD₀ RP1₀ RC₀ [pk0] [sc0] [nz0] [sv0] [snv0] (overlay (List.replicate cnt true) CNT₀)
        (List.replicate cap false) (List.replicate capA false) (List.replicate capC false) (List.replicate capCut false)
        (List.replicate capCoef false)) (fun _ : Fin 1 => List.replicate capEnt false))
      (Fin.addCases (enH (GRpre.length + 2 * (entryWord Q PC.length k U).length + 1)
        (out ++ entryWords W (stackBits h side width (selAt PC U PC.length)) (width + width)
          (decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1)))
          (decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))) (c.natAbs * 2 ^ (k - 1))).length
        (cnt + 1)) (fun _ : Fin 1 => 0))
      (Fin.addCases (enA (GRpre ++ frame (entryWord Q PC.length k U) ++ GRtail)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL)
        (overlay (out ++ entryWords W (stackBits h side width (selAt PC U PC.length)) (width + width)
          (decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1)))
          (decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))) (c.natAbs * 2 ^ (k - 1))) BW)
        (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) [par]
        (overlay (frame (entryWord Q PC.length k U)) RE₀)
        (overlay (stackStream h side width (selAt PC U PC.length)) S1₀)
        (overlay (stackStream h side width (selAt PC U PC.length)) S2₀)
        (regAt W (regAt W RP₀ (fx (stackBits h side width (selAt PC U PC.length))) (width + width + 1))
          (fx (stackBits h side width (selAt PC U PC.length))) (width + width + 1))
        (regAt W (regAt W RN₀ (fy (stackBits h side width (selAt PC U PC.length))) (width + width + 1))
          (fy (stackBits h side width (selAt PC U PC.length))) (width + width + 1))
        (overlay (frame (binary W (fz (stackBits h side width (selAt PC U PC.length)) (width + width) + 1).natAbs))
          (regAt W (regAt W RD₀ (fun q => (fz (stackBits h side width (selAt PC U PC.length)) q).natAbs) (width + width + 1))
            (fun q => (fz (stackBits h side width (selAt PC U PC.length)) q).natAbs) (width + width)))
        (overlay (frame (binary W (fx (stackBits h side width (selAt PC U PC.length)) (width + width) + 1))) RP1₀)
        (overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀) [decide (k % 2 = 1)] [decide (c < 0)]
        [decide (c ≠ 0)] [decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1))]
        [decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))]
        (overlay (List.replicate (cnt + 1) true) CNT₀)
        (List.replicate cap false) (List.replicate capA false) (List.replicate capC false) (List.replicate capCut false)
        (List.replicate capCoef false)) (fun _ : Fin 1 => List.replicate capEnt false)) := by
  set GRt := GRpre ++ frame (entryWord Q PC.length k U) ++ GRtail
  set PLt := (PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL
  set TZt := frame (List.replicate W false) ++ tz
  set TSt := streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale
  set CQt := List.replicate Q true ++ postQ
  set CWt := List.replicate (width + width) true ++ postW
  set RCBt := frame (cbits c) ++ tRCB
  set LGt := List.replicate cap false
  set sel := selAt PC U PC.length
  set BS := stackBits h side width sel
  set nf := width + width with hnfdef
  set mm := c.natAbs * 2 ^ (k - 1)
  obtain ⟨sv, hsv⟩ : ∃ b, b = (decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (k % 2 = 1))) := ⟨_, rfl⟩
  obtain ⟨snv, hsnv⟩ : ∃ b, b = (decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (k % 2 = 1))) := ⟨_, rfl⟩
  rw [← hsv, ← hsnv]
  have hN1 : ∀ r ∈ stackRecs h side width ([] : List (List Bool × ExactThresholdGate n)), r.length = 1 := by
    intro r hr; rw [stackRecs_nil] at hr; simp at hr; rw [hr]; rfl
  have hcapS' : appendCost 0 (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))).length 1 ≤ cap := by
    rw [stackRecs_length]; exact hcapS
  have hnf : 2 * nf + 1 < BS.length := by rw [stackBits_length]; omega
  -- 1
  have s1 := dockRun (loadStep GRpre (entryWord Q PC.length k U) GRtail RE₀ cap (by rw [entryWord_length Q PC.length k U hk]; omega)) eLoad eLoad_inj ![GRpre.length, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eLoad, dockH_eLoad] at s1
  have t1 : Step eLoadD (2 * (2 * (entryWord Q PC.length k U).length + 1) + 2) ![GRpre.length, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s1.congr rfl rfl
  -- 2
  have s2 := dockRun (moveStep GRt (GRpre.length + 2 * (entryWord Q PC.length k U).length)) eGR eGR_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_eGR, dockH_eGR] at s2
  have t2 : Step eGRD (1) ![GRpre.length + 2 * (entryWord Q PC.length k U).length, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s2.congr rfl rfl
  -- 3
  have s3 := dockRun (copyS_step (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale S1₀ 1 cap hN1 (le_refl 1) hcapS') eS1 eS1_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eS1, dockH_eS1] at s3
  have t3 : Step eS1D (1 + 1 + (1 + 1 + (2 * appendCost 0 (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))).length 1 + 2))) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s3.congr rfl rfl
  -- 4
  have s4 := dockRun (copyS_step (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale S2₀ 1 cap hN1 (le_refl 1) hcapS') eS2 eS2_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eS2, dockH_eS2] at s4
  have t4 : Step eS2D (1 + 1 + (1 + 1 + (2 * appendCost 0 (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))).length 1 + 2))) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s4.congr rfl rfl
  -- 5
  have s5 := dockRun (coef_phase Q PC.length k U W hk1 hk c par (RE₀.drop (frame (entryWord Q PC.length k U)).length) postQ tRCB RC₀ tz pk0 sc0 nz0 sv0 snv0 hpostQ cap capCoef hcap1 hfit hcoef) eCoef eCoef_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eCoef, dockH_eCoef, ← hsv, ← hsnv] at s5
  have t5 : Step eCoefD (2 * coefRawCost Q W (Nat.bits c.natAbs).length + 2) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, RC₀, [pk0], [sc0], [nz0], [sv0], [snv0], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 2 * Q + 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s5.congr rfl rfl
  -- 6
  have s6 := dockRun (labels_loop h side width PC U (fpre (thermo Q k ++ [true])) (RE₀.drop (frame (entryWord Q PC.length k U)).length) tlPL S1₀ S2₀ capA capC hA1 hA2 hC) eLab eLab_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 2 * Q + 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> first | rfl | exact (pre_length Q k hk).symm) (by intro j; fin_cases j <;> first | rfl | exact re_split Q PC.length k U RE₀)
  rw [install_eLab, dockH_eLab, ← re_split Q PC.length k U RE₀] at s6
  have t6 : Step eLabD (PC.length * (labelCost (2 * (width + width + 1)) (1 + PC.length * h) h + 2) + 1) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, 0, out.length, 0, 0, 0, 0, 0, 0, 2 * Q + 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S1₀, overlay (stackStream h side width ([] : List (List Bool × ExactThresholdGate n))) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, out.length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s6.congr rfl rfl
  -- 7
  have s7 := dockRun (cut0_step W (sel.length * h) nf hLW BS (stackBits_width h side width sel) hnf (S1₀.drop (((stackRecs h side width sel).flatMap frame).length + 1)) tz RP₀ RN₀ RD₀ out BW postW RP1₀ hpostW cap capCut hcap1 hcapL hcut0) eCut eCut_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, out.length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> first | rfl | exact s1_split h side width sel S1₀)
  rw [install_eCut, dockH_eCut, ← s1_split h side width sel S1₀] at s7
  have t7 : Step eCut0D (2 * cut0Cost W (sel.length * h) nf + 2) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, out.length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay out BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, RP₀, RN₀, RD₀, [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (out ++ fieldsWord W BS (nf + 1)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay (out ++ fieldsWord W BS (nf + 1)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s7.congr rfl rfl
  -- 8
  have s8 := dockRun (coefEmit_step W mm sv (RC₀.drop (frame (binary W mm)).length) (out ++ fieldsWord W BS (nf + 1)) BW cap hcap1) eEv eEv_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (out ++ fieldsWord W BS (nf + 1)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay (out ++ fieldsWord W BS (nf + 1)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eEv, dockH_eEv] at s8
  have t8 : Step eEvD (coefEmitCost W) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (out ++ fieldsWord W BS (nf + 1)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay (out ++ fieldsWord W BS (nf + 1)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s8.congr rfl rfl
  -- 9
  have s9 := dockRun (cut1_step W (sel.length * h) nf hLW BS (stackBits_width h side width sel) hnf (S1₀.drop (((stackRecs h side width sel).flatMap frame).length + 1)) tz (regAt W RP₀ (fx BS) (nf + 1)) (regAt W RN₀ (fy BS) (nf + 1)) (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) BW postW RP1₀ hpostW cap capCut hcap1 hcapL hcut1) eCut eCut_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> first | rfl | exact s1_split h side width sel S1₀)
  rw [install_eCut, dockH_eCut, ← s1_split h side width sel S1₀] at s9
  have t9 : Step eCut1D (2 * cut1Cost W (sel.length * h) nf + 2) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay ((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W RP₀ (fx BS) (nf + 1), regAt W RN₀ (fy BS) (nf + 1), regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1), [false], RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s9.congr rfl rfl
  -- 10
  have s10 := dockRun (coefEmit_step W mm snv (RC₀.drop (frame (binary W mm)).length) (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) BW cap hcap1) eEnv eEnv_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_eEnv, dockH_eEnv] at s10
  have t10 : Step eEnvD (coefEmitCost W) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s10.congr rfl rfl
  -- 11
  have s11 := dockRun (cntStep cnt CNT₀) eCnt eCnt_inj ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
    ![GRt, PLt, overlay ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_eCnt, dockH_eCnt] at s11
  have t11 : Step eCntD (1) ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate cnt true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false]
      ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1, ((PC.flatMap (labRecs h side width)).flatMap frame).length, ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length, 0, 0, 0, 0, 0, 0, (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt + 1, 0, 0, 0, 0, 0]
      ![GRt, PLt, overlay ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++ frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)) BW, TZt, TSt, CQt, CWt, RCBt, [par], overlay (frame (entryWord Q PC.length k U)) RE₀, overlay (stackStream h side width sel) S1₀, overlay (stackStream h side width sel) S2₀, regAt W (regAt W RP₀ (fx BS) (nf + 1)) (fx BS) (nf + 1), regAt W (regAt W RN₀ (fy BS) (nf + 1)) (fy BS) (nf + 1), overlay (frame (binary W (fz BS nf + 1).natAbs)) (regAt W (regAt W RD₀ (fun q => (fz BS q).natAbs) (nf + 1)) (fun q => (fz BS q).natAbs) nf), [false], overlay (frame (binary W (fx BS nf + 1))) RP1₀, overlay (frame (binary W (c.natAbs * 2 ^ (k - 1)))) RC₀, [decide (k % 2 = 1)], [decide (c < 0)], [decide (c ≠ 0)], [sv], [snv], overlay (List.replicate (cnt + 1) true) CNT₀, LGt, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false] :=
    s11.congr rfl rfl
  have jj := t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (t7.seq (t8.seq (t9.seq (t10.seq (t11))))))))))

  have hew : (entryWord Q PC.length k U).length = Q + PC.length + 1 := entryWord_length Q PC.length k U hk
  have hstart : ∀ i, entSel i = true → (enH GRpre.length out.length cnt) i = 0 := entry_start _ _ _
  have hm := jj.mask entSel hstart (cap := capEnt) (by
    simp only [hnfdef, hew, stackRecs_length]; unfold entryCost at hent; omega)
  have hH := entry_heads (fun i => ![GRpre.length + 2 * (entryWord Q PC.length k U).length + 1,
    ((PC.flatMap (labRecs h side width)).flatMap frame).length,
    ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++
      frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length, 0, 0, 0, 0, 0, 0,
    (fpre (thermo Q k ++ [true])).length + 2 * PC.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cnt + 1, 0, 0, 0, 0,
    0] i) (GRpre.length + 2 * (entryWord Q PC.length k U).length + 1)
    ((((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++
      frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm)).length (cnt + 1) rfl rfl rfl
  have hw : (((out ++ fieldsWord W BS (nf + 1)) ++ frame (sv :: binary W mm)) ++ (fieldsWord W BS nf ++
      frame (signMagnitude W (fz BS nf + 1)))) ++ frame (snv :: binary W mm) = out ++ entryWords W BS nf sv snv mm := by
    simp [entryWords, List.append_assoc]
  rw [hw] at hm hH
  refine ((hm.congr_in rfl rfl).congr ?_ rfl).enlarge ?_
  · exact congrArg (fun f => Fin.addCases (motive := fun _ => ℕ) f (fun _ : Fin 1 => 0)) hH
  · simp only [hnfdef, hew, stackRecs_length]; unfold entryCost; omega

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
