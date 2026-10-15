import Proof.Wire_3_5.CompilerMachineEmitGroupPre

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits groupWord)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The group loop's state: the entries loop's state and the group registers. -/
structure GSt where
  en : EnSt
  rcb : List Bool
  rpar : Bool

/-- The state after one group of coefficient `c`, parity `par` and entries `es`. -/
def gnext (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n)) (c : ℤ)
    (par : Bool) (es : List (ℕ × ℕ)) (g : GSt) : GSt where
  en := (es.map fun e => entryWord Q PC.length e.1 e.2).foldl (enNext h width Q W side PC c par es) { g.en with idx := 0 }
  rcb := overlay (frame (cbits c)) g.rcb
  rpar := par

/-- The cost of one group. -/
def groupCost (ne cbl1 ec : ℕ) : ℕ :=
  1 + 1 + ((2 * (2 * cbl1 + 1) + 2) + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + ((ne * (ec + 2) + 1) + 1 + 1)))))))

theorem enBA_vec (GRt PLt TZt TSt CQt CWt RCBt : List Bool) (par : Bool) (BW CNT₀ : List Bool)
    (cap capA capC capCut capCoef capEnt : ℕ) (st : EnSt) :
    enBA GRt PLt TZt TSt CQt CWt RCBt par BW CNT₀ cap capA capC capCut capCoef capEnt st =
      ![GRt, PLt, overlay st.out BW, TZt, TSt, CQt, CWt, RCBt, [par], st.re, st.s1, st.s2, st.rp, st.rn, st.rd, [false], st.rp1, st.rc, [st.pk], [st.sc], [st.nz], [st.sv], [st.snv], overlay (List.replicate st.cnt true) CNT₀, List.replicate cap false, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false, List.replicate capEnt false] := by
  funext i
  fin_cases i <;> rfl

theorem enBH_vec (p : ℕ) (st : EnSt) : enBH p st = ![p, 0, st.out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, st.cnt, 0, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

/-- **One group**: its lifted occurrences' request words appended to the output. -/
theorem group_body (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (A R tlPL tz tsStale postQ postW BW CNT₀ : List Bool) (g : GSt)
    (Lmax cap capA capC capCut capCoef capEnt : ℕ)
    (hpostQ : readTapeBit postQ 0 = false) (hpostW : readTapeBit postW 0 = false)
    (hk : ∀ e ∈ es, 1 ≤ e.1 ∧ e.1 ≤ Q)
    (hLe : ∀ e ∈ es, (selAt PC e.2 PC.length).length * h ≤ Lmax) (hLW : Lmax < W)
    (hfit : ∀ e ∈ es, c ≠ 0 → e.1 - 1 + (Nat.bits c.natAbs).length < W)
    (hcap1 : 2 * W + 1 ≤ cap) (hcapL : 2 * Lmax + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (Q + PC.length + 1) + 1 ≤ cap) (hcapS : appendCost 0 (2 * (width + width + 1)) 1 ≤ cap)
    (hcapC : 2 * (cbits c).length + 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hA2 : skipCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hC : appendCost 0 (2 * (width + width + 1)) (1 + PC.length * h + h) ≤ capC)
    (hcut0 : cut0Cost W Lmax (width + width) ≤ capCut) (hcut1 : cut1Cost W Lmax (width + width) ≤ capCut)
    (hcoef : coefRawCost Q W (Nat.bits c.natAbs).length ≤ capCoef)
    (hent : entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length ≤ capEnt) :
    Step groupBodyM (groupCost es.length (cbits c).length
        (2 * entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length + 2))
      (enBH A.length g.en)
      (enBA (A ++ groupWord (cbits c) par (es.map fun e => entryWord Q PC.length e.1 e.2) ++ R)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) g.rcb g.rpar
        BW CNT₀ cap capA capC capCut capCoef capEnt g.en)
      (enBH (A ++ groupWord (cbits c) par (es.map fun e => entryWord Q PC.length e.1 e.2)).length
        (gnext h width Q W side PC c par es g).en)
      (enBA (A ++ groupWord (cbits c) par (es.map fun e => entryWord Q PC.length e.1 e.2) ++ R)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW)
        (gnext h width Q W side PC c par es g).rcb (gnext h width Q W side PC c par es g).rpar
        BW CNT₀ cap capA capC capCut capCoef capEnt (gnext h width Q W side PC c par es g).en) := by
  set E := es.map fun e => entryWord Q PC.length e.1 e.2
  set GRt := A ++ groupWord (cbits c) par E ++ R
  set PLt := (PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL
  set TZt := frame (List.replicate W false) ++ tz
  set TSt := streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale
  set CQt := List.replicate Q true ++ postQ
  set CWt := List.replicate (width + width) true ++ postW
  simp only [enBA_vec, enBH_vec]
  set bA := fun (rcb : List Bool) (rpar : Bool) (st : EnSt) => ![GRt, PLt, overlay st.out BW, TZt, TSt, CQt, CWt, rcb,
    [rpar], st.re, st.s1, st.s2, st.rp, st.rn, st.rd, [false], st.rp1, st.rc, [st.pk], [st.sc], [st.nz], [st.sv],
    [st.snv], overlay (List.replicate st.cnt true) CNT₀, List.replicate cap false, List.replicate capA false,
    List.replicate capC false, List.replicate capCut false, List.replicate capCoef false, List.replicate capEnt false]
  set bH := fun (p : ℕ) (st : EnSt) => ![p, 0, st.out.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, st.cnt, 0, 0, 0, 0, 0, 0]
  have mv : ∀ (p : ℕ) (rcb : List Bool) (rpar : Bool),
      Step gMvD 1 (bH p g.en) (bA rcb rpar g.en) (bH (p + 1) g.en) (bA rcb rpar g.en) := by
    intro p rcb rpar
    have e := dockRun (moveStep GRt p) gGR gGR_inj (bH p g.en) (bA rcb rpar g.en) (by intro j; fin_cases j; rfl)
      (by intro j; fin_cases j; rfl)
    rw [install_gGR, dockH_gGR] at e
    exact e.congr rfl rfl
  -- the coefficient word
  have hsp := group_split A R (cbits c) par E
  have ld := loadStep (A ++ [true]) (cbits c) ([true, par, false] ++ (E.flatMap frame ++ false :: R)) g.rcb cap hcapC
  rw [← hsp] at ld
  have dl := dockRun ld gLoad gLoad_inj (bH (A.length + 1) g.en) (bA g.rcb g.rpar g.en)
    (by intro j; fin_cases j <;> simp [bH, gLoad]) (by intro j; fin_cases j <;> rfl)
  rw [install_gLoad, dockH_gLoad] at dl
  set RCB1 := overlay (frame (cbits c)) g.rcb
  have dl' : Step gLoadD (2 * (2 * (cbits c).length + 1) + 2) (bH (A.length + 1) g.en) (bA g.rcb g.rpar g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length) g.en) (bA RCB1 g.rpar g.en) :=
    dl.congr rfl rfl
  -- the parity bit
  have hp := group_par A R (cbits c) par E
  have cp := dockRun (cpbGen GRt ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) [g.rpar] 0) gPar gPar_inj
    (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) g.en) (bA RCB1 g.rpar g.en)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_gPar, dockH_gPar, hp] at cp
  have cp' : Step gParD 1 (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) g.en) (bA RCB1 g.rpar g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) g.en) (bA RCB1 par g.en) :=
    cp.congr rfl rfl
  -- the entries
  have hsE := group_splitE A R (cbits c) par E
  have hPl : (A ++ [true] ++ frame (cbits c) ++ [true, par, false]).length =
      (A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 := by simp; omega
  have eL := entries_loop h width Q W side PC c par es (A ++ [true] ++ frame (cbits c) ++ [true, par, false]) R tlPL tz
    tsStale postQ postW (g.rcb.drop (frame (cbits c)).length) BW CNT₀ { g.en with idx := 0 } rfl Lmax cap capA capC
    capCut capCoef capEnt hpostQ hpostW hk hLe hLW hfit hcap1 hcapL hcapE hcapS hA1 hA2 hC hcut0 hcut1 hcoef hent
  rw [← hsE, hPl, enBA_vec, enBA_vec, enBH_vec, enBH_vec] at eL
  have eL' : Step (StreamController.machine entryM 0) (E.length *
        ((2 * entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length + 2) + 2) + 1)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1) g.en) (bA RCB1 par g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 + (E.flatMap frame).length)
        (gnext h width Q W side PC c par es g).en) (bA RCB1 par (gnext h width Q W side PC c par es g).en) :=
    eL
  have mvE := dockRun (moveStep GRt ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 + (E.flatMap frame).length))
    gGR gGR_inj (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 + (E.flatMap frame).length)
      (gnext h width Q W side PC c par es g).en) (bA RCB1 par (gnext h width Q W side PC c par es g).en)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_gGR, dockH_gGR] at mvE
  have hend : (A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 + (E.flatMap frame).length + 1 =
      (A ++ groupWord (cbits c) par E).length := by simp [groupWord]; omega
  have mvE' : Step gMvD 1
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1 + (E.flatMap frame).length)
        (gnext h width Q W side PC c par es g).en) (bA RCB1 par (gnext h width Q W side PC c par es g).en)
      (bH (A ++ groupWord (cbits c) par E).length (gnext h width Q W side PC c par es g).en)
      (bA RCB1 par (gnext h width Q W side PC c par es g).en) := by
    rw [← hend]; exact mvE.congr rfl rfl
  have m1 := mv A.length g.rcb g.rpar
  have m3 : Step gMvD 1 (bH ((A ++ [true]).length + 2 * (cbits c).length) g.en) (bA RCB1 g.rpar g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1) g.en) (bA RCB1 g.rpar g.en) := mv _ _ _
  have m4 : Step gMvD 1 (bH ((A ++ [true]).length + 2 * (cbits c).length + 1) g.en) (bA RCB1 g.rpar g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) g.en) (bA RCB1 g.rpar g.en) := mv _ _ _
  have m6 : Step gMvD 1 (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1) g.en) (bA RCB1 par g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1) g.en) (bA RCB1 par g.en) := mv _ _ _
  have m7 : Step gMvD 1 (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1) g.en) (bA RCB1 par g.en)
      (bH ((A ++ [true]).length + 2 * (cbits c).length + 1 + 1 + 1 + 1) g.en) (bA RCB1 par g.en) := mv _ _ _
  have j := m1.seq (dl'.seq (m3.seq (m4.seq (cp'.seq (m6.seq (m7.seq (eL'.seq mvE')))))))
  have hEl : E.length = es.length := by simp [E]
  rw [hEl] at j
  exact j

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
