import Proof.Wire_3_5.CompilerMachineEmitEntry

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

/-- The state of the loop over a group's entries: the output, the count, the scratch registers, the index. -/
structure EnSt where
  out : List Bool
  cnt : ℕ
  re : List Bool
  s1 : List Bool
  s2 : List Bool
  rp : List Bool
  rn : List Bool
  rd : List Bool
  rp1 : List Bool
  rc : List Bool
  pk : Bool
  sc : Bool
  nz : Bool
  sv : Bool
  snv : Bool
  idx : ℕ

/-- **The request word of one entry** `(k, U)` of a group of coefficient `c` and parity `par`. -/
def entryOut (h width W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n)) (c : ℤ)
    (par : Bool) (e : ℕ × ℕ) : List Bool :=
  entryWords W (stackBits h side width (selAt PC e.2 PC.length)) (width + width)
    (decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide (e.1 % 2 = 1)))
    (decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide (e.1 % 2 = 1))) (c.natAbs * 2 ^ (e.1 - 1))

/-- The state after one entry (`entry_step`'s exit). -/
def enNext (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n)) (c : ℤ)
    (par : Bool) (es : List (ℕ × ℕ)) (st : EnSt) (_ : List Bool) : EnSt where
  out := st.out ++ entryOut h width W side PC c par (es.getD st.idx (0, 0))
  cnt := st.cnt + 1
  re := overlay (frame (entryWord Q PC.length (es.getD st.idx (0, 0)).1 (es.getD st.idx (0, 0)).2)) st.re
  s1 := overlay (stackStream h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)) st.s1
  s2 := overlay (stackStream h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)) st.s2
  rp := regAt W (regAt W st.rp (fx (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)))
    (width + width + 1)) (fx (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length))) (width + width + 1)
  rn := regAt W (regAt W st.rn (fy (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)))
    (width + width + 1)) (fy (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length))) (width + width + 1)
  rd := overlay (frame (binary W (fz (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length))
      (width + width) + 1).natAbs))
    (regAt W (regAt W st.rd (fun q => (fz (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)) q).natAbs)
      (width + width + 1))
      (fun q => (fz (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length)) q).natAbs) (width + width))
  rp1 := overlay (frame (binary W (fx (stackBits h side width (selAt PC (es.getD st.idx (0, 0)).2 PC.length))
    (width + width) + 1))) st.rp1
  rc := overlay (frame (binary W (c.natAbs * 2 ^ ((es.getD st.idx (0, 0)).1 - 1)))) st.rc
  pk := decide ((es.getD st.idx (0, 0)).1 % 2 = 1)
  sc := decide (c < 0)
  nz := decide (c ≠ 0)
  sv := decide (c ≠ 0) && (decide (c < 0) ^^ par ^^ decide ((es.getD st.idx (0, 0)).1 % 2 = 1))
  snv := decide (c ≠ 0) && !(decide (c < 0) ^^ par ^^ decide ((es.getD st.idx (0, 0)).1 % 2 = 1))
  idx := st.idx + 1

theorem foldl_enNext_idx (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (E : List (List Bool)) (s0 : EnSt) :
    (E.foldl (enNext h width Q W side PC c par es) s0).idx = s0.idx + E.length := by
  induction E generalizing s0 with
  | nil => simp
  | cons r E ih => rw [List.foldl_cons, ih]; simp [enNext]; omega

theorem foldl_enNext_out (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (E : List (List Bool)) (s0 : EnSt) (hlen : s0.idx + E.length ≤ es.length) :
    (E.foldl (enNext h width Q W side PC c par es) s0).out =
      s0.out ++ ((es.drop s0.idx).take E.length).flatMap (entryOut h width W side PC c par) := by
  induction E generalizing s0 with
  | nil => simp
  | cons r E ih =>
    have hi : s0.idx < es.length := by simp at hlen; omega
    rw [List.foldl_cons, ih _ (by simp only [enNext, List.length_cons] at hlen ⊢; omega)]
    show (s0.out ++ entryOut h width W side PC c par (es.getD s0.idx (0, 0))) ++
      ((es.drop (s0.idx + 1)).take E.length).flatMap (entryOut h width W side PC c par) = _
    rw [List.length_cons, List.drop_eq_getElem_cons hi, List.take_succ_cons, List.flatMap_cons,
      List.getD_eq_getElem _ _ hi, List.append_assoc]

theorem foldl_enNext_cnt (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (E : List (List Bool)) (s0 : EnSt) :
    (E.foldl (enNext h width Q W side PC c par es) s0).cnt = s0.cnt + E.length := by
  induction E generalizing s0 with
  | nil => simp
  | cons r E ih => rw [List.foldl_cons, ih]; simp [enNext]; omega

theorem cut0Cost_mono (W L1 L2 nf : ℕ) (hL : L1 ≤ L2) : cut0Cost W L1 nf ≤ cut0Cost W L2 nf := by
  unfold cut0Cost fieldCost padCost
  gcongr

theorem cut1Cost_mono (W L1 L2 nf : ℕ) (hL : L1 ≤ L2) : cut1Cost W L1 nf ≤ cut1Cost W L2 nf := by
  unfold cut1Cost fieldCost padCost
  gcongr

theorem entryCost_mono (Q W Wm h width L1 L2 cbl : ℕ) (hL : L1 ≤ L2) :
    entryCost Q W Wm h width L1 cbl ≤ entryCost Q W Wm h width L2 cbl := by
  unfold entryCost cut0Cost cut1Cost fieldCost padCost
  gcongr

/-- The entry loop's heads at a state. -/
def enBH (p : ℕ) (st : EnSt) : Fin (29 + 1) → ℕ :=
  Fin.addCases (motive := fun _ => ℕ) (enH p st.out.length st.cnt) (fun _ : Fin 1 => 0)

/-- The entry loop's tapes at a state. -/
def enBA (GRt PLt TZt TSt CQt CWt RCBt : List Bool) (par : Bool) (BW CNT₀ : List Bool)
    (cap capA capC capCut capCoef capEnt : ℕ) (st : EnSt) : Fin (29 + 1) → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) (enA GRt PLt (overlay st.out BW) TZt TSt CQt CWt RCBt [par]
    st.re st.s1 st.s2 st.rp st.rn st.rd st.rp1 st.rc [st.pk] [st.sc] [st.nz] [st.sv] [st.snv]
    (overlay (List.replicate st.cnt true) CNT₀) (List.replicate cap false) (List.replicate capA false)
    (List.replicate capC false) (List.replicate capCut false) (List.replicate capCoef false))
    (fun _ : Fin 1 => List.replicate capEnt false)

/-- **One entry of the group** at the loop's state `st` (index `j`): `entry_step` at the loop's bank. -/
theorem entries_body (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (P rest tlPL tz tsStale postQ postW tRCB BW CNT₀ : List Bool)
    (st : EnSt) (j : ℕ) (hj : j < es.length) (hidx : st.idx = j) (Lmax cap capA capC capCut capCoef capEnt : ℕ)
    (hpostQ : readTapeBit postQ 0 = false) (hpostW : readTapeBit postW 0 = false)
    (hk : ∀ e ∈ es, 1 ≤ e.1 ∧ e.1 ≤ Q)
    (hLe : ∀ e ∈ es, (selAt PC e.2 PC.length).length * h ≤ Lmax) (hLW : Lmax < W)
    (hfit : ∀ e ∈ es, c ≠ 0 → e.1 - 1 + (Nat.bits c.natAbs).length < W)
    (hcap1 : 2 * W + 1 ≤ cap) (hcapL : 2 * Lmax + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (Q + PC.length + 1) + 1 ≤ cap) (hcapS : appendCost 0 (2 * (width + width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hA2 : skipCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hC : appendCost 0 (2 * (width + width + 1)) (1 + PC.length * h + h) ≤ capC)
    (hcut0 : cut0Cost W Lmax (width + width) ≤ capCut) (hcut1 : cut1Cost W Lmax (width + width) ≤ capCut)
    (hcoef : coefRawCost Q W (Nat.bits c.natAbs).length ≤ capCoef)
    (hent : entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length ≤ capEnt) :
    Step entryM (2 * entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length + 2)
      (enBH (P.length + off (es.map fun e => entryWord Q PC.length e.1 e.2) j) st)
      (enBA (P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) par
        BW CNT₀ cap capA capC capCut capCoef capEnt st)
      (enBH (P.length + off (es.map fun e => entryWord Q PC.length e.1 e.2) (j + 1))
        (enNext h width Q W side PC c par es st ((es.map fun e => entryWord Q PC.length e.1 e.2)[j]'(by simpa using hj))))
      (enBA (P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) par
        BW CNT₀ cap capA capC capCut capCoef capEnt
        (enNext h width Q W side PC c par es st ((es.map fun e => entryWord Q PC.length e.1 e.2)[j]'(by simpa using hj)))) := by
  have hget : es.getD st.idx (0, 0) = es[j] := by rw [hidx, List.getD_eq_getElem _ _ hj]
  have hmem : es.getD st.idx (0, 0) ∈ es := by rw [hget]; exact List.getElem_mem _
  obtain ⟨hk1, hkQ⟩ := hk _ hmem
  have hjE : j < (es.map fun e => entryWord Q PC.length e.1 e.2).length := by simpa using hj
  have hEj : (es.map fun e => entryWord Q PC.length e.1 e.2)[j] =
      entryWord Q PC.length (es.getD st.idx (0, 0)).1 (es.getD st.idx (0, 0)).2 := by
    rw [hget]; simp
  have hsplit : P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest =
      (P ++ ((es.map fun e => entryWord Q PC.length e.1 e.2).take j).flatMap frame) ++
        frame (entryWord Q PC.length (es.getD st.idx (0, 0)).1 (es.getD st.idx (0, 0)).2) ++
        (((es.map fun e => entryWord Q PC.length e.1 e.2).drop (j + 1)).flatMap frame ++ false :: rest) := by
    rw [← hEj, streamTape_split _ rest j hjE]; simp only [List.append_assoc]
  have hLj := hLe _ hmem
  have es1 := entry_step h width Q W side PC (es.getD st.idx (0, 0)).1 (es.getD st.idx (0, 0)).2 hk1 hkQ c par
    (P ++ ((es.map fun e => entryWord Q PC.length e.1 e.2).take j).flatMap frame)
    (((es.map fun e => entryWord Q PC.length e.1 e.2).drop (j + 1)).flatMap frame ++ false :: rest) tlPL tz tsStale
    postQ postW tRCB st.re st.s1 st.s2 st.rp st.rn st.rd st.rp1 st.rc st.out BW CNT₀ st.pk st.sc st.nz st.sv st.snv
    st.cnt cap capA capC capCut capCoef capEnt hpostQ hpostW (by omega) (hfit _ hmem) hcap1 (by omega) hcapE hcapS hA1
    hA2 hC ((cut0Cost_mono W _ Lmax (width + width) hLj).trans hcut0)
    ((cut1Cost_mono W _ Lmax (width + width) hLj).trans hcut1) hcoef
    ((entryCost_mono Q W PC.length h width _ Lmax _ hLj).trans hent)
  rw [← hsplit] at es1
  have hoff1 : (P ++ ((es.map fun e => entryWord Q PC.length e.1 e.2).take j).flatMap frame).length +
      2 * (entryWord Q PC.length (es.getD st.idx (0, 0)).1 (es.getD st.idx (0, 0)).2).length + 1 =
      P.length + off (es.map fun e => entryWord Q PC.length e.1 e.2) (j + 1) := by
    rw [off_succ _ j hjE, hEj]; simp [off]; ring
  have hoff : (P ++ ((es.map fun e => entryWord Q PC.length e.1 e.2).take j).flatMap frame).length =
      P.length + off (es.map fun e => entryWord Q PC.length e.1 e.2) j := by simp [off]
  rw [hoff1, hoff] at es1
  have hc := entryCost_mono Q W PC.length h width _ Lmax (Nat.bits c.natAbs).length hLj
  exact es1.enlarge (by omega)

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
