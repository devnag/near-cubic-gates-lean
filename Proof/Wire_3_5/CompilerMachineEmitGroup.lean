import Proof.Wire_3_5.CompilerMachineEmitEntries

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits)
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **The lifted occurrences of one group**, the stream of its entries walked by `entries_body`. -/
theorem entries_loop (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    (c : ℤ) (par : Bool) (es : List (ℕ × ℕ)) (P rest tlPL tz tsStale postQ postW tRCB BW CNT₀ : List Bool)
    (s0 : EnSt) (hs0 : s0.idx = 0) (Lmax cap capA capC capCut capCoef capEnt : ℕ)
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
    Step (StreamController.machine entryM 0)
      ((es.map fun e => entryWord Q PC.length e.1 e.2).length *
        ((2 * entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length + 2) + 2) + 1)
      (enBH P.length s0)
      (enBA (P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) par
        BW CNT₀ cap capA capC capCut capCoef capEnt s0)
      (enBH (P.length + ((es.map fun e => entryWord Q PC.length e.1 e.2).flatMap frame).length)
        ((es.map fun e => entryWord Q PC.length e.1 e.2).foldl (enNext h width Q W side PC c par es) s0))
      (enBA (P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest)
        ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) par
        BW CNT₀ cap capA capC capCut capCoef capEnt
        ((es.map fun e => entryWord Q PC.length e.1 e.2).foldl (enNext h width Q W side PC c par es) s0)) := by
  have hE : (es.map fun e => entryWord Q PC.length e.1 e.2).length = es.length := by simp
  have hne : ∀ r ∈ es.map (fun e => entryWord Q PC.length e.1 e.2), r ≠ [] := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    intro h0
    have := entryWord_length Q PC.length e.1 e.2 (hk e he).2
    rw [h0] at this
    simp at this
  refine streamRunAt entryM 0 P (es.map fun e => entryWord Q PC.length e.1 e.2) rest hne
    (enNext h width Q W side PC c par es) s0 (fun st p => enBH p st)
    (fun st => enBA (P ++ streamTape (es.map fun e => entryWord Q PC.length e.1 e.2) rest)
      ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL) (frame (List.replicate W false) ++ tz)
      (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
      (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) (frame (cbits c) ++ tRCB) par
      BW CNT₀ cap capA capC capCut capCoef capEnt st) (fun _ => rfl) (fun _ _ => rfl)
    (2 * entryCost Q W PC.length h width Lmax (Nat.bits c.natAbs).length + 2) ?_
  intro j hj
  have hj' : j < es.length := by omega
  have hidx : ((es.map fun e => entryWord Q PC.length e.1 e.2).take j |>.foldl
      (enNext h width Q W side PC c par es) s0).idx = j := by
    rw [foldl_enNext_idx, hs0, List.length_take]; omega
  have b := entries_body h width Q W side PC c par es P rest tlPL tz tsStale postQ postW tRCB BW CNT₀
    (((es.map fun e => entryWord Q PC.length e.1 e.2).take j).foldl (enNext h width Q W side PC c par es) s0) j hj'
    hidx Lmax cap capA capC capCut capCoef capEnt hpostQ hpostW hk hLe hLW hfit hcap1 hcapL hcapE hcapS hA1 hA2 hC
    hcut0 hcut1 hcoef hent
  have hst : ((es.map fun e => entryWord Q PC.length e.1 e.2).take (j + 1)).foldl (enNext h width Q W side PC c par es) s0 =
      enNext h width Q W side PC c par es
        (((es.map fun e => entryWord Q PC.length e.1 e.2).take j).foldl (enNext h width Q W side PC c par es) s0)
        ((es.map fun e => entryWord Q PC.length e.1 e.2)[j]'hj) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]; rfl
  rw [hst]
  exact b

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
