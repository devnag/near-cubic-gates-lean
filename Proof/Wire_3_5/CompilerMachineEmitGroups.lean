import Proof.Wire_3_5.CompilerMachineEmitGroupRun

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

theorem gnext_out (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n)) (c : ℤ)
    (par : Bool) (es : List (ℕ × ℕ)) (g : GSt) :
    (gnext h width Q W side PC c par es g).en.out = g.en.out ++ es.flatMap (entryOut h width W side PC c par) := by
  have := foldl_enNext_out h width Q W side PC c par es (es.map fun e => entryWord Q PC.length e.1 e.2)
    { g.en with idx := 0 } (by simp)
  simp only [List.length_map, List.drop_zero, List.take_length] at this
  exact this

theorem gnext_cnt (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n)) (c : ℤ)
    (par : Bool) (es : List (ℕ × ℕ)) (g : GSt) :
    (gnext h width Q W side PC c par es g).en.cnt = g.en.cnt + es.length := by
  have := foldl_enNext_cnt h width Q W side PC c par es (es.map fun e => entryWord Q PC.length e.1 e.2)
    { g.en with idx := 0 }
  simp only [List.length_map] at this
  exact this

theorem gfold_out (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    {α : Type} (cOf : α → ℤ) (parOf : α → Bool) (esOf : α → List (ℕ × ℕ)) :
    ∀ (xs : List α) (g : GSt), (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g).en.out =
      g.en.out ++ xs.flatMap (fun x => (esOf x).flatMap (entryOut h width W side PC (cOf x) (parOf x)))
  | [], g => by simp
  | x :: xs, g => by
    rw [List.foldl_cons, gfold_out h width Q W side PC cOf parOf esOf xs, gnext_out]
    simp [List.append_assoc]

theorem gfold_cnt (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    {α : Type} (cOf : α → ℤ) (parOf : α → Bool) (esOf : α → List (ℕ × ℕ)) :
    ∀ (xs : List α) (g : GSt), (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g).en.cnt =
      g.en.cnt + (xs.map fun x => (esOf x).length).sum
  | [], g => by simp
  | x :: xs, g => by
    rw [List.foldl_cons, gfold_cnt h width Q W side PC cOf parOf esOf xs, gnext_cnt]
    simp; omega

theorem groupCost_mono (n1 n2 c1 c2 e1 e2 : ℕ) (hn : n1 ≤ n2) (hc : c1 ≤ c2) (he : e1 ≤ e2) :
    groupCost n1 c1 e1 ≤ groupCost n2 c2 e2 := by
  unfold groupCost
  gcongr

theorem entryCost_mono_cb (Q W Wm h width L b1 b2 : ℕ) (hb : b1 ≤ b2) :
    entryCost Q W Wm h width L b1 ≤ entryCost Q W Wm h width L b2 := by
  unfold entryCost coefRawCost shiftCost
  gcongr

theorem coefRawCost_mono (Q W b1 b2 : ℕ) (hb : b1 ≤ b2) : coefRawCost Q W b1 ≤ coefRawCost Q W b2 := by
  unfold coefRawCost shiftCost
  gcongr

/-- **All groups**: every lifted occurrence's request words, in the compiler stages' order. -/
theorem groups_loop (h width Q W : ℕ) {n : ℕ} (side : List Bool) (PC : List (List Bool × ExactThresholdGate n))
    {α : Type} (xs : List α) (cOf : α → ℤ) (parOf : α → Bool) (esOf : α → List (ℕ × ℕ)) (enc : α → List Bool)
    (henc : ∀ x, enc x = groupWord (cbits (cOf x)) (parOf x) ((esOf x).map fun e => entryWord Q PC.length e.1 e.2))
    (Pg post tlPL tz tsStale postQ postW BW CNT₀ : List Bool) (g0 : GSt)
    (Lmax Emax CB cap capA capC capCut capCoef capEnt : ℕ)
    (hpostQ : readTapeBit postQ 0 = false) (hpostW : readTapeBit postW 0 = false)
    (hk : ∀ x ∈ xs, ∀ e ∈ esOf x, 1 ≤ e.1 ∧ e.1 ≤ Q)
    (hLe : ∀ x ∈ xs, ∀ e ∈ esOf x, (selAt PC e.2 PC.length).length * h ≤ Lmax) (hLW : Lmax < W)
    (hfit : ∀ x ∈ xs, ∀ e ∈ esOf x, cOf x ≠ 0 → e.1 - 1 + (Nat.bits (cOf x).natAbs).length < W)
    (hE : ∀ x ∈ xs, (esOf x).length ≤ Emax) (hCB : ∀ x ∈ xs, (Nat.bits (cOf x).natAbs).length ≤ CB)
    (hcap1 : 2 * W + 1 ≤ cap) (hcapL : 2 * Lmax + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (Q + PC.length + 1) + 1 ≤ cap) (hcapS : appendCost 0 (2 * (width + width + 1)) 1 ≤ cap)
    (hcapC : 2 * (CB + 1) + 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hA2 : skipCost (2 * (width + width + 1)) (1 + PC.length * h) h ≤ capA)
    (hC : appendCost 0 (2 * (width + width + 1)) (1 + PC.length * h + h) ≤ capC)
    (hcut0 : cut0Cost W Lmax (width + width) ≤ capCut) (hcut1 : cut1Cost W Lmax (width + width) ≤ capCut)
    (hcoef : coefRawCost Q W CB ≤ capCoef)
    (hent : entryCost Q W PC.length h width Lmax CB ≤ capEnt) :
    Step (StreamController.machine groupBodyM 0)
      (xs.length * (groupCost Emax (CB + 1) (2 * entryCost Q W PC.length h width Lmax CB + 2) + 2) + 1)
      (enBH Pg.length g0.en)
      (enBA (Pg ++ xs.flatMap enc ++ false :: post) ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL)
        (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) g0.rcb g0.rpar
        BW CNT₀ cap capA capC capCut capCoef capEnt g0.en)
      (enBH (Pg.length + (xs.flatMap enc).length)
        (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0).en)
      (enBA (Pg ++ xs.flatMap enc ++ false :: post) ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL)
        (frame (List.replicate W false) ++ tz)
        (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
        (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW)
        (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0).rcb
        (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0).rpar
        BW CNT₀ cap capA capC capCut capCoef capEnt
        (xs.foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0).en) := by
  have hne : ∀ x, ∃ l, enc x = true :: l := by
    intro x; rw [henc]; exact ⟨_, rfl⟩
  refine encRun enc hne groupBodyM 0 Pg xs post (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0
    (fun g p => enBH p g.en)
    (fun g => enBA (Pg ++ xs.flatMap enc ++ false :: post) ((PC.flatMap (labRecs h side width)).flatMap frame ++ tlPL)
      (frame (List.replicate W false) ++ tz)
      (streamTape (stackRecs h side width ([] : List (List Bool × ExactThresholdGate n))) tsStale)
      (List.replicate Q true ++ postQ) (List.replicate (width + width) true ++ postW) g.rcb g.rpar
      BW CNT₀ cap capA capC capCut capCoef capEnt g.en) (fun _ => rfl) (fun _ _ => rfl) _ ?_
  intro j hj
  set gj := (xs.take j).foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0
  have hx := List.getElem_mem hj
  have hsplit : Pg ++ xs.flatMap enc ++ false :: post =
      (Pg ++ (xs.take j).flatMap enc) ++ groupWord (cbits (cOf xs[j])) (parOf xs[j])
        ((esOf xs[j]).map fun e => entryWord Q PC.length e.1 e.2) ++ ((xs.drop (j + 1)).flatMap enc ++ false :: post) := by
    rw [enc_split enc xs j hj, henc]; simp only [List.append_assoc]
  have hcbl : (cbits (cOf xs[j])).length = (Nat.bits (cOf xs[j]).natAbs).length + 1 := by simp [cbits]
  have b := group_body h width Q W side PC (cOf xs[j]) (parOf xs[j]) (esOf xs[j]) (Pg ++ (xs.take j).flatMap enc)
    ((xs.drop (j + 1)).flatMap enc ++ false :: post) tlPL tz tsStale postQ postW BW CNT₀ gj Lmax cap capA capC capCut
    capCoef capEnt hpostQ hpostW (hk _ hx) (hLe _ hx) hLW (hfit _ hx) hcap1 hcapL hcapE hcapS
    (by rw [hcbl]; have := hCB _ hx; omega) hA1 hA2 hC hcut0 hcut1
    ((coefRawCost_mono Q W _ CB (hCB _ hx)).trans hcoef)
    ((entryCost_mono_cb Q W PC.length h width Lmax _ CB (hCB _ hx)).trans hent)
  rw [← hsplit] at b
  have hlen : (Pg ++ (xs.take j).flatMap enc).length = Pg.length + ((xs.take j).flatMap enc).length := by simp
  have hlen1 : (Pg ++ (xs.take j).flatMap enc ++ groupWord (cbits (cOf xs[j])) (parOf xs[j])
      ((esOf xs[j]).map fun e => entryWord Q PC.length e.1 e.2)).length =
      Pg.length + ((xs.take (j + 1)).flatMap enc).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]; simp [henc]
  rw [hlen, hlen1] at b
  have hst : (xs.take (j + 1)).foldl (fun g x => gnext h width Q W side PC (cOf x) (parOf x) (esOf x) g) g0 =
      gnext h width Q W side PC (cOf xs[j]) (parOf xs[j]) (esOf xs[j]) gj := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]; rfl
  rw [hst]
  refine b.enlarge (groupCost_mono _ _ _ _ _ _ (hE _ hx) (by rw [hcbl]; have := hCB _ hx; omega) ?_)
  have := entryCost_mono_cb Q W PC.length h width Lmax _ CB (hCB _ hx)
  omega

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
