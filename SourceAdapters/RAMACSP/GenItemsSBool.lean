import SourceAdapters.RAMACSP.GenItemsSBlock

/-!
# The Booleanity block of the sorted vertices

Paper: "Placement" in `app:affine-embedding`. Sorted semantic values receive
Booleanity checks at the final stage in their corresponding columns; these
checks require no lane restriction.

The sorted slots (`sortSlotList`): the predecessor's record bits, the borrow bits `ob_l` (by key-bit segments), the
comparison and load/read flags. Each is printed by `boolItem` hosted at the final stage (`den_sbBlock`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob} (V : Verifier)

/-- The Booleanity item of a sorted slot in `machineItems`. -/
def sbItem {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (sl : SSlot) :
    Routing.Pattern (ownLayout V r.2).m × Routing.Expr F :=
  let c := sCell (wordW V r.2) sl
  (guardAt (ownLayout V r.2) (wordExp V r.2) 0 0 (2 * (ownLayout V r.2).k - 1) ⟨c.tag, c.bit, c.role + 3, 1⟩,
    boolExpr (localOffset (ownLayout V r.2) (wordExp V r.2) ⟨c.tag, c.bit, c.role + 3, 1⟩ c))

/-- A sorted Booleanity piece. -/
def sbP (c : Cnt) (jk : JK) (tag role area : ℕ) : P := Pc.prog ⟨c, jk, boolItem tag role area k0 k0 finE⟩

theorem den_sbP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (r : ClockRequest) (hR : Room V r G) {s : FS}
    (hb : Base V r s) (c : Cnt) (jk : JK) (tag role area : ℕ) (hr : role ≤ 1) (slot : ℕ → SSlot)
    (hcell : ∀ i < c.val (dims (ownRam V r) (tau V r.2)),
      sCell (wordW V r.2) (slot i) = ⟨tag, jk.val i, role, area⟩)
    (hact : ∀ i < c.val (dims (ownRam V r) (tau V r.2)), (slot i).Active (dims (ownRam V r) (tau V r.2))) :
    den G s (sbP c jk tag role area) =
      ((List.range (c.val (dims (ownRam V r) (tau V r.2)))).map slot).flatMap (fun sl => itemNums mk (sbItem V r sl)) := by
  obtain ⟨hcap, hmN⟩ := layout_room V r hR
  have hτ := tau_lt_wordW_all V r.2
  have hd := dims_own V r
  rw [sbP, den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial _
    (fun i => itemNums mk (sbItem V r (slot i))), List.flatMap_map]
  intro i hi s' hb' _ hj
  have hi2 : i < c.val (dims (ownRam V r) (tau V r.2)) := hi
  have hj2 : s'.env vJ = jk.val i := hj
  have hok : (sCell (wordW V r.2) (slot i)).Ok (wordExp V r.2) (tagExp V) := by
    have ha := hact i hi2
    rw [hd] at ha
    exact sCell_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) hτ (Nat.sub_le _ _) (ftags_bound V) (.inl (slot i)) ha
  rw [hcell i hi2] at hok
  have hl := hb'.lay
  rw [den_boolItem mk hl hcap hmN tag role area k0 k0 finE 0 0 (2 * laneExp V r.2 - 1) _ hj2 (Nat.zero_min _)
    (Nat.zero_min _) (eval_finE V r hR hb') (Nat.two_pow_pos _) (Nat.two_pow_pos _) (fin_lt V r) hok hr trivial
    trivial ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩]
  unfold sbItem
  rw [hcell i hi2]
  rfl

/-- **The printer of the sorted Booleanity block.** -/
def sbBlockP : P :=
  seqL [sbP .w .idx RecField.va.tag 1 1, sbP .w .idx RecField.ad.tag 1 1, sbP .tau .idx RecField.ts.tag 1 1,
    sbP .one .zero RecField.ph.tag 1 1, sbP .one .zero RecField.rgn.tag 1 1, sbP .one .zero RecField.act.tag 1 1,
    sbP .w .idx 8 0 1, sbP .seg1 .idx 9 0 1, sbP .seg2 .idx 10 0 1, sbP .one .zero 11 0 1,
    sbP .w .idx 12 0 1, sbP .one .zero 13 0 1, sbP .one .zero 14 0 1, sbP .one .zero 15 0 1,
    sbP .w .idx 16 0 1, sbP .one .zero 17 0 1, sbP .one .zero 18 0 1]

/-- The sorted slots with the key-bit range and the comparison bits cut into pieces. -/
theorem sortSlotList_seg (d : Dims) (hw : 1 ≤ d.w) (hτ : d.τ < d.w) :
    sortSlotList d = (List.range d.w).map (SSlot.prev .va) ++ (List.range d.w).map (SSlot.prev .ad) ++
      (List.range d.τ).map (SSlot.prev .ts) ++ [SSlot.prev .ph 0, SSlot.prev .rgn 0, SSlot.prev .act 0] ++
      ((List.range d.w).map (fun i => SSlot.ob (0 * d.w + i)) ++
        (List.range (d.τ + 2 - (d.τ + 2 - d.w))).map (fun i => SSlot.ob (1 * d.w + i)) ++
        (List.range (d.τ + 2 - d.w)).map (fun i => SSlot.ob (2 * d.w + i))) ++ [SSlot.both] ++
      ((List.range d.w).map SSlot.so ++ [SSlot.so d.w]) ++ [SSlot.u, SSlot.g] ++ (List.range d.w).map SSlot.ev ++
      [SSlot.gA1, SSlot.gA] := by
  unfold sortSlotList
  rw [show d.κ = d.w + d.τ + 2 from rfl, range_kappa d.w d.τ hw hτ, List.range_succ]
  simp [List.map_append, List.map_map, Function.comp_def, RecField.width]

/-- **The sorted Booleanity block prints the sorted Booleanity items of `machineItems`.** -/
theorem den_sbBlock {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (r : ClockRequest) (hR : Room V r G) {s : FS}
    (hb : Base V r s) :
    den G s sbBlockP =
      (sortSlotList (dims (ownRam V r) (tau V r.2))).flatMap (fun sl => itemNums mk (sbItem V r sl)) := by
  have hτ := tau_lt_wordW_all V r.2
  have hw1 : 1 ≤ wordW V r.2 := by omega
  have hdw := dims_w V r
  have hdt := dims_tau V r
  have hk : (dims (ownRam V r) (tau V r.2)).κ = wordW V r.2 + tau V r.2 + 2 := by
    show (dims (ownRam V r) (tau V r.2)).w + (dims (ownRam V r) (tau V r.2)).τ + 2 = _; rw [hdw, hdt]
  have hw0 : 0 < wordW V r.2 := by omega
  have hob : ∀ seg i, i < wordW V r.2 →
      sCell (wordW V r.2) (.ob (seg * wordW V r.2 + i)) = ⟨8 + seg, i, 0, 1⟩ := by
    intro seg i hi
    obtain ⟨e1, e2⟩ := divmod_eq (x := seg * wordW V r.2 + i) (w := wordW V r.2) (qq := seg) (r := i) hw0 rfl hi
    simp only [sCell, e1, e2]
  rw [sortSlotList_seg _ (by rw [hdw]; omega) (by rw [hdw, hdt]; omega)]
  simp only [sbBlockP, den_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
    List.singleton_append, List.cons_append, List.nil_append]
  rw [den_sbP V mk r hR hb .w .idx RecField.va.tag 1 1 le_rfl (SSlot.prev .va) (fun _ _ => rfl)
      (fun i hi => by simp only [Cnt.val, hdw] at hi; exact ⟨by simp, by simp [RecField.width, hdw]; omega⟩),
    den_sbP V mk r hR hb .w .idx RecField.ad.tag 1 1 le_rfl (SSlot.prev .ad) (fun _ _ => rfl)
      (fun i hi => by simp only [Cnt.val, hdw] at hi; exact ⟨by simp, by simp [RecField.width, hdw]; omega⟩),
    den_sbP V mk r hR hb .tau .idx RecField.ts.tag 1 1 le_rfl (SSlot.prev .ts) (fun _ _ => rfl)
      (fun i hi => by simp only [Cnt.val, hdt] at hi; exact ⟨by simp, by simp [RecField.width, hdt]; omega⟩),
    den_sbP V mk r hR hb .one .zero RecField.ph.tag 1 1 le_rfl (fun _ => SSlot.prev .ph 0) (fun _ _ => rfl)
      (fun i hi => ⟨by simp, by simp [RecField.width]⟩),
    den_sbP V mk r hR hb .one .zero RecField.rgn.tag 1 1 le_rfl (fun _ => SSlot.prev .rgn 0) (fun _ _ => rfl)
      (fun i hi => ⟨by simp, by simp [RecField.width]⟩),
    den_sbP V mk r hR hb .one .zero RecField.act.tag 1 1 le_rfl (fun _ => SSlot.prev .act 0) (fun _ _ => rfl)
      (fun i hi => ⟨by simp, by simp [RecField.width]⟩),
    den_sbP V mk r hR hb .w .idx 8 0 1 (by norm_num) (fun i => SSlot.ob (0 * (dims (ownRam V r) (tau V r.2)).w + i))
      (fun i hi => by simp only [Cnt.val, hdw] at hi ⊢; exact hob 0 i hi)
      (fun i hi => by simp only [Cnt.val, hdw] at hi; show _ < _; rw [hk, hdw]; omega),
    den_sbP V mk r hR hb .seg1 .idx 9 0 1 (by norm_num)
      (fun i => SSlot.ob (1 * (dims (ownRam V r) (tau V r.2)).w + i))
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi ⊢; exact hob 1 i (by omega))
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi; show _ < _; rw [hk, hdw]; omega),
    den_sbP V mk r hR hb .seg2 .idx 10 0 1 (by norm_num)
      (fun i => SSlot.ob (2 * (dims (ownRam V r) (tau V r.2)).w + i))
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi ⊢; exact hob 2 i (by omega))
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi; show _ < _; rw [hk, hdw]; omega),
    den_sbP V mk r hR hb .one .zero 11 0 1 (by norm_num) (fun _ => SSlot.both) (fun _ _ => rfl) (fun _ _ => trivial),
    den_sbP V mk r hR hb .w .idx 12 0 1 (by norm_num) SSlot.so
      (fun i hi => by simp only [Cnt.val, hdw] at hi; simp [sCell, hi, JK.val])
      (fun i hi => by simp only [Cnt.val, hdw] at hi; show i ≤ _; rw [hdw]; omega),
    den_sbP V mk r hR hb .one .zero 13 0 1 (by norm_num) (fun _ => SSlot.so (dims (ownRam V r) (tau V r.2)).w)
      (fun i hi => by simp [sCell, hdw, JK.val]) (fun _ _ => le_rfl),
    den_sbP V mk r hR hb .one .zero 14 0 1 (by norm_num) (fun _ => SSlot.u) (fun _ _ => rfl) (fun _ _ => trivial),
    den_sbP V mk r hR hb .one .zero 15 0 1 (by norm_num) (fun _ => SSlot.g) (fun _ _ => rfl) (fun _ _ => trivial),
    den_sbP V mk r hR hb .w .idx 16 0 1 (by norm_num) SSlot.ev (fun _ _ => rfl)
      (fun i hi => by simp only [Cnt.val, hdw] at hi; show i < _; rw [hdw]; exact hi),
    den_sbP V mk r hR hb .one .zero 17 0 1 (by norm_num) (fun _ => SSlot.gA1) (fun _ _ => rfl) (fun _ _ => trivial),
    den_sbP V mk r hR hb .one .zero 18 0 1 (by norm_num) (fun _ => SSlot.gA) (fun _ _ => rfl) (fun _ _ => trivial)]
  simp only [Cnt.val, List.append_assoc, range_one_map, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.singleton_append]

theorem WF_sbP (c : Cnt) (jk : JK) (tag role area : ℕ) : WF baseA (sbP c jk tag role area) := by
  refine WF_loopBind _ _ _ (rd_cnt c) (rd_jk jk) ?_
  have hh : SC.Rd itemA ⟨tag, jE, role + 3, 1⟩ := itemA_J
  have hc : SC.Rd itemA ⟨tag, jE, role, area⟩ := itemA_J
  exact WF_itemP (itemA_base (Or.inl ⟨by decide, by decide⟩)) not_itemA_vA _ _ _
    (rd_knE (layA_itemA _ (by simp [layA])) _ trivial)
    (rd_vaE layA_itemA _ hh _ _ trivial ⟨⟨trivial, itemA_base (Or.inl ⟨by decide, by decide⟩)⟩, trivial⟩)
    (WF_boolP layA_itemA _ _ hh hc)

theorem Ok_sbP (c : Cnt) (jk : JK) (tag role area : ℕ) : Ok 0 (sbP c jk tag role area) := by
  refine Ok_loopBind _ _ _ (dE_cnt c) (dE_jk jk) ?_
  have hh : SC.Dp ⟨tag, jE, role + 3, 1⟩ := show dE jE ≤ 3 by simp [jE, dE]
  have hc : SC.Dp ⟨tag, jE, role, area⟩ := show dE jE ≤ 3 by simp [jE, dE]
  exact Ok_itemP (by norm_num) _ _ _ (by simp [knE, k0, dE]) (dE_vaE _ _ _ hh (by simp [k0, dE]) dE_finE)
    (Ok_boolP (by norm_num) _ _ hh hc)

theorem WF_sbBlock : WF baseA sbBlockP := by
  apply WF_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact WF_sbP _ _ _ _ _

theorem Ok_sbBlock : Ok 0 sbBlockP := by
  apply Ok_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Ok_sbP _ _ _ _ _

end NearCubicGates.Adapters.RAMACSP.Gen.Items
