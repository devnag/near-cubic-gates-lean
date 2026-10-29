import SourceAdapters.RAMACSP.GenItemsPiece

/-!
# The Booleanity blocks (G) of the time rows and of the sorted vertices

Paper: `app:affine-embedding`, "Placement". Every semantic role-zero bit
has its `Y²+Y` check at role three, and every role-one bit at role four, in
the same column. Time checks also carry TIME; final-stage sorted checks
need no lane restriction.

`boolItem tag role area lk lv st`: the item `Y² + Y` of the slot with field tag `tag`, bit index `j` (in `vJ`), role,
area, hosted at role `role + 3`; `den_boolItem`. Pieces (`BP`): a count, a bit index, the fixed tag/role/area and the
slots of the passes, with the proof that each pass's slot has that cell.
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

variable {G : Glob}

/-! ## Items with a general equation printer -/

/-- **One item, any equation printer**: the guard at `lk`, `lv`, `st` and host `h`, then the equation `e`
printed by `body`. -/
theorem den_itemGen {F : Type} [Field F] [CharP F 2] (mk : F → ℕ)
    {l : Routing.Layout} {om dt : ℕ} {s : FS} (hl : LayV l om dt s) (hcap : 2 ^ l.m + 8 ≤ G.cap) (hmN : l.m ≤ G.N)
    (h : SC) (body : P) (e : Routing.Expr F) (lk lv st : E) (vlk vlv vst : ℕ) (hlk : evalE G s lk = vlk)
    (hlv : evalE G s lv = vlv) (hst : evalE G s st = vst) (hlkr : vlk < 2 ^ l.k) (hlvr : vlv < 2 ^ l.k)
    (hstr : vst < 2 ^ l.ell) (hh : (h.ev G s).Ok om dt) (rk : RdE notA (knE lk)) (rv : RdE notA (vaE h lv st))
    (hb : den G s body = (Joins.exprToks mk e).flatMap tokNums) :
    den G s (itemP (knE lk) (vaE h lv st) body) = itemNums mk (guardAt l om vlk vlv vst (h.ev G s), e) := by
  have hp : 0 < 2 ^ l.m := Nat.two_pow_pos _
  rw [den_itemP s _ _ _ rk rv hl.hmH hmN (by omega), evalE_knE hl lk vlk hlk hlkr (by omega),
    evalE_vaE hl h lv st vlv vst hlv hst hlvr hstr hh (by omega), hb]
  rfl

/-- The tokens of `Y² + Y` for the read from `h` to `c`. -/
def boolP (h c : SC) : P :=
  .seq (tokE 1 (.add (offE h c) (.k 1))) (.seq (tokE 4 k0) (.seq (tokE 1 (.add (offE h c) (.k 1))) (tokE 2 k0)))

theorem den_boolP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) {l : Routing.Layout} {om dt : ℕ} {s : FS}
    (hl : LayV l om dt s) (hcap : 2 ^ l.m + 8 ≤ G.cap) (h c : SC) (hh : (h.ev G s).Ok om dt)
    (hc : (c.ev G s).Ok om dt) :
    den G s (boolP h c) =
      (Joins.exprToks mk (boolExpr (localOffset l om (h.ev G s) (c.ev G s)) : Routing.Expr F)).flatMap tokNums := by
  have ho := evalE_offE hl h c hh hc (by omega)
  have hlt := localOffset_lt l om dt hl.hq _ _ hh hc
  have e1 : evalE G s (.add (offE h c) (.k 1)) = localOffset l om (h.ev G s) (c.ev G s) + 1 := by
    show min (evalE G s (offE h c) + min 1 G.cap) G.cap = _
    rw [ho, min_cap (show 1 ≤ G.cap by omega)]; exact min_cap (by omega)
  simp only [boolP, den, tokE, evalE, ho, k0, Nat.zero_min, min_cap (show 1 ≤ G.cap by omega),
    min_cap (show 2 ≤ G.cap by omega), min_cap (show 4 ≤ G.cap by omega),
    min_cap (show localOffset l om (h.ev G s) (c.ev G s) + 1 ≤ G.cap by omega)]
  simp [boolExpr, Joins.exprToks, tokNums, Joins.varCode]

theorem WF_boolP {A : Var → Prop} (hA : ∀ x, layA x → A x) (h c : SC) (hh : h.Rd A) (hc : c.Rd A) :
    WF A (boolP h c) :=
  ⟨⟨trivial, ⟨RdE_offE hA h c hh hc, trivial⟩⟩, ⟨⟨trivial, trivial⟩, ⟨⟨trivial, ⟨RdE_offE hA h c hh hc, trivial⟩⟩,
    ⟨trivial, trivial⟩⟩⟩⟩

theorem Ok_boolP {d : ℕ} (hd : d < 8) (h c : SC) (hh : h.Dp) (hc : c.Dp) : Ok d (boolP h c) := by
  have ho := dE_offE _ _ hh hc
  exact ⟨⟨⟨by simp [dE], hd⟩, by simp only [dE]; omega, hd⟩, ⟨⟨by simp [dE], hd⟩, by simp [k0, dE], hd⟩,
    ⟨⟨by simp [dE], hd⟩, by simp only [dE]; omega, hd⟩, ⟨by simp [dE], hd⟩, by simp [k0, dE], hd⟩

/-- The Booleanity item of the slot with tag `tag`, bit `j` (in `vJ`), role and area. -/
def boolItem (tag role area : ℕ) (lk lv st : E) : P :=
  itemP (knE lk) (vaE ⟨tag, jE, role + 3, 1⟩ lv st) (boolP ⟨tag, jE, role + 3, 1⟩ ⟨tag, jE, role, area⟩)

/-- **One Booleanity item.** -/
theorem den_boolItem {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) {l : Routing.Layout} {om dt : ℕ} {s : FS}
    (hl : LayV l om dt s) (hcap : 2 ^ l.m + 8 ≤ G.cap) (hmN : l.m ≤ G.N) (tag role area : ℕ) (lk lv st : E)
    (vlk vlv vst j : ℕ) (hj : s.env vJ = j) (hlk : evalE G s lk = vlk) (hlv : evalE G s lv = vlv)
    (hst : evalE G s st = vst) (hlkr : vlk < 2 ^ l.k) (hlvr : vlv < 2 ^ l.k) (hstr : vst < 2 ^ l.ell)
    (hc : (⟨tag, j, role, area⟩ : Cell).Ok om dt) (hr : role ≤ 1) (rk : RdE notA lk) (rv : RdE notA lv)
    (rs : RdE notA st) :
    den G s (boolItem tag role area lk lv st) =
      itemNums mk (guardAt l om vlk vlv vst ⟨tag, j, role + 3, 1⟩,
        (boolExpr (localOffset l om ⟨tag, j, role + 3, 1⟩ ⟨tag, j, role, area⟩) : Routing.Expr F)) := by
  have hjE : evalE G s jE = j := hj
  have ehc : (SC.ev G s ⟨tag, jE, role, area⟩) = ⟨tag, j, role, area⟩ := by simp [SC.ev, hjE]
  have ehh : (SC.ev G s ⟨tag, jE, role + 3, 1⟩) = ⟨tag, j, role + 3, 1⟩ := by simp [SC.ev, hjE]
  have hh : (⟨tag, j, role + 3, 1⟩ : Cell).Ok om dt := ⟨hc.1, hc.2.1, show role + 3 < 8 by omega, show 1 < 2 by norm_num⟩
  have := den_itemGen mk hl hcap hmN ⟨tag, jE, role + 3, 1⟩ (boolP ⟨tag, jE, role + 3, 1⟩ ⟨tag, jE, role, area⟩)
    (boolExpr (localOffset l om ⟨tag, j, role + 3, 1⟩ ⟨tag, j, role, area⟩)) lk lv st vlk vlv vst hlk hlv hst hlkr
    hlvr hstr (by rw [ehh]; exact hh) (rd_knE (show vUK ≠ vA by decide) lk rk)
    (rd_vaE (A := notA) (fun x hx => by
        unfold notA
        rcases hx with h | h | h | h | h | h | h <;> (subst h; decide)) ⟨tag, jE, role + 3, 1⟩
      (show vJ ≠ vA by decide : RdE notA (.v vJ)) lv st rv rs)
    (by rw [den_boolP mk hl hcap _ _ (by rw [ehh]; exact hh) (by rw [ehc]; exact hc), ehh, ehc])
  rw [ehh] at this
  exact this

/-! ## Time Booleanity -/

/-- A piece of the time slots: count, bit index, and slots whose cells differ only in the bit index. -/
structure BPT where
  c : Cnt
  jk : JK
  slot : ℕ → TSlot
  hcell : ∀ K L i, tCell K L (slot i) =
    ⟨(tCell K L (slot 0)).tag, jk.val i, (tCell K L (slot 0)).role, (tCell K L (slot 0)).area⟩

variable (V : Verifier)

/-- Its printer (guard TIME, stage `0`). -/
def BPT.prog (pc : BPT) : P :=
  Pc.prog ⟨pc.c, pc.jk, boolItem (tCell (regCount V) (codeLen V) (pc.slot 0)).tag
    (tCell (regCount V) (codeLen V) (pc.slot 0)).role (tCell (regCount V) (codeLen V) (pc.slot 0)).area (.v 28) k0 k0⟩

/-- A range piece. -/
def bpr (c : Cnt) (sl : ℕ → TSlot) (h : ∀ K L i, tCell K L (sl i) =
    ⟨(tCell K L (sl 0)).tag, i, (tCell K L (sl 0)).role, (tCell K L (sl 0)).area⟩) : BPT := ⟨c, .idx, sl, h⟩

/-- A single slot. -/
def bps (sl : TSlot) (h : ∀ K L, (tCell K L sl).bit = 0) : BPT :=
  ⟨.one, .zero, fun _ => sl, fun K L _ => by
    show tCell K L sl = ⟨(tCell K L sl).tag, 0, (tCell K L sl).role, (tCell K L sl).area⟩
    rw [← h K L]⟩

/-- **The pieces of the time slots.** -/
def tbPieces (K L : ℕ) : List BPT :=
  [bpr .w TSlot.pc (fun _ _ _ => rfl)] ++ (List.range K).map (fun r => bps (TSlot.fl r) (fun _ _ => rfl)) ++
  (List.range K).map (fun r => bpr .w (TSlot.rg r) (fun _ _ _ => rfl)) ++
  (List.range L).map (fun p => bps (TSlot.e p) (fun _ _ => rfl)) ++
  (List.range L).map (fun p => bps (TSlot.o p) (fun _ _ => rfl)) ++
  [bpr .w TSlot.X (fun _ _ _ => rfl), bps .XF (fun _ _ => rfl), bpr .w TSlot.Y (fun _ _ _ => rfl),
   bpr .w TSlot.AD (fun _ _ _ => rfl), bpr .wm1 TSlot.CA (fun _ _ _ => rfl), bpr .w TSlot.SB (fun _ _ _ => rfl),
   bpr .w TSlot.BO (fun _ _ _ => rfl), bpr .w TSlot.AN (fun _ _ _ => rfl), bpr .w TSlot.OZ (fun _ _ _ => rfl),
   bps .GT (fun _ _ => rfl), bpr .w TSlot.Z (fun _ _ _ => rfl), bps .ZF (fun _ _ => rfl),
   bpr .w TSlot.RV (fun _ _ _ => rfl), bps .RF (fun _ _ => rfl), bpr .w TSlot.MV (fun _ _ _ => rfl),
   bpr .taum1 TSlot.TC (fun _ _ _ => rfl), bpr .tau TSlot.cA (fun _ _ _ => rfl),
   bpr .beta1 TSlot.cB (fun _ _ _ => rfl), bpr .taum1 TSlot.AC (fun _ _ _ => rfl),
   bpr .beta TSlot.BC (fun _ _ _ => rfl), bps .aA (fun _ _ => rfl), bps .aB (fun _ _ => rfl),
   bpr .w TSlot.npc (fun _ _ _ => rfl)] ++
  (List.range K).map (fun r => bps (TSlot.nfl r) (fun _ _ => rfl)) ++
  (List.range K).map (fun r => bpr .w (TSlot.nrg r) (fun _ _ _ => rfl)) ++
  [bpr .tau TSlot.ncA (fun _ _ _ => rfl), bpr .beta1 TSlot.ncB (fun _ _ _ => rfl),
   bpr .tau TSlot.TSN (fun _ _ _ => rfl)]

theorem timeSlotList_pieces (d : Dims) :
    timeSlotList d = (tbPieces d.K d.L).flatMap (fun pc => (List.range (pc.c.val d)).map pc.slot) := by
  simp [timeSlotList, tbPieces, List.flatMap_append, List.flatMap_map, bpr, bps, Cnt.val, Function.comp_def,
    List.flatMap_singleton', range_one_map, flatMap_singleton_eq_map]

/-- The Booleanity item of a time slot in `machineItems`. -/
def tbItem {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (sl : TSlot) :
    Routing.Pattern (ownLayout V r.2).m × Routing.Expr F :=
  let c := tCell (regCount V) (codeLen V) sl
  (guardAt (ownLayout V r.2) (wordExp V r.2) (2 ^ tau V r.2) 0 0 ⟨c.tag, c.bit, c.role + 3, 1⟩,
    boolExpr (localOffset (ownLayout V r.2) (wordExp V r.2) ⟨c.tag, c.bit, c.role + 3, 1⟩ c))

theorem timeSlotList_own (r : ClockRequest) :
    timeSlotList (dims (ownRam V r) (tau V r.2)) = (tbPieces (regCount V) (codeLen V)).flatMap
      (fun pc => (List.range (pc.c.val (dims (ownRam V r) (tau V r.2)))).map pc.slot) := by
  have h := timeSlotList_pieces (dims (ownRam V r) (tau V r.2))
  have hL : (dims (ownRam V r) (tau V r.2)).L = codeLen V := mnCode_length V _ _ _ _
  rw [hL] at h
  exact h

/-- **The time Booleanity block.** -/
def tbBlockP : P := seqL ((tbPieces (regCount V) (codeLen V)).map (BPT.prog V))

theorem layout_room (r : ClockRequest) (hR : Room V r G) :
    2 ^ (ownLayout V r.2).m + 8 ≤ G.cap ∧ (ownLayout V r.2).m ≤ G.N := by
  have hpd := pow_dom V r
  have := hR.cap
  have h8 : 8 ≤ 2 ^ (domExp V r.2 + 8) := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (show 3 ≤ domExp V r.2 + 8 by omega) : 2 ^ 3 ≤ _)
  have := cB_16 V
  refine ⟨by omega, ?_⟩
  rw [ownLayout_m]; have := hR.mN; omega

theorem den_tbBlock {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (r : ClockRequest) (hR : Room V r G) {s : FS}
    (hb : Base V r s) :
    den G s (tbBlockP V) =
      (timeSlotList (dims (ownRam V r) (tau V r.2))).flatMap (fun sl => itemNums mk (tbItem V r sl)) := by
  obtain ⟨hcap, hmN⟩ := layout_room V r hR
  have hτ := tau_lt_wordW_all V r.2
  rw [tbBlockP, den_seqL, List.flatMap_map, timeSlotList_own V r, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pc hpc
  rw [BPT.prog, den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial _
    (fun i => itemNums mk (tbItem V r (pc.slot i))), List.flatMap_map]
  intro i hi s' hb' _ hj
  have hmem : pc.slot i ∈ timeSlotList (dims (ownRam V r) (tau V r.2)) := by
    rw [timeSlotList_own V r]
    exact List.mem_flatMap.mpr ⟨pc, hpc, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩
  have hok := cellT_ok V r (.inl (pc.slot i)) (mem_timeSlotList _ _ hmem)
  have hc := pc.hcell (regCount V) (codeLen V) i
  simp only [cellT] at hok
  rw [hc] at hok
  have hr : (tCell (regCount V) (codeLen V) (pc.slot 0)).role ≤ 1 := (tCell_role _ _ _).1
  have hl := hb'.lay
  have hTk : 2 ^ tau V r.2 < 2 ^ (ownLayout V r.2).k := Nat.pow_lt_pow_right (by norm_num) (by
    show tau V r.2 < laneExp V r.2; unfold laneExp; omega)
  rw [den_boolItem mk hl hcap hmN _ _ _ (.v 28) k0 k0 (2 ^ tau V r.2) 0 0 _ hj hb'.pv.T (Nat.zero_min _)
    (Nat.zero_min _) hTk (Nat.two_pow_pos _) (Nat.two_pow_pos _) hok hr (show (28 : Var) ≠ vA by decide) trivial
    trivial]
  unfold tbItem
  rw [hc]

theorem WF_tbBlock : WF baseA (tbBlockP V) := by
  apply WF_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  refine WF_loopBind _ _ _ (rd_cnt pc.c) (rd_jk pc.jk) ?_
  have hh : SC.Rd itemA ⟨(tCell (regCount V) (codeLen V) (pc.slot 0)).tag, jE,
    (tCell (regCount V) (codeLen V) (pc.slot 0)).role + 3, 1⟩ := itemA_J
  have hc : SC.Rd itemA ⟨(tCell (regCount V) (codeLen V) (pc.slot 0)).tag, jE,
    (tCell (regCount V) (codeLen V) (pc.slot 0)).role, (tCell (regCount V) (codeLen V) (pc.slot 0)).area⟩ := itemA_J
  exact WF_itemP (itemA_base (Or.inl ⟨by decide, by decide⟩)) not_itemA_vA _ _ _
    (rd_knE (layA_itemA _ (by simp [layA])) _ itemA_28) (rd_vaE layA_itemA _ hh _ _ trivial trivial)
    (WF_boolP layA_itemA _ _ hh hc)

theorem Ok_tbBlock : Ok 0 (tbBlockP V) := by
  apply Ok_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  refine Ok_loopBind _ _ _ (dE_cnt pc.c) (dE_jk pc.jk) ?_
  have hh : SC.Dp ⟨(tCell (regCount V) (codeLen V) (pc.slot 0)).tag, jE,
    (tCell (regCount V) (codeLen V) (pc.slot 0)).role + 3, 1⟩ := show dE jE ≤ 3 by simp [jE, dE]
  have hc : SC.Dp ⟨(tCell (regCount V) (codeLen V) (pc.slot 0)).tag, jE,
    (tCell (regCount V) (codeLen V) (pc.slot 0)).role, (tCell (regCount V) (codeLen V) (pc.slot 0)).area⟩ :=
    show dE jE ≤ 3 by simp [jE, dE]
  exact Ok_itemP (by norm_num) _ _ _ (by simp [knE, dE]) (dE_vaE _ _ _ hh (by simp [k0, dE]) (by simp [k0, dE]))
    (Ok_boolP (by norm_num) _ _ hh hc)

end NearCubicGates.Adapters.RAMACSP.Gen.Items
