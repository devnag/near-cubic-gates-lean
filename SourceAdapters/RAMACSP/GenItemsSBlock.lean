import SourceAdapters.RAMACSP.GenItemsBool

/-!
# The SORT block of the item stream

Paper: the sorted equations (S1)–(S5) of `def:event-trace` and their placement
in `app:affine-embedding`. The 17 sorted templates are hosted at the final
stage, role two, machine area, without a lane restriction. The key's borrow
chain is split into segments of at most w bits.

The sorted equations are hosted at the final stage `2k − 1` (`finE`), with no lane bits. The key-bit range of (S2)
is cut into the segments `l = s·w + j` (`range_kappa`: `κ = w + τ + 2 ≤ 3w`). `den_sBlock`: the printer of the
pieces prints the sorted items of `machineItems`, in order.
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

/-! ## Facts of the sorted side -/

/-- The final stage `2k − 1` (`k` in 31). -/
def finE : E := .sub (.mul (.k 2) (.v 31)) (.k 1)

theorem eval_finE (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) :
    evalE G s finE = 2 * laneExp V r.2 - 1 := by
  have hk : 2 * laneExp V r.2 < 2 ^ domExp V r.2 := by
    have h1 := two_laneExp_le V r.2
    have h2 : 2 ^ stageExp V r.2 < 2 ^ domExp V r.2 := Nat.pow_lt_pow_right (by norm_num) (by
      unfold domExp laneExp; omega)
    omega
  have h3 : 2 ^ domExp V r.2 ≤ 2 ^ (domExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc := hR.cap
  have h16 := cB_16 V
  show evalE G s (.mul (.k 2) (.v 31)) - min 1 G.cap = _
  simp only [evalE, hb.pv.k, min_cap (show 2 ≤ G.cap by omega), min_cap (show 1 ≤ G.cap by omega)]
  rw [min_cap (by omega)]

theorem fin_lt (r : ClockRequest) : 2 * laneExp V r.2 - 1 < 2 ^ (ownLayout V r.2).ell := by
  have := two_laneExp_le V r.2
  show 2 * laneExp V r.2 - 1 < 2 ^ stageExp V r.2
  have : 1 ≤ laneExp V r.2 := by unfold laneExp; omega
  omega

theorem sCell_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W) (hβ : β ≤ τ)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (v : SVar) (hv : v.Active ⟨W, K, L, τ, β⟩) : (cellS W v).Ok om dt := by
  cases v with
  | inl s => exact sCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hF s hv
  | inr s => exact recCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF s hv

theorem sHost_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (q : SEq) (hq : q.Active ⟨W, K, L, τ, β⟩) :
    (⟨sTag W q, sBit W q, 2, 1⟩ : Cell).Ok om dt :=
  sHost_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hF q hq

/-! ## Sorted items -/

/-- The printer of a sorted item: guard at the final stage, host tag `tag`, the tree `x`. -/
def itemS (tag : ℕ) (x : SX) : P :=
  itemP (knE k0) (vaE ⟨tag, jE, 2, 1⟩ k0 finE) (tokP ⟨tag, jE, 2, 1⟩ x)

/-- The item of the sorted equation `q` in `machineItems`. -/
def sItem {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (q : SEq) :
    Routing.Pattern (ownLayout V r.2).m × Routing.Expr F :=
  (guardAt (ownLayout V r.2) (wordExp V r.2) 0 0 (2 * (ownLayout V r.2).k - 1)
      ⟨sTag (wordW V r.2) q, sBit (wordW V r.2) q, 2, 1⟩,
    toRouting (sRead (ownLayout V r.2) (wordExp V r.2) (wordW V r.2) ⟨sTag (wordW V r.2) q, sBit (wordW V r.2) q, 2, 1⟩)
      (sortEq (dims (ownRam V r) (tau V r.2)) q))

/-- **A sorted item**, from a template whose evaluation is the equation's tree of cells. -/
theorem den_itemS_gen {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (q : SEq)
    (hq : q.Active (dims (ownRam V r) (tau V r.2))) (tag : ℕ) (htag : sTag (wordW V r.2) q = tag)
    (hj : s.env vJ = sBit (wordW V r.2) q) (x : SX)
    (hx : SX.ev G s x = xmap (cellS (wordW V r.2)) (sortEq (dims (ownRam V r) (tau V r.2)) q)) :
    den G s (itemS tag x) = itemNums mk (sItem V r q) := by
  obtain ⟨hcap, hmN⟩ := layout_room V r hR
  have hl := hb.lay
  have hd := dims_own V r
  have hτ := tau_lt_wordW_all V r.2
  have hq' := hq
  rw [hd] at hq'
  have hhost : (SC.ev G s ⟨tag, jE, 2, 1⟩) = ⟨sTag (wordW V r.2) q, sBit (wordW V r.2) q, 2, 1⟩ := by
    simp only [SC.ev, jE, evalE, hj, htag]
  have hhok : (SC.ev G s ⟨tag, jE, 2, 1⟩).Ok (wordExp V r.2) (tagExp V) := by
    rw [hhost]
    exact sHost_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) hτ (ftags_bound V) q hq'
  have hw1 : 1 ≤ (dims (ownRam V r) (tau V r.2)).w := by
    rw [hd]; show 1 ≤ wordW V r.2; rw [wordW_eq]; exact Nat.one_le_two_pow
  have hvx : ∀ c ∈ (SX.ev G s x).vars, c.Ok (wordExp V r.2) (tagExp V) := by
    rw [hx, vars_xmap]
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    have hact := sortEq_reads_active _ hw1 q hq v hv
    rw [hd] at hact
    exact sCell_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) hτ (Nat.sub_le _ _) (ftags_bound V) v hact
  rw [itemS, den_item mk hm0 hm1 hl hcap hmN ⟨tag, jE, 2, 1⟩ x k0 k0 finE 0 0 (2 * laneExp V r.2 - 1)
    (Nat.zero_min _) (Nat.zero_min _) (eval_finE V r hR hb) (Nat.two_pow_pos _) (Nat.two_pow_pos _) (fin_lt V r) hhok
    hvx (rd_knE (show vUK ≠ vA by decide) _ trivial)
    (rd_vaE (A := notA) (fun x hx => by
        unfold notA
        rcases hx with h | h | h | h | h | h | h <;> (subst h; decide)) ⟨tag, jE, 2, 1⟩
      (show vJ ≠ vA by decide : RdE notA (.v vJ)) _ _ trivial
      ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩), hx, ← toRouting_xmap, hhost]
  unfold sItem
  congr 3
  funext v
  exact (sRead_eq' _ _ _ _ v).symm

theorem dims_w (r : ClockRequest) : (dims (ownRam V r) (tau V r.2)).w = wordW V r.2 := by rw [dims_own V r]
theorem dims_tau (r : ClockRequest) : (dims (ownRam V r) (tau V r.2)).τ = tau V r.2 := by rw [dims_own V r]

/-- The sorted state at bit index `j`. -/
theorem sortV_of (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (j : ℕ)
    (hj : s.env vJ = j) (hjw : j < wordW V r.2) :
    SortV (G := G) (dims (ownRam V r) (tau V r.2)).w (dims (ownRam V r) (tau V r.2)).τ j s := by
  have hτ := tau_lt_wordW_all V r.2
  have h2 := wordW_lt_dom V r.2
  have h4 : 4 * 2 ^ domExp V r.2 ≤ 2 ^ (domExp V r.2 + 8) := by
    rw [pow_add]; have : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [this]; omega
  have hc := hR.cap
  have h16 := cB_16 V
  rw [dims_w, dims_tau]
  exact ⟨hj, hb.pv.w, hb.pv.ta, hjw, hτ, by omega⟩

/-! ## The key-bit segments -/

theorem range_kappa (w τ : ℕ) (hw : 1 ≤ w) (hτ : τ < w) :
    List.range (w + τ + 2) = (List.range w).map (0 * w + ·) ++ (List.range (τ + 2 - (τ + 2 - w))).map (1 * w + ·) ++
      (List.range (τ + 2 - w)).map (2 * w + ·) := by
  have e0 : (List.range w).map (0 * w + ·) = List.range w := by simp
  rw [e0, List.append_assoc]
  by_cases h : τ + 2 ≤ w
  · have e1 : τ + 2 - w = 0 := by omega
    rw [e1, show τ + 2 - 0 = τ + 2 from rfl, show w + τ + 2 = w + (τ + 2) by ring, List.range_add]
    simp
  · have e1 : τ + 2 - w = 1 := by omega
    have e2 : τ + 2 - 1 = w := by omega
    rw [e1, e2, show w + τ + 2 = w + w + 1 by omega, List.range_add, List.range_add]
    simp only [List.append_assoc, one_mul]
    congr 2
    simp; ring

/-- The sorted equations with the key-bit range cut into segments. -/
theorem sortEqList_seg (d : Dims) (hw : 1 ≤ d.w) (hτ : d.τ < d.w) :
    sortEqList d = [SEq.act, SEq.both] ++ ((List.range d.w).map (fun i => SEq.borrow (0 * d.w + i)) ++
      (List.range (d.τ + 2 - (d.τ + 2 - d.w))).map (fun i => SEq.borrow (1 * d.w + i)) ++
      (List.range (d.τ + 2 - d.w)).map (fun i => SEq.borrow (2 * d.w + i))) ++ [SEq.strict, SEq.soFirst] ++
      (List.range d.w).map SEq.soNext ++ [SEq.u, SEq.g] ++ (List.range d.w).map SEq.ev ++
      (List.range d.w).map SEq.load ++ [SEq.gA1, SEq.gA, SEq.same, SEq.phase] ++ (List.range d.w).map SEq.value := by
  unfold sortEqList
  rw [show d.κ = d.w + d.τ + 2 from rfl, range_kappa d.w d.τ hw hτ]
  simp [List.map_append, List.map_map, Function.comp_def]

/-! ## The printer of the SORT block -/

/-- A single sorted equation (bit `0`). -/
def sSingle (q : SEq) : P := Pc.prog ⟨.one, .zero, itemS (sTag 1 q) (tmplS q)⟩

/-- A sorted template over `j < w`. -/
def sRange (q : SEq) : P := Pc.prog ⟨.w, .idx, itemS (sTag 1 q) (tmplS q)⟩

/-- Segment `seg` of (S2). -/
def sSeg (seg : ℕ) (c : Cnt) : P := Pc.prog ⟨c, .idx, itemS (2 + seg) (tmplS (.borrow seg))⟩

/-- **The printer of the SORT block.** -/
def sBlockP : P :=
  seqL [sSingle .act, sSingle .both, sSeg 0 .w, sSeg 1 .seg1, sSeg 2 .seg2, sSingle .strict, sSingle .soFirst,
    sRange (.soNext 0), sSingle .u, sSingle .g, sRange (.ev 0), sRange (.load 0), sSingle .gA1, sSingle .gA,
    sSingle .same, sSingle .phase, sRange (.value 0)]

section Den

variable {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
  (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s)
include hm0 hm1 hR hb

theorem den_sSingle (q : SEq) (hq : q.Active (dims (ownRam V r) (tau V r.2))) (hnb : ∀ l, q ≠ .borrow l)
    (hbit : ∀ w, sBit w q = 0) (htag : ∀ w, sTag w q = sTag 1 q) :
    den G s (sSingle q) = itemNums mk (sItem V r q) := by
  have hc := den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial ⟨.one, .zero, itemS (sTag 1 q) (tmplS q)⟩
    (fun _ => itemNums mk (sItem V r q)) (by
      intro i hi s' hb' _ hj
      have hj' : s'.env vJ = sBit (wordW V r.2) q := by rw [hj, hbit]; rfl
      have hτ := tau_lt_wordW_all V r.2
      have hsv := sortV_of V r hR hb' _ hj' (by rw [hbit]; omega)
      exact den_itemS_gen V mk hm0 hm1 r hR hb' q hq _ (htag _) hj' _
        (by rw [← dims_w V r]; exact tmplS_ok _ q hq hnb hsv))
  rw [sSingle, hc]
  simp [Cnt.val]

theorem den_sRange (q0 : SEq) (ctor : ℕ → SEq) (hq0 : q0 = ctor 0)
    (hq : ∀ i < wordW V r.2, (ctor i).Active (dims (ownRam V r) (tau V r.2))) (hnb : ∀ i l, ctor i ≠ .borrow l)
    (hbit : ∀ w i, sBit w (ctor i) = i) (htag : ∀ w i, sTag w (ctor i) = sTag 1 q0)
    (htm : ∀ i, tmplS (ctor i) = tmplS q0) :
    den G s (sRange q0) = ((List.range (wordW V r.2)).map ctor).flatMap (fun q => itemNums mk (sItem V r q)) := by
  have hc := den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial ⟨.w, .idx, itemS (sTag 1 q0) (tmplS q0)⟩
    (fun i => itemNums mk (sItem V r (ctor i))) (by
      intro i hi s' hb' _ hj
      have hiw : i < wordW V r.2 := by rw [← dims_w V r]; exact hi
      have hj' : s'.env vJ = sBit (wordW V r.2) (ctor i) := by rw [hj, hbit]; rfl
      have hsv := sortV_of V r hR hb' _ hj' (by rw [hbit]; exact hiw)
      rw [← htm i]
      exact den_itemS_gen V mk hm0 hm1 r hR hb' (ctor i) (hq i hiw) _ (htag _ _) hj' _
        (by rw [← dims_w V r]; exact tmplS_ok _ _ (hq i hiw) (hnb i) hsv))
  rw [sRange, hc, List.flatMap_map]
  simp only [Cnt.val, dims_w]

theorem den_sSeg (seg : ℕ) (hseg : seg ≤ 2) (c : Cnt)
    (hc : c.val (dims (ownRam V r) (tau V r.2)) ≤ wordW V r.2)
    (hk : ∀ i, i < c.val (dims (ownRam V r) (tau V r.2)) → seg * wordW V r.2 + i < wordW V r.2 + tau V r.2 + 2) :
    den G s (sSeg seg c) = ((List.range (c.val (dims (ownRam V r) (tau V r.2)))).map
      (fun i => SEq.borrow (seg * wordW V r.2 + i))).flatMap (fun q => itemNums mk (sItem V r q)) := by
  have hτ := tau_lt_wordW_all V r.2
  have hw1 : 1 ≤ wordW V r.2 := by omega
  have hd := den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial ⟨c, .idx, itemS (2 + seg) (tmplS (.borrow seg))⟩
    (fun i => itemNums mk (sItem V r (.borrow (seg * wordW V r.2 + i)))) (by
      intro i hi s' hb' _ hj
      have hi2 : i < c.val (dims (ownRam V r) (tau V r.2)) := hi
      have hj2 : s'.env vJ = i := hj
      have hiw : i < wordW V r.2 := by omega
      have hdm := divmod_eq (x := seg * wordW V r.2 + i) (w := wordW V r.2) (qq := seg) (r := i) (by omega) rfl hiw
      have hj' : s'.env vJ = sBit (wordW V r.2) (.borrow (seg * wordW V r.2 + i)) := by
        rw [hj2]; simp only [sBit, hdm.2]
      have hsv := sortV_of V r hR hb' i hj2 hiw
      have hact : (SEq.borrow (seg * wordW V r.2 + i)).Active (dims (ownRam V r) (tau V r.2)) := by
        show seg * wordW V r.2 + i < (dims (ownRam V r) (tau V r.2)).κ
        rw [show (dims (ownRam V r) (tau V r.2)).κ = (dims (ownRam V r) (tau V r.2)).w + (dims (ownRam V r) (tau V r.2)).τ + 2
          from rfl, dims_w, dims_tau]
        exact hk i hi2
      have htag : sTag (wordW V r.2) (.borrow (seg * wordW V r.2 + i)) = 2 + seg := by
        simp only [sTag, hdm.1]
      have hx := tmplS_borrow_ok (dims (ownRam V r) (tau V r.2)) seg i hseg hsv
      rw [dims_w] at hx
      exact den_itemS_gen V mk hm0 hm1 r hR hb' _ hact _ htag hj' _ hx)
  rw [sSeg, hd, List.flatMap_map]

/-- **The SORT block prints the sorted items of `machineItems`.** -/
theorem den_sBlock :
    den G s (sBlockP) = (sortEqList (dims (ownRam V r) (tau V r.2))).flatMap (fun q => itemNums mk (sItem V r q)) := by
  have hτ := tau_lt_wordW_all V r.2
  have hw1 : 1 ≤ wordW V r.2 := by omega
  have hdw := dims_w V r
  have hdt := dims_tau V r
  rw [sortEqList_seg _ (by rw [hdw]; omega) (by rw [hdw, hdt]; omega)]
  simp only [sBlockP, den_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
    List.singleton_append, List.cons_append, List.nil_append]
  rw [den_sSingle V mk hm0 hm1 r hR hb .act trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .both trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSeg V mk hm0 hm1 r hR hb 0 (by norm_num) .w (by simp only [Cnt.val, hdw]; omega)
      (fun i hi => by simp only [Cnt.val, hdw] at hi; omega),
    den_sSeg V mk hm0 hm1 r hR hb 1 (by norm_num) .seg1 (by simp only [Cnt.val, hdw, hdt]; omega)
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi; omega),
    den_sSeg V mk hm0 hm1 r hR hb 2 (by norm_num) .seg2 (by simp only [Cnt.val, hdw, hdt]; omega)
      (fun i hi => by simp only [Cnt.val, hdw, hdt] at hi; omega),
    den_sSingle V mk hm0 hm1 r hR hb .strict trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .soFirst trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sRange V mk hm0 hm1 r hR hb (.soNext 0) SEq.soNext rfl (fun i hi => by show i < (dims (ownRam V r) (tau V r.2)).w; omega) (by simp)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .u trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .g trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sRange V mk hm0 hm1 r hR hb (.ev 0) SEq.ev rfl (fun i hi => by show i < (dims (ownRam V r) (tau V r.2)).w; omega) (by simp)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl),
    den_sRange V mk hm0 hm1 r hR hb (.load 0) SEq.load rfl (fun i hi => by show i < (dims (ownRam V r) (tau V r.2)).w; omega) (by simp)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .gA1 trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .gA trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .same trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sSingle V mk hm0 hm1 r hR hb .phase trivial (by simp) (fun _ => rfl) (fun _ => rfl),
    den_sRange V mk hm0 hm1 r hR hb (.value 0) SEq.value rfl (fun i hi => by show i < (dims (ownRam V r) (tau V r.2)).w; omega) (by simp)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  simp only [hdw, Cnt.val, hdt, List.append_assoc]

end Den

/-! ## Variables read and depths of the SORT block -/

theorem complS_all {x : SX} (h : x.All (Good itemA)) : (complS x).All (Good itemA) := ⟨trivial, h⟩

theorem good_E (e : E) (hr : RdE itemA e) (hd : dE e ≤ 3) : Good itemA e := ⟨hr, hd⟩

theorem all_keyS (fS : RecField → E → SX) (hf : ∀ f b, Good itemA b → (fS f b).All (Good itemA)) (lE : E)
    (hl : Good itemA lE) (hl1 : dE lE ≤ 1) : (keyS fS lE).All (Good itemA) := by
  refine ⟨⟨⟨hl.1, itemA_27⟩, by simp only [dE]; omega⟩, hf _ _ hl, ⟨⟨hl.1, itemA_27⟩, by simp only [dE]; omega⟩,
    hf _ _ good_k0, ⟨⟨hl.1, ⟨⟨itemA_27, trivial⟩, itemA_26⟩⟩, by simp only [dE]; omega⟩,
    hf _ _ ⟨⟨⟨hl.1, itemA_27⟩, trivial⟩, by simp only [dE]; omega⟩, hf _ _ good_k0⟩

theorem all_tmplS (q : SEq) : (tmplS q).All (Good itemA) := by
  have hseg : ∀ seg, Good itemA (segE seg) ∧ dE (segE seg) ≤ 1 := fun seg =>
    ⟨⟨⟨⟨trivial, itemA_26⟩, itemA_J⟩, by simp [segE, jE, dE]⟩, by simp [segE, jE, dE]⟩
  have hr : ∀ f b, Good itemA b → (rS f b).All (Good itemA) := fun _ _ h => h
  have hp : ∀ f b, Good itemA b → (prevS f b).All (Good itemA) := fun _ _ h => h
  have hob : ∀ seg, (obS seg).All (Good itemA) := by
    intro seg; unfold obS; split_ifs
    · exact ⟨good_j0E, trivial, good_jm1E⟩
    · exact ⟨good_j0E, good_wm1E, good_jm1E⟩
  have hj1 : Good itemA (.add jE (.k 1)) := ⟨⟨itemA_J, trivial⟩, by simp [jE, dE]⟩
  have h271 : Good itemA (.add (.v 27) (.k 1)) := ⟨⟨itemA_27, trivial⟩, by simp [dE]⟩
  cases q
  case borrow seg =>
    exact ⟨good_jE, ⟨complS_all (all_keyS prevS hp _ (hseg seg).1 (hseg seg).2) , all_keyS rS hr _ (hseg seg).1
      (hseg seg).2, hob seg⟩, all_keyS rS hr _ (hseg seg).1 (hseg seg).2, hob seg⟩
  all_goals simp only [tmplS, SX.All, sF, prevS, rS, complS, soNextS, obKappaS, good_jE, good_k0, hj1, h271,
    true_and, and_true, and_self]
  case strict => exact ⟨⟨h271.1, itemA_26⟩, by simp [dE]⟩
  case soNext => exact ⟨⟨hj1.1, itemA_26⟩, by simp [jE, dE]⟩

theorem dE_finE : dE finE ≤ 3 := by simp [finE, dE]

theorem WF_itemS (tag : ℕ) (x : SX) (hx : x.All (Good itemA)) : WF itemA (itemS tag x) := by
  have hh : SC.Rd itemA ⟨tag, jE, 2, 1⟩ := itemA_J
  exact WF_itemP (itemA_base (Or.inl ⟨by decide, by decide⟩)) not_itemA_vA _ _ _
    (rd_knE (layA_itemA _ (by simp [layA])) _ trivial)
    (rd_vaE layA_itemA _ hh _ _ trivial ⟨⟨trivial, itemA_base (Or.inl ⟨by decide, by decide⟩)⟩, trivial⟩)
    (WF_tokP layA_itemA _ hh _ hx.rd)

theorem Ok_itemS {d : ℕ} (hd : d + 1 < 8) (tag : ℕ) (x : SX) (hx : x.All (Good itemA)) : Ok d (itemS tag x) := by
  have hh : SC.Dp ⟨tag, jE, 2, 1⟩ := show dE jE ≤ 3 by simp [jE, dE]
  exact Ok_itemP hd _ _ _ (by simp [knE, k0, dE]) (dE_vaE _ _ _ hh (by simp [k0, dE]) dE_finE)
    (Ok_tokP (by omega) _ hh _ hx.dp)

theorem WF_pcS (c : Cnt) (jk : JK) (tag : ℕ) (x : SX) (hx : x.All (Good itemA)) :
    WF baseA (Pc.prog ⟨c, jk, itemS tag x⟩) :=
  WF_loopBind _ _ _ (rd_cnt c) (rd_jk jk) (WF_itemS tag x hx)

theorem Ok_pcS (c : Cnt) (jk : JK) (tag : ℕ) (x : SX) (hx : x.All (Good itemA)) :
    Ok 0 (Pc.prog ⟨c, jk, itemS tag x⟩) :=
  Ok_loopBind _ _ _ (dE_cnt c) (dE_jk jk) (Ok_itemS (by norm_num) tag x hx)

theorem WF_sBlock : WF baseA sBlockP := by
  apply WF_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact WF_pcS _ _ _ _ (all_tmplS _)

theorem Ok_sBlock : Ok 0 sBlockP := by
  apply Ok_seqL
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Ok_pcS _ _ _ _ (all_tmplS _)

end NearCubicGates.Adapters.RAMACSP.Gen.Items
