import SourceAdapters.RAMACSP.GenItemsSBool

/-!
# The copy and boundary blocks (B1)–(B4) of the item stream

Paper: (B1)–(B4) of `def:event-trace`, placed as in `app:affine-embedding`.
At role five, the first time lane checks zero and other time lanes copy the
previous lane through `Γ_t+η_5+η_1`. At role seven, earlier time lanes forbid
Out and the last checks Acc. At role six, the first sorted lane checks the
sentinel and other lanes copy the preceding record through `Γ_t+z+η_6`.
FIRST, PREV, EARLY_TIME and LAST_TIME select these cases.

Each copied slot prints its lane-`0` item, then one item per lane-carry index `t` (program variable `vT`).
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

/-! ## Lane masks -/

/-- `2^e`. -/
def pow1E (e : E) : E := .shl (.k 1) e

/-- `2^k − 1` (the lane bits of the first lane, FIRST). -/
def fkE : E := .sub (pow1E (.v 31)) (.k 1)

/-- `2^(t+1) − 1` (`t` in `vT`; the lane carry `Γ_t`). -/
def lcE : E := .sub (pow1E (.add (.v vT) (.k 1))) (.k 1)

/-- The read token argument of a lane-carry source: `(Γ_t ⊕ mask) + 1` (`mask` in `v`). -/
def predE (v : Var) : E := .add (.bxor lcE (.v v)) (.k 1)

/-- The read token from `h` to `c`. -/
def readTokP (h c : SC) : P := tokE 1 (.add (offE h c) (.k 1))

theorem eval_pow1 {s : FS} {e : E} {x : ℕ} (he : evalE G s e = x) (h : 2 ^ x ≤ G.cap) : evalE G s (pow1E e) = 2 ^ x := by
  simp only [pow1E, evalE, he, min_cap (show 1 ≤ G.cap by have := Nat.one_le_two_pow (n := x); omega), one_mul]
  exact min_cap h

theorem den_readTokP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) {l : Routing.Layout} {om dt : ℕ} {s : FS}
    (hl : LayV l om dt s) (hcap : 2 ^ l.m + 8 ≤ G.cap) (h c : SC) (hh : (h.ev G s).Ok om dt)
    (hc : (c.ev G s).Ok om dt) :
    den G s (readTokP h c) = [1, localOffset l om (h.ev G s) (c.ev G s) + 1] := by
  have ho := evalE_offE hl h c hh hc (by omega)
  have hlt := localOffset_lt l om dt hl.hq _ _ hh hc
  simp only [readTokP, den, tokE, evalE, ho, min_cap (show 1 ≤ G.cap by omega),
    min_cap (show localOffset l om (h.ev G s) (c.ev G s) + 1 ≤ G.cap by omega), List.singleton_append]

theorem eval_lcE {s : FS} (t : ℕ) (ht : s.env vT = t) (hc : 2 ^ (t + 1) ≤ G.cap) :
    evalE G s lcE = Routing.laneCarry t := by
  have h1 : evalE G s (.add (.v vT) (.k 1)) = t + 1 := by
    show min (s.env vT + min 1 G.cap) G.cap = _
    have : t + 1 ≤ G.cap := le_trans (Nat.lt_two_pow_self (n := t + 1)).le hc
    rw [ht, min_cap (show 1 ≤ G.cap by omega)]; exact min_cap this
  show evalE G s (pow1E _) - min 1 G.cap = _
  rw [eval_pow1 h1 hc, min_cap (by have := Nat.one_le_two_pow (n := t + 1); omega)]
  rfl

theorem eval_predE {s : FS} (v : Var) (t mask : ℕ) (ht : s.env vT = t) (hv : s.env v = mask) (n : ℕ)
    (hlc : 2 ^ (t + 1) ≤ 2 ^ n) (hm : mask < 2 ^ n) (hc : 2 ^ n + 1 ≤ G.cap) (hK : n ≤ G.K) :
    evalE G s (predE v) = (Routing.laneCarry t ^^^ mask) + 1 := by
  have hlct : Routing.laneCarry t < 2 ^ n := by
    unfold Routing.laneCarry; have := Nat.one_le_two_pow (n := t + 1); omega
  have hx : Routing.laneCarry t ^^^ mask < 2 ^ n := xor_lt_pow hlct hm
  have hKp : 2 ^ n ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) hK
  have e1 : evalE G s (.bxor lcE (.v v)) = Routing.laneCarry t ^^^ mask :=
    eE_bxor' (eval_lcE t ht (by omega)) hv (by omega)
  show min (evalE G s (.bxor lcE (.v v)) + min 1 G.cap) G.cap = _
  rw [e1, min_cap (show 1 ≤ G.cap by omega)]; exact min_cap (by omega)

theorem eta_lt (l : Routing.Layout) (r : ℕ) (hr : r < 8) : Routing.eta l r < 2 ^ l.m := by
  unfold Routing.eta
  exact cellMask_lt l 0 0 0 r 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) hr (by norm_num)

theorem areaMask_lt (l : Routing.Layout) : Routing.areaMask l < 2 ^ l.m := by
  unfold Routing.areaMask
  exact cellMask_lt l 0 0 0 0 1 (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) (by norm_num) (by norm_num)

/-! ## (B1)/(B2): the time copies -/

/-- The copy group of the slot with tag `tag`, bit `j` (in `vJ`), role, area: the lane-`0` item, then one item per
`t < τ`. -/
def copyP (tag role area : ℕ) : P :=
  .seq (itemP (knE fkE) (vaE ⟨tag, jE, 5, 1⟩ k0 k0) (readTokP ⟨tag, jE, 5, 1⟩ ⟨tag, jE, role, area⟩))
    (.loop vT (.v 27) (itemP (knE (.add lcE (.v 28))) (vaE ⟨tag, jE, 5, 1⟩ (pow1E (.v vT)) k0)
      (.seq (readTokP ⟨tag, jE, 5, 1⟩ ⟨tag, jE, role, area⟩) (.seq (tokE 1 (predE vP5)) (tokE 2 k0)))))

/-- The items of the copy group of the destination cell `dc` in `machineItems` (layout `l`, `ω`, `τ`). -/
def copyItems {F : Type} [Field F] [CharP F 2] (l : Routing.Layout) (om τ : ℕ) (dc : Cell) :
    List (Routing.Pattern l.m × Routing.Expr F) :=
  (guardAt l om (2 ^ l.k - 1) 0 0 ⟨dc.tag, dc.bit, 5, 1⟩, .read (some (localOffset l om ⟨dc.tag, dc.bit, 5, 1⟩ dc))) ::
    (List.range τ).map fun t =>
      (guardAt l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0 ⟨dc.tag, dc.bit, 5, 1⟩,
        .add (.read (some (localOffset l om ⟨dc.tag, dc.bit, 5, 1⟩ dc)))
          (.read (some (Routing.laneCarry t ^^^ Routing.eta l 5 ^^^ Routing.eta l 1))))

theorem notA_layA (x : Var) (hx : layA x) : notA x := by
  unfold notA; rcases hx with h | h | h | h | h | h | h <;> (subst h; decide)

theorem rd_vaE_notA (h : SC) (hh : RdE notA h.bit) (lv st : E) (hlv : RdE notA lv) (hst : RdE notA st) :
    RdE notA (vaE h lv st) := rd_vaE notA_layA h hh lv st hlv hst

/-- The state facts of a lane-carry group: layout, `τ` (27), `2^τ` (28), `k = τ + 1` (31), the source mask in `vM`,
room. -/
structure LaneV (l : Routing.Layout) (om dt τ : ℕ) (vM : Var) (mask : ℕ) (s : FS) : Prop where
  lay : LayV l om dt s
  ht : s.env 27 = τ
  hT : s.env 28 = 2 ^ τ
  hk : s.env 31 = l.k
  hk1 : τ + 1 = l.k
  hkm : l.k < l.m
  hM : s.env vM = mask
  hmask : mask < 2 ^ l.m
  cap : 2 ^ l.m + 8 ≤ G.cap
  mN : l.m ≤ G.N
  mK : l.m ≤ G.K

theorem LaneV.setT {l : Routing.Layout} {om dt τ : ℕ} {vM : Var} {mask : ℕ} {s : FS}
    (h : LaneV (G := G) l om dt τ vM mask s) (hM : vM ≠ vT) (t : ℕ) : LaneV (G := G) l om dt τ vM mask (s.setv vT t) := by
  have ha : Agree layA s (s.setv vT t) := ⟨fun x hx => by
    have : x ≠ vT := by rcases hx with e | e | e | e | e | e | e <;> (subst e; decide)
    simp [Function.update_of_ne this], rfl, rfl⟩
  exact ⟨h.lay.agree (fun _ hx => hx) ha, by simp [h.ht, vT], by simp [h.hT, vT], by simp [h.hk, vT], h.hk1, h.hkm,
    by simp [Function.update_of_ne hM, h.hM], h.hmask, h.cap, h.mN, h.mK⟩

/-- **One copy group.** -/
theorem den_copyP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) {l : Routing.Layout} {om dt τ : ℕ} {s : FS}
    (hs : LaneV (G := G) l om dt τ vP5 (Routing.eta l 5 ^^^ Routing.eta l 1) s) (tag role area j : ℕ)
    (hj : s.env vJ = j) (hc : (⟨tag, j, role, area⟩ : Cell).Ok om dt) :
    den G s (copyP tag role area) = (copyItems l om τ (⟨tag, j, role, area⟩ : Cell) : List (_ × Routing.Expr F)).flatMap
      (itemNums mk) := by
  have hcap := hs.cap
  have hpm := Nat.two_pow_pos l.m
  have hh : (⟨tag, j, 5, 1⟩ : Cell).Ok om dt := ⟨hc.1, hc.2.1, by norm_num, by norm_num⟩
  have ehh : ∀ t : FS, t.env vJ = j → SC.ev G t ⟨tag, jE, 5, 1⟩ = ⟨tag, j, 5, 1⟩ := fun t ht => by
    simp [SC.ev, jE, evalE, ht]
  have ehc : ∀ t : FS, t.env vJ = j → SC.ev G t ⟨tag, jE, role, area⟩ = ⟨tag, j, role, area⟩ := fun t ht => by
    simp [SC.ev, jE, evalE, ht]
  have hp2 : ∀ x, x ≤ l.m → 2 ^ x ≤ G.cap := fun x hx => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hx; omega
  have hkm := hs.hkm
  have hfk : evalE G s fkE = 2 ^ l.k - 1 := by
    show evalE G s (pow1E (.v 31)) - min 1 G.cap = _
    rw [eval_pow1 (show evalE G s (.v 31) = l.k from hs.hk) (hp2 _ hkm.le), min_cap (show 1 ≤ G.cap by omega)]
  have rdh : RdE notA (vaE ⟨tag, jE, 5, 1⟩ k0 k0) :=
    rd_vaE_notA ⟨tag, jE, 5, 1⟩ (show vJ ≠ vA by decide) _ _ trivial trivial
  simp only [copyP, den, copyItems, List.flatMap_cons]
  congr 1
  · rw [den_itemGen mk hs.lay (by omega) hs.mN ⟨tag, jE, 5, 1⟩ _
      (.read (some (localOffset l om ⟨tag, j, 5, 1⟩ ⟨tag, j, role, area⟩)))
      fkE k0 k0 (2 ^ l.k - 1) 0 0 hfk (Nat.zero_min _) (Nat.zero_min _) (by have := Nat.one_le_two_pow (n := l.k); omega)
      (Nat.two_pow_pos _) (Nat.two_pow_pos _) (by rw [ehh s hj]; exact hh)
      (rd_knE (show vUK ≠ vA by decide) _ ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩) rdh
      (by rw [den_readTokP mk hs.lay (by omega) _ _ (by rw [ehh s hj]; exact hh) (by rw [ehc s hj]; exact hc), ehh s hj,
        ehc s hj]; simp [Joins.exprToks, tokNums, Joins.varCode]), ehh s hj]
  · have hmin : min (evalE G s (.v 27)) G.N = τ := by
      show min (s.env 27) G.N = _; rw [hs.ht]; have := hs.mN; have := hs.hk1; omega
    rw [hmin, List.flatMap_map]
    apply List.flatMap_congr
    intro t ht
    replace ht := List.mem_range.mp ht
    have hs' := hs.setT (by decide) t
    have hk1 := hs.hk1
    have hj' : (s.setv vT t).env vJ = j := by
      rw [FS.setv_env, Function.update_of_ne (show vJ ≠ vT by decide)]; exact hj
    have hT' : (s.setv vT t).env vT = t := by simp
    have hlc := eval_lcE (G := G) (s := s.setv vT t) t hT' (hp2 _ (by omega))
    have hk2 : 2 ^ (t + 1) - 1 + 2 ^ τ < 2 ^ l.k := by
      have e : 2 ^ l.k = 2 * 2 ^ τ := by rw [← hs.hk1, pow_succ]; ring
      have : 2 ^ (t + 1) ≤ 2 ^ τ := Nat.pow_le_pow_right (by norm_num) ht
      have := Nat.one_le_two_pow (n := t + 1)
      omega
    have hlk : evalE G (s.setv vT t) (.add lcE (.v 28)) = 2 ^ (t + 1) - 1 + 2 ^ τ := by
      show min (evalE G (s.setv vT t) lcE + (s.setv vT t).env 28) G.cap = _
      have := hp2 l.k hkm.le
      rw [hlc, hs'.hT, min_cap (by unfold Routing.laneCarry; omega)]
      rfl
    have hlv : evalE G (s.setv vT t) (pow1E (.v vT)) = 2 ^ t := eval_pow1 hT' (hp2 _ (by omega))
    have hpred := eval_predE (G := G) (s := s.setv vT t) vP5 t _ hT' hs'.hM l.m
      (Nat.pow_le_pow_right (by norm_num) (by omega)) hs.hmask (by omega) hs.mK
    have hoff := den_readTokP mk hs'.lay (by omega) ⟨tag, jE, 5, 1⟩ ⟨tag, jE, role, area⟩
      (by rw [ehh _ hj']; exact hh) (by rw [ehc _ hj']; exact hc)
    rw [den_itemGen mk hs'.lay (by omega) hs.mN ⟨tag, jE, 5, 1⟩ _
      (.add (.read (some (localOffset l om ⟨tag, j, 5, 1⟩ ⟨tag, j, role, area⟩)))
        (.read (some (Routing.laneCarry t ^^^ Routing.eta l 5 ^^^ Routing.eta l 1))))
      _ _ k0 _ _ 0 hlk hlv (Nat.zero_min _) hk2 (Nat.pow_lt_pow_right (by norm_num) (by omega)) (Nat.two_pow_pos _)
      (by rw [ehh _ hj']; exact hh)
      (rd_knE (show vUK ≠ vA by decide) _ ⟨⟨⟨trivial, ⟨show vT ≠ vA by decide, trivial⟩⟩, trivial⟩,
        show (28 : Var) ≠ vA by decide⟩)
      (rd_vaE_notA ⟨tag, jE, 5, 1⟩ (show vJ ≠ vA by decide) _ _ ⟨trivial, show vT ≠ vA by decide⟩ trivial), ehh _ hj']
    simp only [den, tokE, hoff, hpred, ehh _ hj', ehc _ hj', evalE, k0, Nat.zero_min,
      min_cap (show 1 ≤ G.cap by omega), min_cap (show 2 ≤ G.cap by omega)]
    simp [Joins.exprToks, tokNums, Joins.varCode, Nat.xor_assoc]

variable (V : Verifier)

theorem room_basic (r : ClockRequest) (hR : Room V r G) :
    2 ^ (ownLayout V r.2).m + 8 ≤ G.cap ∧ (ownLayout V r.2).m ≤ G.N ∧ (ownLayout V r.2).m ≤ G.K ∧
      tau V r.2 + 1 = (ownLayout V r.2).k ∧ (ownLayout V r.2).k < (ownLayout V r.2).m := by
  obtain ⟨h1, h2⟩ := layout_room V r hR
  refine ⟨h1, h2, ?_, rfl, ?_⟩
  · rw [ownLayout_m]; have := hR.mK; omega
  · show laneExp V r.2 < (ownLayout V r.2).m; rw [ownLayout_m]; unfold domExp; omega

theorem laneV_of (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (vM : Var) (mask : ℕ)
    (hM : s.env vM = mask) (hmask : mask < 2 ^ (ownLayout V r.2).m) :
    LaneV (G := G) (ownLayout V r.2) (wordExp V r.2) (tagExp V) (tau V r.2) vM mask s := by
  obtain ⟨hcap, hmN, hmK, hk1, hkm⟩ := room_basic V r hR
  exact ⟨hb.lay, hb.pv.ta, hb.pv.T, hb.pv.k, hk1, hkm, hM, hmask, hcap, hmN, hmK⟩

theorem dstCell_ok_gen (W K L τ β om dt : ℕ) (hw : W = 2 ^ om) (hτ : τ < W) (hβ : β ≤ τ)
    (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt) (cp : TCopy) (hv : cp.Active ⟨W, K, L, τ, β⟩) :
    (dstCell K L cp).Ok om dt :=
  dstCell_ok ⟨W, K, L, τ, β⟩ K L om dt rfl rfl hw hτ hβ hF cp hv

/-! ## The block of the time copies -/

/-- A piece of the time copies. -/
structure CPc where
  c : Cnt
  jk : JK
  cp : ℕ → TCopy
  hcell : ∀ K L i, dstCell K L (cp i) =
    ⟨(dstCell K L (cp 0)).tag, jk.val i, (dstCell K L (cp 0)).role, (dstCell K L (cp 0)).area⟩

/-- Its printer. -/
def CPc.prog (pc : CPc) : P :=
  Pc.prog ⟨pc.c, pc.jk, copyP (dstCell (regCount V) (codeLen V) (pc.cp 0)).tag
    (dstCell (regCount V) (codeLen V) (pc.cp 0)).role (dstCell (regCount V) (codeLen V) (pc.cp 0)).area⟩

/-- **The pieces of the time copies.** -/
def cpPieces (K : ℕ) : List CPc :=
  [⟨.w, .idx, TCopy.pc, fun _ _ _ => rfl⟩] ++ (List.range K).map (fun r => ⟨.one, .zero, fun _ => TCopy.fl r,
    fun _ _ _ => rfl⟩) ++ (List.range K).map (fun r => ⟨.w, .idx, TCopy.rg r, fun _ _ _ => rfl⟩) ++
  [⟨.tau, .idx, TCopy.ts, fun _ _ _ => rfl⟩, ⟨.tau, .idx, TCopy.cA, fun _ _ _ => rfl⟩,
   ⟨.beta1, .idx, TCopy.cB, fun _ _ _ => rfl⟩]

theorem copyList_pieces (d : Dims) :
    copyList d = (cpPieces d.K).flatMap (fun pc => (List.range (pc.c.val d)).map pc.cp) := by
  simp [copyList, cpPieces, List.flatMap_append, List.flatMap_map, Cnt.val, Function.comp_def,
    List.flatMap_singleton', range_one_map, flatMap_singleton_eq_map]

/-- **The printer of the time copies.** -/
def cpBlockP : P := seqL ((cpPieces (regCount V)).map (CPc.prog V))

theorem den_cpBlock {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (r : ClockRequest) (hR : Room V r G) {s : FS}
    (hb : Base V r s) :
    den G s (cpBlockP V) = (copyList (dims (ownRam V r) (tau V r.2))).flatMap (fun cp =>
      (copyItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (dstCell (regCount V) (codeLen V) cp) :
        List (_ × Routing.Expr F)).flatMap (itemNums mk)) := by
  have hK : (dims (ownRam V r) (tau V r.2)).K = regCount V := by rw [dims_own V r]
  rw [cpBlockP, den_seqL, List.flatMap_map, copyList_pieces, hK, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pc hpc
  rw [CPc.prog, den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial _
    (fun i => (copyItems (ownLayout V r.2) (wordExp V r.2) (tau V r.2) (dstCell (regCount V) (codeLen V) (pc.cp i)) :
      List (_ × Routing.Expr F)).flatMap (itemNums mk)), List.flatMap_map]
  intro i hi s' hb' _ hj
  have hmem : pc.cp i ∈ copyList (dims (ownRam V r) (tau V r.2)) := by
    rw [copyList_pieces, hK]
    exact List.mem_flatMap.mpr ⟨pc, hpc, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩
  have hact := mem_copyList _ _ hmem
  have hF := ftags_bound V
  have hτ := tau_lt_wordW_all V r.2
  rw [dims_own V r] at hact
  have hok := dstCell_ok_gen _ _ _ _ _ _ _ (wordW_eq V r.2) hτ (Nat.sub_le _ _) hF _ hact
  have hc := pc.hcell (regCount V) (codeLen V) i
  rw [hc] at hok ⊢
  have hm5 : Routing.eta (ownLayout V r.2) 5 ^^^ Routing.eta (ownLayout V r.2) 1 < 2 ^ (ownLayout V r.2).m :=
    xor_lt_pow (eta_lt _ 5 (by norm_num)) (eta_lt _ 1 (by norm_num))
  exact den_copyP mk (laneV_of V r hR hb' vP5 _ hb'.p5 hm5) _ _ _ _ hj hok

end NearCubicGates.Adapters.RAMACSP.Gen.Items
