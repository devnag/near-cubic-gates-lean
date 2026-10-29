import SourceAdapters.RAMACSP.GenItemsBound

/-!
# The halting block (B3) and the sorted copies (B4)

Paper: (B3) and (B4) of `def:event-trace`, and "Placement" in
`app:affine-embedding`. The time halt checks share role-seven tag-seven bit-zero:
EARLY_TIME selects `e(Out)=0`, and LAST_TIME selects `e(Acc)+1=0`.
Sorted copies use role six and record tags zero through five: FIRST selects
the sentinel (active one, all other bits zero), and PREV selects the
preceding record through `Γ_t+z+η_6`.-/

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

/-! ## (B3) -/

/-- The host of (B3): stage `0`, role `7`, tag `7`, bit `0`. -/
def h3 : SC := ⟨7, k0, 7, 1⟩

/-- **The printer of (B3).** -/
def b3P : P :=
  .seq (.loop vT (.v 27) (itemP (knE (.add (.v 28) lcE)) (vaE h3 (.sub (pow1E (.v vT)) (.k 1)) k0)
      (tokP h3 (eSetS V (regCount V) (codeLen V) isOut))))
    (itemP (knE fkE) (vaE h3 (.sub (.v 28) (.k 1)) k0)
      (tokP h3 (.add (eSetS V (regCount V) (codeLen V) isAcc) .one)))

/-- The (B3) items of `machineItems`. -/
def b3Items {F : Type} [Field F] [CharP F 2] (r : ClockRequest) :
    List (Routing.Pattern (ownLayout V r.2).m × Routing.Expr F) :=
  let l := ownLayout V r.2
  let om := wordExp V r.2
  let τ := tau V r.2
  let h : Cell := ⟨7, 0, 7, 1⟩
  ((List.range τ).map fun b =>
    (guardAt l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 h,
      toRouting (tRead l om (regCount V) (codeLen V) h) (outE (ownRam V r)))) ++
  [(guardAt l om (2 ^ l.k - 1) (2 ^ τ - 1) 0 h, toRouting (tRead l om (regCount V) (codeLen V) h) (accE (ownRam V r)))]

theorem tRead_comp (l : Routing.Layout) (om K L : ℕ) (h : Cell) :
    tRead l om K L h = localOffset l om h ∘ cellT K L := funext (tRead_eq' l om K L h)

theorem h3_ev (s : FS) : SC.ev G s h3 = ⟨7, 0, 7, 1⟩ := by simp [h3, SC.ev, k0, evalE]

theorem h3_ok (r : ClockRequest) : (⟨7, 0, 7, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) := by
  have hF := ftags_bound V
  exact ⟨Nat.two_pow_pos _, show 7 < 2 ^ tagExp V by omega, by norm_num, by norm_num⟩

theorem den_b3 {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) :
    den G s (b3P V) = (b3Items V r : List (_ × Routing.Expr F)).flatMap (itemNums mk) := by
  obtain ⟨hcap, hmN, hmK, hk1, hkm⟩ := room_basic V r hR
  have hpm := Nat.two_pow_pos (ownLayout V r.2).m
  have hp2 : ∀ x, x ≤ (ownLayout V r.2).m → 2 ^ x ≤ G.cap := fun x hx => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hx; omega
  have hw1 : 1 ≤ (ownRam V r).w := by show 1 ≤ wordW V r.2; rw [wordW_eq]; exact Nat.one_le_two_pow
  have hOut := ev_eSetS V (codeLen_le_two_pow_wordW V r.2) (n := r.1.1) (t := r.2)
    (T := 2 ^ timeExp (clockConst V) r.2) (regCount V) (codeLen V) (G := G) s isOut isOut
    (fun d => isOut_realize V _ d)
  have hAcc : SX.ev G s (eSetS V (regCount V) (codeLen V) isAcc) =
      xmap (cellT (regCount V) (codeLen V)) (eSet (ownRam V r) isAcc) :=
    ev_eSetS V (codeLen_le_two_pow_wordW V r.2) (n := r.1.1) (t := r.2)
      (T := 2 ^ timeExp (clockConst V) r.2) (regCount V) (codeLen V) (G := G) s isAcc isAcc
      (fun d => isAcc_realize V _ d)
  have hτT : 2 ^ tau V r.2 < 2 ^ (ownLayout V r.2).k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [b3P, den, b3Items, List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · have hmin : min (evalE G s (.v 27)) G.N = tau V r.2 := by
      show min (s.env 27) G.N = _; rw [hb.pv.ta]; omega
    rw [hmin]
    apply List.flatMap_congr
    intro b hbm
    replace hbm := List.mem_range.mp hbm
    have hb' : Base V r (s.setv vT b) := hb.setv V vT (by unfold baseA vT vKL vUK vP5 vP6 vD; decide) b
    have hT' : (s.setv vT b).env vT = b := by simp
    have hOut' : SX.ev G (s.setv vT b) (eSetS V (regCount V) (codeLen V) isOut) =
        xmap (cellT (regCount V) (codeLen V)) (outE (ownRam V r)) :=
      ev_eSetS V (codeLen_le_two_pow_wordW V r.2) (n := r.1.1) (t := r.2)
        (T := 2 ^ timeExp (clockConst V) r.2) (regCount V) (codeLen V) (G := G) (s.setv vT b) isOut isOut
        (fun d => isOut_realize V _ d)
    have hlc := eval_lcE (G := G) (s := s.setv vT b) b hT' (hp2 _ (by omega))
    have hlk : evalE G (s.setv vT b) (.add (.v 28) lcE) = 2 ^ tau V r.2 + (2 ^ (b + 1) - 1) := by
      show min ((s.setv vT b).env 28 + evalE G (s.setv vT b) lcE) G.cap = _
      have := hp2 _ hkm.le
      have : 2 ^ (b + 1) ≤ 2 ^ tau V r.2 := Nat.pow_le_pow_right (by norm_num) hbm
      have e : 2 ^ (ownLayout V r.2).k = 2 * 2 ^ tau V r.2 := by rw [← hk1, pow_succ]; ring
      rw [hlc, hb'.pv.T, min_cap (by unfold Routing.laneCarry; omega)]
      rfl
    have hlv : evalE G (s.setv vT b) (.sub (pow1E (.v vT)) (.k 1)) = 2 ^ b - 1 := by
      show evalE G (s.setv vT b) (pow1E (.v vT)) - min 1 G.cap = _
      rw [eval_pow1 (show evalE G (s.setv vT b) (.v vT) = b from hT') (hp2 _ (by omega)),
        min_cap (show 1 ≤ G.cap by omega)]
    have hvars : ∀ c ∈ (SX.ev G (s.setv vT b) (eSetS V (regCount V) (codeLen V) isOut)).vars,
        c.Ok (wordExp V r.2) (tagExp V) := by
      rw [hOut', vars_xmap]
      intro c hc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
      exact cellT_ok V r v (outE_reads _ _ v hv)
    rw [den_item mk hm0 hm1 hb'.lay hcap hmN h3 _ _ _ k0 _ _ 0 hlk hlv (Nat.zero_min _)
      (by have : 2 ^ (b + 1) ≤ 2 ^ tau V r.2 := Nat.pow_le_pow_right (by norm_num) hbm
          have e : 2 ^ (ownLayout V r.2).k = 2 * 2 ^ tau V r.2 := by rw [← hk1, pow_succ]; ring
          omega)
      (by have : 2 ^ b < 2 ^ (ownLayout V r.2).k := Nat.pow_lt_pow_right (by norm_num) (by omega); omega)
      (Nat.two_pow_pos _) (by rw [h3_ev]; exact h3_ok V r) hvars
      (rd_knE (show vUK ≠ vA by decide) _ ⟨show (28 : Var) ≠ vA by decide,
        ⟨⟨trivial, ⟨show vT ≠ vA by decide, trivial⟩⟩, trivial⟩⟩)
      (rd_vaE_notA h3 trivial _ _ ⟨⟨trivial, show vT ≠ vA by decide⟩, trivial⟩ trivial),
      h3_ev, hOut', tRead_comp, toRouting_xmap]
  · have hfk : evalE G s fkE = 2 ^ (ownLayout V r.2).k - 1 := by
      show evalE G s (pow1E (.v 31)) - min 1 G.cap = _
      rw [eval_pow1 (show evalE G s (.v 31) = (ownLayout V r.2).k from hb.pv.k) (hp2 _ hkm.le),
        min_cap (show 1 ≤ G.cap by omega)]
    have hlv : evalE G s (.sub (.v 28) (.k 1)) = 2 ^ tau V r.2 - 1 := by
      show s.env 28 - min 1 G.cap = _
      rw [hb.pv.T, min_cap (show 1 ≤ G.cap by omega)]
    have hev : SX.ev G s (.add (eSetS V (regCount V) (codeLen V) isAcc) .one) =
        xmap (cellT (regCount V) (codeLen V)) (accE (ownRam V r)) := by
      simp only [SX.ev, hAcc, accE, xmap]
    have hvars : ∀ c ∈ (SX.ev G s (.add (eSetS V (regCount V) (codeLen V) isAcc) .one)).vars,
        c.Ok (wordExp V r.2) (tagExp V) := by
      rw [hev, vars_xmap]
      intro c hc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
      exact cellT_ok V r v (accE_reads _ _ v hv)
    rw [den_item mk hm0 hm1 hb.lay hcap hmN h3 _ _ _ k0 _ _ 0 hfk hlv (Nat.zero_min _)
      (by have := Nat.one_le_two_pow (n := (ownLayout V r.2).k); omega)
      (show 2 ^ tau V r.2 - 1 < 2 ^ (ownLayout V r.2).k by have := hτT; have := Nat.two_pow_pos (tau V r.2); omega)
      (Nat.two_pow_pos _) (by rw [h3_ev]; exact h3_ok V r) hvars
      (rd_knE (show vUK ≠ vA by decide) _ ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩)
      (rd_vaE_notA h3 trivial _ _ ⟨show (28 : Var) ≠ vA by decide, trivial⟩ trivial), h3_ev, hev, tRead_comp,
      toRouting_xmap]

/-! ## (B4) -/

/-- The sorted copy group of the predecessor slot with tag `tag`, bit `j` (in `vJ`): the sentinel item (constant
`cst`), then one item per `t < k`. -/
def sCopyP (tag cst : ℕ) : P :=
  .seq (itemP (knE fkE) (vaE ⟨tag, jE, 6, 1⟩ k0 finE)
      (.seq (readTokP ⟨tag, jE, 6, 1⟩ ⟨tag, jE, 1, 1⟩) (.seq (tokE 0 (.k cst)) (tokE 2 k0))))
    (.loop vT (.v 31) (itemP (knE lcE) (vaE ⟨tag, jE, 6, 1⟩ (pow1E (.v vT)) finE)
      (.seq (readTokP ⟨tag, jE, 6, 1⟩ ⟨tag, jE, 1, 1⟩) (.seq (tokE 1 (predE vP6)) (tokE 2 k0)))))

/-- The items of the sorted copy group of the predecessor slot `(f, j)` (layout `l`, `ω`, final stage `fin`). -/
def sCopyItems {F : Type} [Field F] [CharP F 2] (l : Routing.Layout) (om fin : ℕ) (f : RecField) (j : ℕ) :
    List (Routing.Pattern l.m × Routing.Expr F) :=
  (guardAt l om (2 ^ l.k - 1) 0 fin ⟨f.tag, j, 6, 1⟩,
      .add (.read (some (localOffset l om ⟨f.tag, j, 6, 1⟩ ⟨f.tag, j, 1, 1⟩))) (.const (if f = .act then 1 else 0))) ::
    (List.range l.k).map fun t =>
      (guardAt l om (2 ^ (t + 1) - 1) (2 ^ t) fin ⟨f.tag, j, 6, 1⟩,
        .add (.read (some (localOffset l om ⟨f.tag, j, 6, 1⟩ ⟨f.tag, j, 1, 1⟩)))
          (.read (some (Routing.laneCarry t ^^^ Routing.areaMask l ^^^ Routing.eta l 6))))

/-- **One sorted copy group.** -/
theorem den_sCopyP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (f : RecField) (j : ℕ) (hj : s.env vJ = j)
    (hc : (⟨f.tag, j, 1, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V)) :
    den G s (sCopyP f.tag (if f = .act then 1 else 0)) =
      (sCopyItems (ownLayout V r.2) (wordExp V r.2) (2 * (ownLayout V r.2).k - 1) f j :
        List (_ × Routing.Expr F)).flatMap (itemNums mk) := by
  obtain ⟨hcap, hmN, hmK, hk1, hkm⟩ := room_basic V r hR
  have hpm := Nat.two_pow_pos (ownLayout V r.2).m
  have hp2 : ∀ x, x ≤ (ownLayout V r.2).m → 2 ^ x ≤ G.cap := fun x hx => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hx; omega
  have hh : (⟨f.tag, j, 6, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) := ⟨hc.1, hc.2.1, by norm_num, by norm_num⟩
  have ehh : ∀ t : FS, t.env vJ = j → SC.ev G t ⟨f.tag, jE, 6, 1⟩ = ⟨f.tag, j, 6, 1⟩ := fun t ht => by
    simp [SC.ev, jE, evalE, ht]
  have ehc : ∀ t : FS, t.env vJ = j → SC.ev G t ⟨f.tag, jE, 1, 1⟩ = ⟨f.tag, j, 1, 1⟩ := fun t ht => by
    simp [SC.ev, jE, evalE, ht]
  have hfin := fin_lt V r
  have hfk : evalE G s fkE = 2 ^ (ownLayout V r.2).k - 1 := by
    show evalE G s (pow1E (.v 31)) - min 1 G.cap = _
    rw [eval_pow1 (show evalE G s (.v 31) = (ownLayout V r.2).k from hb.pv.k) (hp2 _ hkm.le),
      min_cap (show 1 ≤ G.cap by omega)]
  have hfinE : evalE G s finE = 2 * (ownLayout V r.2).k - 1 := eval_finE V r hR hb
  have rfin : RdE notA finE := ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩
  have hcst : mk (if f = .act then (1 : F) else 0) = if f = .act then 1 else 0 := by
    split_ifs <;> assumption
  simp only [sCopyP, den, sCopyItems, List.flatMap_cons]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · have hoff := den_readTokP mk hb.lay (by omega) ⟨f.tag, jE, 6, 1⟩ ⟨f.tag, jE, 1, 1⟩ (by rw [ehh s hj]; exact hh)
      (by rw [ehc s hj]; exact hc)
    rw [den_itemGen mk hb.lay (by omega) hmN ⟨f.tag, jE, 6, 1⟩ _
      (.add (.read (some (localOffset (ownLayout V r.2) (wordExp V r.2) ⟨f.tag, j, 6, 1⟩ ⟨f.tag, j, 1, 1⟩)))
        (.const (if f = .act then 1 else 0)))
      fkE k0 finE _ 0 _ hfk (Nat.zero_min _) hfinE (by have := Nat.one_le_two_pow (n := (ownLayout V r.2).k); omega)
      (Nat.two_pow_pos _) hfin (by rw [ehh s hj]; exact hh)
      (rd_knE (show vUK ≠ vA by decide) _ ⟨⟨trivial, show (31 : Var) ≠ vA by decide⟩, trivial⟩)
      (rd_vaE_notA ⟨f.tag, jE, 6, 1⟩ (show vJ ≠ vA by decide) _ _ trivial rfin), ehh s hj]
    simp only [den, tokE, hoff, ehh s hj, ehc s hj, evalE, k0, Nat.zero_min, min_cap (show 1 ≤ G.cap by omega),
      min_cap (show 2 ≤ G.cap by omega), min_cap (show (if f = .act then 1 else 0) ≤ G.cap by split_ifs <;> omega)]
    simp [Joins.exprToks, tokNums, Joins.varCode, hcst]
  · have hmin : min (evalE G s (.v 31)) G.N = (ownLayout V r.2).k := by
      have e : (ownLayout V r.2).k = laneExp V r.2 := rfl
      show min (s.env 31) G.N = _; rw [hb.pv.k, e]; rw [e] at hkm; omega
    rw [hmin, List.flatMap_map]
    apply List.flatMap_congr
    intro t ht
    replace ht := List.mem_range.mp ht
    have hb' : Base V r (s.setv vT t) := hb.setv V vT (by unfold baseA vT vKL vUK vP5 vP6 vD; decide) t
    have hj' : (s.setv vT t).env vJ = j := by
      rw [FS.setv_env, Function.update_of_ne (show vJ ≠ vT by decide)]; exact hj
    have hT' : (s.setv vT t).env vT = t := by simp
    have hlc := eval_lcE (G := G) (s := s.setv vT t) t hT' (hp2 _ (by omega))
    have hlv : evalE G (s.setv vT t) (pow1E (.v vT)) = 2 ^ t := eval_pow1 (show evalE G (s.setv vT t) (.v vT) = t from hT')
      (hp2 _ (by omega))
    have hm6 : Routing.areaMask (ownLayout V r.2) ^^^ Routing.eta (ownLayout V r.2) 6 < 2 ^ (ownLayout V r.2).m :=
      xor_lt_pow (areaMask_lt _) (eta_lt _ 6 (by norm_num))
    have hpred := eval_predE (G := G) (s := s.setv vT t) vP6 t _ hT' hb'.p6 (ownLayout V r.2).m
      (Nat.pow_le_pow_right (by norm_num) (by omega)) hm6 (by omega) hmK
    have hoff := den_readTokP mk hb'.lay (by omega) ⟨f.tag, jE, 6, 1⟩ ⟨f.tag, jE, 1, 1⟩ (by rw [ehh _ hj']; exact hh)
      (by rw [ehc _ hj']; exact hc)
    have hlck : Routing.laneCarry t < 2 ^ (ownLayout V r.2).k := by
      unfold Routing.laneCarry
      have : 2 ^ (t + 1) ≤ 2 ^ (ownLayout V r.2).k := Nat.pow_le_pow_right (by norm_num) ht
      have := Nat.one_le_two_pow (n := t + 1)
      omega
    rw [den_itemGen mk hb'.lay (by omega) hmN ⟨f.tag, jE, 6, 1⟩ _
      (.add (.read (some (localOffset (ownLayout V r.2) (wordExp V r.2) ⟨f.tag, j, 6, 1⟩ ⟨f.tag, j, 1, 1⟩)))
        (.read (some (Routing.laneCarry t ^^^ Routing.areaMask (ownLayout V r.2) ^^^ Routing.eta (ownLayout V r.2) 6))))
      lcE (pow1E (.v vT)) finE (2 ^ (t + 1) - 1) (2 ^ t) (2 * (ownLayout V r.2).k - 1) hlc hlv
      (eval_finE V r hR hb') hlck (Nat.pow_lt_pow_right (by norm_num) ht) hfin
      (by rw [ehh _ hj']; exact hh)
      (rd_knE (show vUK ≠ vA by decide) _ ⟨⟨trivial, ⟨show vT ≠ vA by decide, trivial⟩⟩, trivial⟩)
      (rd_vaE_notA ⟨f.tag, jE, 6, 1⟩ (show vJ ≠ vA by decide) _ _ ⟨trivial, show vT ≠ vA by decide⟩ rfin), ehh _ hj']
    simp only [den, tokE, hoff, hpred, ehh _ hj', ehc _ hj', evalE, k0, Nat.zero_min,
      min_cap (show 1 ≤ G.cap by omega), min_cap (show 2 ≤ G.cap by omega)]
    simp [Joins.exprToks, tokNums, Joins.varCode, Nat.xor_assoc]

/-- **The printer of (B4).** -/
def b4P : P :=
  seqL [Pc.prog ⟨.w, .idx, sCopyP RecField.va.tag 0⟩, Pc.prog ⟨.w, .idx, sCopyP RecField.ad.tag 0⟩,
    Pc.prog ⟨.tau, .idx, sCopyP RecField.ts.tag 0⟩, Pc.prog ⟨.one, .zero, sCopyP RecField.ph.tag 0⟩,
    Pc.prog ⟨.one, .zero, sCopyP RecField.rgn.tag 0⟩, Pc.prog ⟨.one, .zero, sCopyP RecField.act.tag 1⟩]

/-- The predecessor slots of (B4). -/
def prevSlots (w τ : ℕ) : List RecSlot :=
  [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f => (List.range (f.width w τ)).map fun j => (f, j)

theorem den_b4 {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) :
    den G s (b4P) = (prevSlots (wordW V r.2) (tau V r.2)).flatMap (fun sl =>
      (sCopyItems (ownLayout V r.2) (wordExp V r.2) (2 * (ownLayout V r.2).k - 1) sl.1 sl.2 :
        List (_ × Routing.Expr F)).flatMap (itemNums mk)) := by
  have hτ := tau_lt_wordW_all V r.2
  have hdw := dims_w V r
  have hdt := dims_tau V r
  have hF := ftags_bound V
  have hwo : wordW V r.2 = 2 ^ wordExp V r.2 := wordW_eq V r.2
  have hok : ∀ f : RecField, f.tag ≤ 6 → ∀ j, j < wordW V r.2 →
      (⟨f.tag, j, 1, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) := fun f hf j hj =>
    ⟨by rw [← hwo]; exact hj, show f.tag < 2 ^ tagExp V by omega, by norm_num, by norm_num⟩
  have piece : ∀ (f : RecField) (hf : f.tag ≤ 6) (c : Cnt) (jk : JK) (cst : ℕ) (hcst : cst = if f = .act then 1 else 0)
      (hc : c.val (dims (ownRam V r) (tau V r.2)) ≤ wordW V r.2)
      (hjk : ∀ i < c.val (dims (ownRam V r) (tau V r.2)), jk.val i = i),
      den G s (Pc.prog ⟨c, jk, sCopyP f.tag cst⟩) =
        ((List.range (c.val (dims (ownRam V r) (tau V r.2)))).map fun j => (f, j)).flatMap (fun sl =>
          (sCopyItems (ownLayout V r.2) (wordExp V r.2) (2 * (ownLayout V r.2).k - 1) sl.1 sl.2 :
            List (_ × Routing.Expr F)).flatMap (itemNums mk)) := by
    intro f hf c jk cst hcst hc hjk
    rw [den_pc V r hR (fun _ => True) (fun _ _ _ _ => trivial) hb trivial _ (fun i =>
      (sCopyItems (ownLayout V r.2) (wordExp V r.2) (2 * (ownLayout V r.2).k - 1) f i :
        List (_ × Routing.Expr F)).flatMap (itemNums mk)), List.flatMap_map]
    intro i hi s' hb' _ hj
    have hi2 : i < c.val (dims (ownRam V r) (tau V r.2)) := hi
    have hj2 : s'.env vJ = i := by rw [hj]; exact hjk i hi2
    rw [hcst]
    exact den_sCopyP V mk hm0 hm1 r hR hb' f i hj2 (hok f hf i (by omega))
  simp only [b4P, den_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, prevSlots]
  rw [piece .va (by decide) .w .idx 0 rfl (by simp [Cnt.val, hdw]) (fun _ _ => rfl),
    piece .ad (by decide) .w .idx 0 rfl (by simp [Cnt.val, hdw]) (fun _ _ => rfl),
    piece .ts (by decide) .tau .idx 0 rfl (by simp only [Cnt.val, hdt]; omega) (fun _ _ => rfl),
    piece .ph (by decide) .one .zero 0 rfl (by simp only [Cnt.val]; omega)
      (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega),
    piece .rgn (by decide) .one .zero 0 rfl (by simp only [Cnt.val]; omega)
      (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega),
    piece .act (by decide) .one .zero 1 rfl (by simp only [Cnt.val]; omega)
      (fun i hi => by simp only [Cnt.val] at hi; simp [JK.val]; omega)]
  simp [Cnt.val, hdw, hdt, RecField.width, List.flatMap_append, List.append_assoc]

end NearCubicGates.Adapters.RAMACSP.Gen.Items
