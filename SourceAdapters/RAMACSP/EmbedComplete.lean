import SourceAdapters.RAMACSP.EmbedSound

/-!
# Embedding theorem, part 7 (E5): an event trace gives a table satisfying every emitted equation

Paper: the completeness direction of `thm:embedding`. Place the event-trace
values at their catalog cells, set unused network padding to zero, route the
whole records using `lem:routing`, fill the other points, and interpolate.
The resulting polynomial has degree less than |H| and satisfies every local,
copy, boundary and routing equation together with the direct input clause.

- `machine_vanish` (generic): a table that agrees with an event trace `a` on every active catalogued slot makes every
  machine item's equation vanish wherever its guard holds, when `Holds a`. (No disjointness is needed in this
  direction.)
- `table_of_trace` (generic): from `Holds a`, the routing completion (`Routing.contract.completion`) with the
  catalogued machine values as background gives such a table, which also satisfies the routing equations.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Guards Lanes Placement
open Routing Routing.Patterns

theorem two_pow_sub_one_mod (τ n : ℕ) (hn : n ≤ τ) : (2 ^ τ - 1) % 2 ^ n = 2 ^ n - 1 :=
  (mod_eq_iff_bits _ _ n (Nat.sub_lt (Nat.two_pow_pos n) (by norm_num))).mpr fun b hb => by
    rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]; simp; omega

/-! ## A table agreeing with a trace on the active catalogued slots -/

section Agree

variable {F : Type} [Field F] {l : Layout} (e : Fin l.m → F) (om K L τ : ℕ) (M : ACSP.Ram) (A : F → F) (tr : Trace F)

/-- The table agrees with the trace on the routed records (stage `0`). -/
abbrev AgSrc : Prop :=
  ∀ x < 2 ^ (τ + 1), ∀ s : RecSlot, s.Active (dims M τ) → cellAt e om A x 0 (recCell s) = tr.src x s.1 s.2
/-- … on the routed records (final stage). -/
abbrev AgDst : Prop :=
  ∀ x < 2 ^ (τ + 1), ∀ s : RecSlot, s.Active (dims M τ) → cellAt e om A x (2 * l.k - 1) (recCell s) = tr.dst x s.1 s.2
/-- … on the time rows. -/
abbrev AgTime : Prop :=
  ∀ x < 2 ^ τ, ∀ s : TSlot, s.Active (dims M τ) → cellAt e om A x 0 (tCell K L s) = tr.time x s
/-- … on the sorted vertices. -/
abbrev AgSort : Prop :=
  ∀ x < 2 ^ (τ + 1), ∀ s : SSlot, s.Active (dims M τ) → cellAt e om A x (2 * l.k - 1) (sCell M.w s) = tr.sort x s

theorem agree_timeRead (hsrc : AgSrc e om τ M A tr) (htime : AgTime e om K L τ M A tr) (x : ℕ) (hx : x < 2 ^ τ) (v : TVar) (hv : v.Active (dims M τ)) :
    cellAt e om A x 0 (cellT K L v) = tr.timeRead x v := by
  rcases v with s | ⟨f, j⟩
  · exact htime x hx s hv
  · exact hsrc x (lt_trans hx (rk_time τ)) (f, j) hv

theorem agree_sortRead (hdst : AgDst e om τ M A tr) (hsort : AgSort e om τ M A tr) (x : ℕ) (hx : x < 2 ^ (τ + 1)) (v : SVar) (hv : v.Active (dims M τ)) :
    cellAt e om A x (2 * l.k - 1) (cellS M.w v) = tr.sortRead x v := by
  rcases v with s | ⟨f, j⟩
  · exact hsort x hx s hv
  · exact hdst x hx (f, j) hv

end Agree

section Vanish

variable {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) {om dt K L τ a : ℕ} {M : ACSP.Ram}
  (c : Ctx l om dt K L τ a M) (A : F → F) (tr : Trace F) {xbar : List Bool}
include c

/-- Block 0 (T1)–(T10). -/
theorem van_te (kind : Fin M.ops → AluOp) (hsrc' : AgSrc e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hT : ∀ i < 2 ^ τ, ∀ q : TEq, q.Active (dims M τ) → (timeEq M kind τ q).eval (tr.timeRead i) = 0)
    (q : TEq) (hq : q ∈ timeEqList (dims M τ)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ τ) 0 0 ⟨tTag K L q, tBit q, 2, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v)
      (toRouting (tRead l om K L ⟨tTag K L q, tBit q, 2, 1⟩) (timeEq M kind τ q)).poly = 0 := by
  have qa := mem_timeEqList _ q hq
  have ok := tHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF q qa
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_time τ)) (c.lt_kk _ (rk_zero τ)) (Nat.two_pow_pos _) ok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  have hxT := (lane_time x τ hx).mp hlane
  show Routing.evaluate l e A (label l e x 0 _ _ _) _ = 0
  rw [evaluate_place e om A x 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos _) ok)
    (fun w hw => c.inR hx (Nat.two_pow_pos _) (c.cellTOk w (timeEq_reads_active M kind τ c.hw1 q qa w hw)))
    (fun w => tRead_eq om K L _ w)]
  rw [eval_congr_on_vars _ _ (tr.timeRead x) fun w hw =>
    agree_timeRead e om K L τ M A tr hsrc' htime' x hxT w (timeEq_reads_active M kind τ c.hw1 q qa w hw)]
  exact hT x hxT q qa


/-- Block 1: Booleanity of time-row slots. -/
theorem van_tb (htime' : AgTime e om K L τ M A tr)
    (hG : ∀ i < 2 ^ τ, ∀ s : TSlot, s.Active (dims M τ) → RAMTrace.IsBit (tr.time i s))
    (s : TSlot) (hs : s ∈ timeSlotList (dims M τ)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ τ) 0 0
      ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (boolExpr (localOffset l om
      ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩ (tCell K L s))).poly = 0 := by
  have sa := mem_timeSlotList _ s hs
  have ok := c.tOk s sa
  have hok := hostOk ok ((tCell K L s).role + 3) (by have := (tCell_role K L s).1; omega)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_time τ)) (c.lt_kk _ (rk_zero τ)) (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  have hxT := (lane_time x τ hx).mp hlane
  show Routing.evaluate l e A (label l e x 0 _ _ _) _ = 0
  rw [evaluate_bool_local e om A x 0 _ _ (c.inR hx (Nat.two_pow_pos _) hok) (c.inR hx (Nat.two_pow_pos _) ok),
    htime' x hxT s sa]
  exact sq_add_of_isBit (hG x hxT s sa)

/-- Block 2, (B1): the first lane's copied values are `0`. -/
theorem van_cp_first (hsrc' : AgSrc e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hB1 : ∀ cp : TCopy, cp.Active (dims M τ) → tr.timeRead 0 cp.dst = 0)
    (cp : TCopy) (hcp : cp ∈ copyList (dims M τ)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ l.k - 1) 0 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (Routing.Expr.read (some (localOffset l om
      ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ (dstCell K L cp)))).poly = 0 := by
  have ca := mem_copyList _ cp hcp
  have ok := dstCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF cp ca
  have hok := hostOk ok 5 (by norm_num)
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (Nat.two_pow_pos _) (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx0 : x = 0 := by
    have := (lane_low x 0 l.k).mp hlane
    rwa [Nat.mod_eq_of_lt hxk, Nat.zero_mod] at this
  subst hx0
  show Routing.evaluate l e A (label l e 0 0 _ _ _) _ = 0
  have h0 : (0 : ℕ) < 2 ^ (τ + 1) := rk_zero τ
  rw [evaluate_local e om A 0 0 _ _ (c.inR h0 (Nat.two_pow_pos _) hok) (c.inR h0 (Nat.two_pow_pos _) ok),
    dstCell_eq, agree_timeRead e om K L τ M A tr hsrc' htime' 0 (Nat.two_pow_pos _) _
      (by cases cp <;> exact ca)]
  exact hB1 cp ca

/-- Block 2, (B2): the copies from the previous lane. -/
theorem van_cp_pred (hsrc' : AgSrc e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hB2 : ∀ i, i + 1 < 2 ^ τ → ∀ cp : TCopy, cp.Active (dims M τ) → tr.timeRead (i + 1) cp.dst = tr.time i cp.src)
    (cp : TCopy) (hcp : cp ∈ copyList (dims M τ)) (t : ℕ) (ht : t < τ) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0
      ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (Routing.Expr.add (.read (some (localOffset l om
      ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ (dstCell K L cp))))
      (.read (some (laneCarry t ^^^ eta l 5 ^^^ eta l 1)))).poly = 0 := by
  have ca := mem_copyList _ cp hcp
  have ok := dstCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF cp ca
  have hok := hostOk ok 5 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_lowTime τ t ht)) (c.lt_kk _ (rk_pow τ t ht.le))
    (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  rw [Nat.add_comm (2 ^ (t + 1) - 1)] at hlane
  obtain ⟨hmod, hxT⟩ := (lane_low_time x (2 ^ t) (t + 1) τ ht (Nat.pow_lt_pow_right (by norm_num) (by omega)) hx).mp
    hlane
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · rw [Nat.zero_mod] at hmod; have := Nat.two_pow_pos t; omega
    · exact h
  show Routing.evaluate l e A (label l e x 0 _ _ _) _ = 0
  rw [evaluate_add, evaluate_local e om A x 0 _ _ (c.inR hx (Nat.two_pow_pos _) hok) (c.inR hx (Nat.two_pow_pos _) ok),
    evaluate_pred5 e A x 0 t _ (c.inR hx (Nat.two_pow_pos _) hok) (by rw [c.hk]; omega) hmod]
  obtain ⟨e1, e2, e3⟩ := srcCell_eq K L om cp
  have hsrcV : A (label l e (x - 1) 0 ((⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ : Cell).col om) 1 1) =
      tr.time (x - 1) cp.src := by
    rw [← htime' (x - 1) (by omega) cp.src (by cases cp <;> exact ca)]
    show _ = A (label l e (x - 1) 0 ((tCell K L cp.src).col om) (tCell K L cp.src).role (tCell K L cp.src).area)
    rw [e1, e2, e3]; rfl
  rw [hsrcV, dstCell_eq, agree_timeRead e om K L τ M A tr hsrc' htime' x hxT _ (by cases cp <;> exact ca)]
  have := hB2 (x - 1) (by omega) cp ca
  rw [Nat.sub_add_cancel hx1] at this
  rw [this, CharTwo.add_self_eq_zero]

/-- Block 3: (B2) `e(Out) = 0` on early time lanes. -/
theorem van_early (hsrc' : AgSrc e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hOut : ∀ i, i + 1 < 2 ^ τ → (outE M).eval (tr.timeRead i) = 0)
    (b : ℕ) (hb : b < τ) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 ⟨7, 0, 7, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (toRouting (tRead l om K L ⟨7, 0, 7, 1⟩) (outE M)).poly = 0 := by
  have hok : (⟨7, 0, 7, 1⟩ : Cell).Ok om dt :=
    ⟨Nat.two_pow_pos _, show 7 < 2 ^ dt by have := c.hF; omega, show (7 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_early τ b hb)) (c.lt_kk _ (rk_powSub τ b hb.le))
    (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  have hb1 : 2 ^ b - 1 < 2 ^ (b + 1) := by
    have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (show b < b + 1 by omega); omega
  obtain ⟨hmod, hxT⟩ := (lane_low_time x (2 ^ b - 1) (b + 1) τ hb hb1 hx).mp hlane
  have hne : x ≠ 2 ^ τ - 1 := by
    intro he
    rw [he, two_pow_sub_one_mod τ (b + 1) hb] at hmod
    have := two_pow_succ' b; have := Nat.two_pow_pos b; omega
  show Routing.evaluate l e A (label l e x 0 _ _ _) _ = 0
  rw [evaluate_place e om A x 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos _) hok)
    (fun w hw => c.inR hx (Nat.two_pow_pos _) (c.cellTOk w (outE_reads M τ w hw)))
    (fun w => tRead_eq om K L _ w)]
  rw [eval_congr_on_vars _ _ (tr.timeRead x) fun w hw =>
    agree_timeRead e om K L τ M A tr hsrc' htime' x hxT w (outE_reads M τ w hw)]
  exact hOut x (by omega)

/-- Block 3: (B3) `e(Acc) = 1` on the last time lane. -/
theorem van_last (hsrc' : AgSrc e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hAcc : (accE M).eval (tr.timeRead (2 ^ τ - 1)) = 0) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ l.k - 1) (2 ^ τ - 1) 0 ⟨7, 0, 7, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (toRouting (tRead l om K L ⟨7, 0, 7, 1⟩) (accE M)).poly = 0 := by
  have hok : (⟨7, 0, 7, 1⟩ : Cell).Ok om dt :=
    ⟨Nat.two_pow_pos _, show 7 < 2 ^ dt by have := c.hF; omega, show (7 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (c.lt_kk _ (rk_last τ)) (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  have hxe : x = 2 ^ τ - 1 := by
    have := (lane_low x (2 ^ τ - 1) l.k).mp hlane
    rwa [Nat.mod_eq_of_lt hxk, Nat.mod_eq_of_lt (c.lt_kk _ (rk_last τ))] at this
  subst hxe
  show Routing.evaluate l e A (label l e (2 ^ τ - 1) 0 _ _ _) _ = 0
  rw [evaluate_place e om A _ 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos _) hok)
    (fun w hw => c.inR hx (Nat.two_pow_pos _) (c.cellTOk w (accE_reads M τ w hw)))
    (fun w => tRead_eq om K L _ w)]
  rw [eval_congr_on_vars _ _ (tr.timeRead (2 ^ τ - 1)) fun w hw =>
    agree_timeRead e om K L τ M A tr hsrc' htime' _ (by have := Nat.two_pow_pos τ; omega) w (accE_reads M τ w hw)]
  exact hAcc

/-- Block 4: (S1)–(S5). -/
theorem van_se (hdst' : AgDst e om τ M A tr) (hsort' : AgSort e om τ M A tr)
    (hSq : ∀ j < 2 ^ (τ + 1), ∀ q : SEq, q.Active (dims M τ) → (sortEq (dims M τ) q).eval (tr.sortRead j) = 0)
    (q : SEq) (hq : q ∈ sortEqList (dims M τ)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om 0 0 (2 * l.k - 1) ⟨sTag M.w q, sBit M.w q, 2, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v)
      (toRouting (sRead l om M.w ⟨sTag M.w q, sBit M.w q, 2, 1⟩) (sortEq (dims M τ) q)).poly = 0 := by
  have qa := mem_sortEqList _ q hq
  have ok : (⟨sTag M.w q, sBit M.w q, 2, 1⟩ : Cell).Ok om dt :=
    sHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF q qa
  have g := guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin ok
  obtain ⟨x, hxk, -, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  show Routing.evaluate l e A (label l e x _ _ _ _) _ = 0
  rw [evaluate_place e om A x _ _ _ (cellS M.w) _ (c.inR hx c.hfin ok)
    (fun w hw => c.inR hx c.hfin (c.cellSOk w (sortEq_reads_active _ c.hw1 q qa w hw)))
    (fun w => sRead_eq om M.w _ w)]
  rw [eval_congr_on_vars _ _ (tr.sortRead x) fun w hw =>
    agree_sortRead e om τ M A tr hdst' hsort' x hx w (sortEq_reads_active _ c.hw1 q qa w hw)]
  exact hSq x hx q qa

/-- Block 5: Booleanity of sorted slots. -/
theorem van_sb (hsort' : AgSort e om τ M A tr)
    (hG : ∀ j < 2 ^ (τ + 1), ∀ s : SSlot, s.Active (dims M τ) → RAMTrace.IsBit (tr.sort j s))
    (s : SSlot) (hs : s ∈ sortSlotList (dims M τ)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om 0 0 (2 * l.k - 1)
      ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (boolExpr (localOffset l om
      ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩ (sCell M.w s))).poly = 0 := by
  have sa := mem_sortSlotList _ s hs
  have ok := c.sOk s sa
  have hok := hostOk ok ((sCell M.w s).role + 3) (by have := (sCell_role M.w s).1; omega)
  have g := guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin hok
  obtain ⟨x, hxk, -, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  show Routing.evaluate l e A (label l e x _ _ _ _) _ = 0
  rw [evaluate_bool_local e om A x _ _ _ (c.inR hx c.hfin hok) (c.inR hx c.hfin ok), hsort' x hx s sa]
  exact sq_add_of_isBit (hG x hx s sa)

/-- Block 6, (B4): the sentinel at the first sorted lane. -/
theorem van_b4_first (hsort' : AgSort e om τ M A tr)
    (hB4s : ∀ f k, (SSlot.prev f k).Active (dims M τ) → tr.sort 0 (.prev f k) = sentinel f)
    (s : RecSlot) (hs : s ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ l.k - 1) 0 (2 * l.k - 1)
      ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (Routing.Expr.add (.read (some (localOffset l om
      ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ (sCell M.w (.prev s.1 s.2)))))
      (.const (if s.1 = .act then 1 else 0))).poly = 0 := by
  obtain ⟨hf, hj⟩ := mem_prevs hs
  have sa : (SSlot.prev s.1 s.2).Active (dims M τ) := ⟨hf, hj⟩
  have ok := c.sOk _ sa
  have hok := hostOk ok 6 (by norm_num)
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (Nat.two_pow_pos _) c.hfin hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx0 : x = 0 := by
    have := (lane_low x 0 l.k).mp hlane
    rwa [Nat.mod_eq_of_lt hxk, Nat.zero_mod] at this
  subst hx0
  have h0 : (0 : ℕ) < 2 ^ (τ + 1) := rk_zero τ
  show Routing.evaluate l e A (label l e 0 _ _ _ _) _ = 0
  rw [evaluate_add, evaluate_local e om A 0 _ _ _ (c.inR h0 c.hfin hok) (c.inR h0 c.hfin ok), evaluate_const,
    hsort' 0 h0 _ sa, hB4s _ _ sa, sentinel_eq, CharTwo.add_self_eq_zero]

/-- Block 6, (B4): the sorted predecessor copy. -/
theorem van_b4_pred (hdst' : AgDst e om τ M A tr) (hsort' : AgSort e om τ M A tr)
    (hB4c : ∀ j, j + 1 < 2 ^ (τ + 1) → ∀ f k, (SSlot.prev f k).Active (dims M τ) →
      tr.sort (j + 1) (.prev f k) = tr.dst j f k)
    (s : RecSlot) (hs : s ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)) (t : ℕ) (ht : t < l.k)
    (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ (t + 1) - 1) (2 ^ t) (2 * l.k - 1)
      ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) (Routing.Expr.add (.read (some (localOffset l om
      ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ (sCell M.w (.prev s.1 s.2)))))
      (.read (some (laneCarry t ^^^ areaMask l ^^^ eta l 6)))).poly = 0 := by
  obtain ⟨hf, hj⟩ := mem_prevs hs
  have sa : (SSlot.prev s.1 s.2).Active (dims M τ) := ⟨hf, hj⟩
  have ra : RecSlot.Active (dims M τ) s := hj
  have ok := c.sOk _ sa
  have hok := hostOk ok 6 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_low τ t (by rw [← c.hk]; exact ht)))
    (c.lt_kk _ (rk_pow τ t (by have := c.hk; omega))) c.hfin hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  have hmod : x % 2 ^ (t + 1) = 2 ^ t := by
    rw [(lane_low x (2 ^ t) (t + 1)).mp hlane, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · rw [Nat.zero_mod] at hmod; have := Nat.two_pow_pos t; omega
    · exact h
  show Routing.evaluate l e A (label l e x _ _ _ _) _ = 0
  rw [evaluate_add, evaluate_local e om A x _ _ _ (c.inR hx c.hfin hok) (c.inR hx c.hfin ok),
    evaluate_pred6 e A x _ t _ (c.inR hx c.hfin hok) ht hmod]
  have hp : A (label l e (x - 1) (2 * l.k - 1)
      ((⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ : Cell).col om) 0 0) =
      tr.dst (x - 1) s.1 s.2 := hdst' (x - 1) (by omega) s ra
  rw [hp, hsort' x hx _ sa]
  have := hB4c (x - 1) (by omega) s.1 s.2 sa
  rw [Nat.sub_add_cancel hx1] at this
  rw [this, CharTwo.add_self_eq_zero]

/-- Block 7, (B5): the input records. -/
theorem van_b5_input (lam : ℕ → Routing.Expr F) (hsrc' : AgSrc e om τ M A tr)
    (hB5 : ∀ c0 < 2 ^ a,
      tr.src (2 ^ τ + c0) .act 0 = 1 ∧ tr.src (2 ^ τ + c0) .rgn 0 = 1 ∧ tr.src (2 ^ τ + c0) .ph 0 = 0 ∧
      tr.src (2 ^ τ + c0) .st 0 = 0 ∧ (∀ j < τ, tr.src (2 ^ τ + c0) .ts j = 0) ∧
      (∀ j < M.w, tr.src (2 ^ τ + c0) .ad j = if c0.testBit j then 1 else 0) ∧
      (∀ b < M.w, tr.src (2 ^ τ + c0) .va b = if xbar.getD (c0 * M.w + b) false then 1 else 0))
    (hlam : ∀ j < τ, ∀ u < 2 ^ l.m, Routing.evaluate l e A (maskEval l.m e u) (lam j).poly = if u.testBit j then 1 else 0)
    (s : RecSlot) (hs : s ∈ recSlotList (dims M τ)) (E : Routing.Expr F)
    (hE : E ∈ inputEqs τ lam (.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) s)
    (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v) E.poly = 0 := by
  have sa := mem_recSlotList _ s hs
  have ok := c.rOk s sa
  have hok := hostOk ok 7 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_block τ a)) (c.lt_kk _ (rk_time τ)) (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  obtain ⟨hx1, hx2⟩ := (lane_input x a τ c.ha hx).mp hlane
  have hxe : x = 2 ^ τ + (x - 2 ^ τ) := by omega
  have hc0 : x - 2 ^ τ < 2 ^ a := by omega
  obtain ⟨hact, hrgn, hph, hst, hts, had, -⟩ := hB5 _ hc0
  rw [← hxe] at hact hrgn hph hst hts had
  have hin := c.inR hx (Nat.two_pow_pos _) hok
  have Y : Routing.evaluate l e A (label l e x 0 ((⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).col om) 7 1)
      (Routing.Expr.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))).poly =
      tr.src x s.1 s.2 := by
    rw [evaluate_local e om A x 0 _ _ hin (c.inR hx (Nat.two_pow_pos _) ok)]
    exact hsrc' x hx s sa
  show Routing.evaluate l e A (label l e x 0 _ 7 1) E.poly = 0
  obtain ⟨f, j⟩ := s
  have hj : j < f.width (dims M τ).w (dims M τ).τ := sa
  cases f with
  | va => simp [inputEqs] at hE
  | act =>
    simp only [inputEqs, List.mem_singleton] at hE; subst hE
    have : j = 0 := by simp [RecField.width] at hj; omega
    subst this
    rw [evaluate_add, Y, evaluate_const, hact, CharTwo.add_self_eq_zero]
  | rgn =>
    simp only [inputEqs, List.mem_singleton] at hE; subst hE
    have : j = 0 := by simp [RecField.width] at hj; omega
    subst this
    rw [evaluate_add, Y, evaluate_const, hrgn, CharTwo.add_self_eq_zero]
  | ph =>
    simp only [inputEqs, List.mem_singleton] at hE; subst hE
    have : j = 0 := by simp [RecField.width] at hj; omega
    subst this
    rw [Y, hph]
  | st =>
    simp only [inputEqs, List.mem_singleton] at hE; subst hE
    have : j = 0 := by simp [RecField.width] at hj; omega
    subst this
    rw [Y, hst]
  | ts =>
    simp only [inputEqs, List.mem_singleton] at hE; subst hE
    rw [Y, hts j hj]
  | ad =>
    have hjw : j < M.w := hj
    by_cases hjτ : j < τ
    · simp only [inputEqs, hjτ, if_true, List.mem_singleton] at hE; subst hE
      rw [evaluate_add, Y, had j hjw]
      rw [show label l e x 0 ((⟨(recCell (.ad, j)).tag, (recCell (.ad, j)).bit, 7, 1⟩ : Cell).col om) 7 1 =
          maskEval l.m e (cellMask l x 0 ((⟨(recCell (.ad, j)).tag, (recCell (.ad, j)).bit, 7, 1⟩ : Cell).col om) 7 1)
          from rfl, hlam j hjτ _ (LayoutFacts.cellMask_lt l _ _ _ _ _ hin),
        cellMask_testBit_lane l _ _ _ _ _ j hin.1 (by rw [c.hk]; omega), hxe, Nat.testBit_two_pow_add_gt hjτ,
        ← hxe, CharTwo.add_self_eq_zero]
    · simp only [inputEqs, hjτ, if_false, List.mem_singleton] at hE; subst hE
      rw [Y, had j hjw]
      have hb : (x - 2 ^ τ).testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hc0 (Nat.pow_le_pow_right (by norm_num) (by have := c.ha; omega)))
      rw [hb]
      simp

/-- Block 7, (B5): the dummy records. -/
theorem van_b5_dummy (hsrc' : AgSrc e om τ M A tr)
    (hB5d : ∀ x, 2 ^ τ + 2 ^ a ≤ x → x < 2 ^ (τ + 1) → ∀ s : RecSlot, s.Active (dims M τ) → tr.src x s.1 s.2 = 0)
    (s : RecSlot) (hs : s ∈ recSlotList (dims M τ)) (i : ℕ) (hi : i < τ - a) (v : Fin l.m → Bool)
    (hv : patternHolds (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0
      ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩) v) :
    Routing.evaluate l e A (cubeEval l.m e v)
      (Routing.Expr.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))).poly = 0 := by
  have sa := mem_recSlotList _ s hs
  have ok := c.rOk s sa
  have hok := hostOk ok 7 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_block τ (a + i))) (c.lt_kk _ (rk_dummyV τ (a + i) (by omega)))
    (Nat.two_pow_pos _) hok
  obtain ⟨x, hxk, hlane, rfl⟩ := (guardAt_cube_iff l om _ _ _ _ v g.known g.value g.stage g.col g.role g.area).mp hv
  have hx : x < 2 ^ (τ + 1) := by rw [← c.hk]; exact hxk
  obtain ⟨hx1, -⟩ := (lane_dummy x (a + i) τ (by omega) hx).mp hlane
  have hai : 2 ^ a ≤ 2 ^ (a + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  show Routing.evaluate l e A (label l e x 0 _ 7 1) _ = 0
  rw [evaluate_local e om A x 0 _ _ (c.inR hx (Nat.two_pow_pos _) hok) (c.inR hx (Nat.two_pow_pos _) ok),
    hsrc' x hx s sa]
  exact hB5d x (by omega) hx s sa

/-- **E5 (generic, machine part): every machine item vanishes where its guard holds** (`thm:embedding`: All local, copy,
boundary … equations vanish), for a table agreeing with an event trace satisfying `Holds`. -/
theorem machine_vanish (kind : Fin M.ops → AluOp) (lam : ℕ → Routing.Expr F)
    (hsrc' : AgSrc e om τ M A tr) (hdst' : AgDst e om τ M A tr) (htime' : AgTime e om K L τ M A tr)
    (hsort' : AgSort e om τ M A tr) (hH : Holds M kind τ xbar tr) (hNA : xbar.length / M.w = 2 ^ a)
    (hlam : ∀ j < τ, ∀ u < 2 ^ l.m, Routing.evaluate l e A (maskEval l.m e u) (lam j).poly = if u.testBit j then 1 else 0) :
    ∀ v, ∀ t ∈ machineItems l om K L M kind τ a lam, patternHolds t.1 v →
      Routing.evaluate l e A (cubeEval l.m e v) t.2.poly = 0 := by
  unfold Holds at hH
  dsimp only at hH
  rw [hNA] at hH
  obtain ⟨-, -, hGt, hGo, hT, hB1, hB2, hOut, hAcc, hSq, hB4s, hB4c, hB5, hB5d, -⟩ := hH
  intro v t ht hv
  dsimp only [machineItems] at ht
  rcases List.mem_append.mp ht with ht | h8
  rcases List.mem_append.mp ht with ht | h7
  rcases List.mem_append.mp ht with ht | h6
  rcases List.mem_append.mp ht with ht | h5
  rcases List.mem_append.mp ht with ht | h4
  rcases List.mem_append.mp ht with ht | h3
  rcases List.mem_append.mp ht with h1 | h2
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
    exact van_te e c A tr kind hsrc' htime' hT q hq v hv
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h2
    exact van_tb e c A tr htime' hGt s hs v hv
  · obtain ⟨cp, hcp, h⟩ := List.mem_flatMap.mp h3
    rcases List.mem_cons.mp h with rfl | h
    · exact van_cp_first e c A tr hsrc' htime' hB1 cp hcp v hv
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp h
      exact van_cp_pred e c A tr hsrc' htime' hB2 cp hcp t' (List.mem_range.mp ht') v hv
  · rcases List.mem_append.mp h4 with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact van_early e c A tr hsrc' htime' hOut b (List.mem_range.mp hb) v hv
    · rw [List.mem_singleton.mp h] at hv ⊢
      exact van_last e c A tr hsrc' htime' hAcc v hv
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h5
    exact van_se e c A tr hdst' hsort' hSq q hq v hv
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h6
    exact van_sb e c A tr hsort' hGo s hs v hv
  · obtain ⟨s, hs, h⟩ := List.mem_flatMap.mp h7
    rcases List.mem_cons.mp h with rfl | h
    · exact van_b4_first e c A tr hsort' hB4s s hs v hv
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp h
      exact van_b4_pred e c A tr hdst' hsort' hB4c s hs t' (List.mem_range.mp ht') v hv
  · obtain ⟨s, hs, h⟩ := List.mem_flatMap.mp h8
    rcases List.mem_append.mp h with h | h
    · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h
      exact van_b5_input e c A tr lam hsrc' hB5 hlam s hs E hE v hv
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      exact van_b5_dummy e c A tr hsrc' hB5d s hs i (List.mem_range.mp hi) v hv

end Vanish

/-! ## The table of an event trace (routing completion with the catalogued machine values) -/

theorem col_inj {om : ℕ} {c c' : Cell} (hb : c.bit < 2 ^ om) (hb' : c'.bit < 2 ^ om) (h : c.col om = c'.col om) :
    c.tag = c'.tag ∧ c.bit = c'.bit := by
  obtain ⟨h1, h2⟩ := LayoutFacts.block_injective om _ _ _ _ hb hb' h
  exact ⟨h2, h1⟩

theorem recField_tag_inj (f f' : RecField) (h : f.tag = f'.tag) : f = f' := by
  cases f <;> cases f' <;> simp_all [RecField.tag]

section Table

open Classical

variable {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) {om dt K L τ a : ℕ} {M : ACSP.Ram}
  (c : Ctx l om dt K L τ a M) (tr : Trace F)

/-- The value of an active record column (`0` on the unused payload columns). -/
def recPick (om τ : ℕ) (M : ACSP.Ram) (g : ℕ → RecField → ℕ → F) (x col : ℕ) : F :=
  if h : ∃ s : RecSlot, s.Active (dims M τ) ∧ (recCell s).col om = col then g x (Classical.choose h).1
    (Classical.choose h).2 else 0

omit [CharP F 2] in
include c in
theorem recPick_eq (g : ℕ → RecField → ℕ → F) (x : ℕ) (s : RecSlot) (hs : s.Active (dims M τ)) :
    recPick om τ M g x ((recCell s).col om) = g x s.1 s.2 := by
  have hex : ∃ s' : RecSlot, s'.Active (dims M τ) ∧ (recCell s').col om = (recCell s).col om := ⟨s, hs, rfl⟩
  unfold recPick
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  obtain ⟨et, eb⟩ := col_inj (c.rOk _ h1).1 (c.rOk s hs).1 h2
  have : Classical.choose hex = s := Prod.ext (recField_tag_inj _ _ et) eb
  rw [this]

/-- The background table: catalogued time and sorted values, `0` elsewhere. -/
def background (om K L τ : ℕ) (M : ACSP.Ram) (A0 : Trace F) (z : F) : F :=
  if h : ∃ p : ℕ × TSlot, p.1 < 2 ^ τ ∧ p.2.Active (dims M τ) ∧
      label l e p.1 0 ((tCell K L p.2).col om) (tCell K L p.2).role (tCell K L p.2).area = z then
    A0.time (Classical.choose h).1 (Classical.choose h).2
  else if h : ∃ p : ℕ × SSlot, p.1 < 2 ^ (τ + 1) ∧ p.2.Active (dims M τ) ∧
      label l e p.1 (2 * l.k - 1) ((sCell M.w p.2).col om) (sCell M.w p.2).role (sCell M.w p.2).area = z then
    A0.sort (Classical.choose h).1 (Classical.choose h).2
  else 0

variable (hInd : Independent l.m e)
include c hInd

omit [CharP F 2] c in
theorem not_writable (x s col r : ℕ) (hin : InRange l x s col r 1) : ¬ RoutingWritable l e (label l e x s col r 1) := by
  have hst : ∀ j < 2 * l.k, j < 2 ^ l.ell := fun j hj => by have := l.stages_fit; omega
  rintro (⟨j, hj, x', c', he⟩ | ⟨j, hj, x', c', he⟩)
  · have := (LayoutFacts.label_eq_iff l e hInd _ _ _ _ _ _ _ _ _ _ hin
      ⟨x'.isLt, hst j hj, c'.isLt, by norm_num, by norm_num⟩).mp he
    omega
  · have := (LayoutFacts.label_eq_iff l e hInd _ _ _ _ _ _ _ _ _ _ hin
      ⟨x'.isLt, hst j (by unfold switchCount at hj; omega), c'.isLt, by norm_num, by norm_num⟩).mp he
    omega

omit [CharP F 2] in
theorem background_time (x : ℕ) (hx : x < 2 ^ τ) (s : TSlot) (hs : s.Active (dims M τ)) :
    background e om K L τ M tr (label l e x 0 ((tCell K L s).col om) (tCell K L s).role (tCell K L s).area) =
      tr.time x s := by
  have hex : ∃ p : ℕ × TSlot, p.1 < 2 ^ τ ∧ p.2.Active (dims M τ) ∧
      label l e p.1 0 ((tCell K L p.2).col om) (tCell K L p.2).role (tCell K L p.2).area =
        label l e x 0 ((tCell K L s).col om) (tCell K L s).role (tCell K L s).area := ⟨(x, s), hx, hs, rfl⟩
  unfold background
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have hx' : x < 2 ^ (τ + 1) := lt_trans hx (rk_time τ)
  have ok := c.tOk s hs
  have ok' := c.tOk _ h2
  obtain ⟨e1, -, e3, e4, -⟩ := (LayoutFacts.label_eq_iff l e hInd _ _ _ _ _ _ _ _ _ _
    (c.inR (lt_trans h1 (rk_time τ)) (Nat.two_pow_pos _) ok') (c.inR hx' (Nat.two_pow_pos _) ok)).mp h3
  obtain ⟨et, eb⟩ := col_inj ok'.1 ok.1 e3
  have := tCell_inj (dims M τ) K L c.hK c.hL _ s h2 hs et eb e4
  have hp : Classical.choose hex = (x, s) := Prod.ext e1 this
  rw [hp]

omit [CharP F 2] in
theorem background_sort (x : ℕ) (hx : x < 2 ^ (τ + 1)) (s : SSlot) (hs : s.Active (dims M τ)) :
    background e om K L τ M tr
      (label l e x (2 * l.k - 1) ((sCell M.w s).col om) (sCell M.w s).role (sCell M.w s).area) = tr.sort x s := by
  have ok := c.sOk s hs
  have hnt : ¬ ∃ p : ℕ × TSlot, p.1 < 2 ^ τ ∧ p.2.Active (dims M τ) ∧
      label l e p.1 0 ((tCell K L p.2).col om) (tCell K L p.2).role (tCell K L p.2).area =
        label l e x (2 * l.k - 1) ((sCell M.w s).col om) (sCell M.w s).role (sCell M.w s).area := by
    rintro ⟨p, h1, h2, h3⟩
    have := (LayoutFacts.label_eq_iff l e hInd _ _ _ _ _ _ _ _ _ _
      (c.inR (lt_trans h1 (rk_time τ)) (Nat.two_pow_pos _) (c.tOk _ h2)) (c.inR hx c.hfin ok)).mp h3
    have := c.fin_pos
    omega
  have hex : ∃ p : ℕ × SSlot, p.1 < 2 ^ (τ + 1) ∧ p.2.Active (dims M τ) ∧
      label l e p.1 (2 * l.k - 1) ((sCell M.w p.2).col om) (sCell M.w p.2).role (sCell M.w p.2).area =
        label l e x (2 * l.k - 1) ((sCell M.w s).col om) (sCell M.w s).role (sCell M.w s).area := ⟨(x, s), hx, hs, rfl⟩
  unfold background
  rw [dif_neg hnt, dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have ok' := c.sOk _ h2
  obtain ⟨e1, -, e3, -, -⟩ := (LayoutFacts.label_eq_iff l e hInd _ _ _ _ _ _ _ _ _ _
    (c.inR h1 c.hfin ok') (c.inR hx c.hfin ok)).mp h3
  obtain ⟨et, eb⟩ := col_inj ok'.1 ok.1 e3
  have := sCell_inj (dims M τ) c.hw1 c.hκ _ s h2 hs et eb
  have hp : Classical.choose hex = (x, s) := Prod.ext e1 this
  rw [hp]

end Table

/-- **E5 (generic, table part): the table of an event trace** (`thm:embedding` COMPLETENESS and Full embedding equivalence,
converse): route the endpoint records (stage `0` = the source records, final stage = the sorted records, unused payload
columns `0`) with the catalogued machine values as background; the routed table satisfies the routing equations and
agrees with the trace on every active catalogued slot. -/
theorem table_of_trace {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) (hInd : Independent l.m e)
    {om dt K L τ a : ℕ} {M : ACSP.Ram} (c : Ctx l om dt K L τ a M) (kind : Fin M.ops → AluOp) (xbar : List Bool)
    (tr : Trace F) (hH : Holds M kind τ xbar tr) :
    ∃ A' : F → F, LocalRouting l e A' ∧ AgSrc e om τ M A' tr ∧ AgDst e om τ M A' tr ∧
      AgTime e om K L τ M A' tr ∧ AgSort e om τ M A' tr := by
  unfold Holds at hH
  dsimp only at hH
  obtain ⟨hGs, hGd, -, -, -, -, -, -, -, -, -, -, -, -, hP⟩ := hH
  let eqv : Lane l.k ≃ Fin (2 ^ (τ + 1)) := BitVec.equivFin.toEquiv.trans (finCongr (by rw [c.hk]))
  let U : Lane l.k → Fin l.C → F := fun x cc => recPick om τ M tr.src x.toNat cc.val
  let W : Lane l.k → Fin l.C → F := fun x cc => recPick om τ M tr.dst x.toNat cc.val
  have hxk : ∀ x : Lane l.k, x.toNat < 2 ^ (τ + 1) := fun x => by rw [← c.hk]; exact x.isLt
  have hU : ∀ x cc, Routing.IsBit (U x cc) := by
    intro x cc
    show Routing.IsBit (recPick om τ M tr.src x.toNat cc.val)
    unfold recPick
    split
    · next h => exact hGs x.toNat (hxk x) _ (Classical.choose_spec h).1
    · exact Or.inl rfl
  have hW : ∀ x cc, Routing.IsBit (W x cc) := by
    intro x cc
    show Routing.IsBit (recPick om τ M tr.dst x.toNat cc.val)
    unfold recPick
    split
    · next h => exact hGd x.toNat (hxk x) _ (Classical.choose_spec h).1
    · exact Or.inl rfl
  obtain ⟨π0, hπ0⟩ := hP
  have hπ : ∃ π : Equiv.Perm (Lane l.k), ∀ x cc, W (π x) cc = U x cc := by
    refine ⟨eqv.trans (π0.trans eqv.symm), fun x cc => ?_⟩
    show recPick om τ M tr.dst (eqv.symm (π0 (eqv x))).toNat cc.val = recPick om τ M tr.src x.toNat cc.val
    unfold recPick
    split
    · next h => exact hπ0 (eqv x) _ (Classical.choose_spec h).1
    · rfl
  obtain ⟨A', hLR, h0, hfin, hbg⟩ :=
    Routing.contract.completion l e hInd U W hU hW hπ (background e om K L τ M tr)
  have hst0 : 0 < 2 ^ l.ell := Nat.two_pow_pos _
  refine ⟨A', hLR, ?_, ?_, ?_, ?_⟩
  · intro x hx s hs
    have hcol : (recCell s).col om < l.C := by rw [Layout.C, c.hq]; exact Cell.col_lt (c.rOk s hs)
    have h := h0 (BitVec.ofNat l.k x) ⟨(recCell s).col om, hcol⟩
    unfold dataValue at h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)] at h
    show A' (label l e x 0 ((recCell s).col om) 0 0) = _
    rw [h]
    show recPick om τ M tr.src (BitVec.ofNat l.k x).toNat ((recCell s).col om) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)]
    exact recPick_eq c tr.src x s hs
  · intro x hx s hs
    have hcol : (recCell s).col om < l.C := by rw [Layout.C, c.hq]; exact Cell.col_lt (c.rOk s hs)
    have h := hfin (BitVec.ofNat l.k x) ⟨(recCell s).col om, hcol⟩
    unfold dataValue switchCount at h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)] at h
    show A' (label l e x (2 * l.k - 1) ((recCell s).col om) 0 0) = _
    rw [h]
    show recPick om τ M tr.dst (BitVec.ofNat l.k x).toNat ((recCell s).col om) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)]
    exact recPick_eq c tr.dst x s hs
  · intro x hx s hs
    have ok := c.tOk s hs
    have hx' : x < 2 ^ (τ + 1) := lt_trans hx (rk_time τ)
    have hin := c.inR hx' hst0 ok
    have ha1 := (tCell_role K L s).2
    have hnw : ¬ RoutingWritable l e (label l e x 0 ((tCell K L s).col om) (tCell K L s).role (tCell K L s).area) := by
      rw [ha1] at hin ⊢; exact not_writable e hInd x 0 _ _ hin
    show A' _ = _
    rw [hbg _ hnw]
    exact background_time e c tr hInd x hx s hs
  · intro x hx s hs
    have ok := c.sOk s hs
    have hin := c.inR hx c.hfin ok
    have ha1 := (sCell_role M.w s).2
    have hnw : ¬ RoutingWritable l e
        (label l e x (2 * l.k - 1) ((sCell M.w s).col om) (sCell M.w s).role (sCell M.w s).area) := by
      rw [ha1] at hin ⊢; exact not_writable e hInd x _ _ _ hin
    show A' _ = _
    rw [hbg _ hnw]
    exact background_sort e c tr hInd x hx s hs

end NearCubicGates.Adapters.RAMACSP
