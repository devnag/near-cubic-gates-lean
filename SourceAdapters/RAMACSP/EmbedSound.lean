import SourceAdapters.RAMACSP.EmbedPlace
import SourceAdapters.Routing.Final

/-!
# Embedding theorem, part 6 (E4): a table satisfying every emitted equation is an event trace

Paper: the soundness direction of `thm:embedding`. A table satisfying the
emitted equations gives every event-trace equation and Booleanity condition.
Routing soundness yields one permutation of whole endpoint records; the
direct input clause supplies the input-record values omitted from the circuit.

`holds_of_table` (generic in the layout): if every machine item's equation vanishes where its guard holds, the table
satisfies the routing equations (`LocalRouting`), the coordinate expressions are the coordinates, and the input
records carry `x̄` in their `va` slots, then `traceOf A` satisfies `Holds` (`def:event-trace`) — every clause (G),
(T1)–(T10), (B1)–(B5), (S1)–(S5), (P).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Guards Lanes Placement
open Routing

/-! ## Membership of the machine items (the catalog is emitted) -/

section Mem

variable {F : Type} [Field F] (l : Layout) (om K L : ℕ) (M : ACSP.Ram) (kind : Fin M.ops → AluOp) (τ a : ℕ)
  (lam : ℕ → Routing.Expr F)

theorem mem_te (q : TEq) (hq : q ∈ timeEqList (dims M τ)) :
    (guardAt l om (2 ^ τ) 0 0 ⟨tTag K L q, tBit q, 2, 1⟩,
      toRouting (tRead l om K L ⟨tTag K L q, tBit q, 2, 1⟩) (timeEq M kind τ q)) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hq)))))))

theorem mem_tb (s : TSlot) (hs : s ∈ timeSlotList (dims M τ)) :
    (guardAt l om (2 ^ τ) 0 0 ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩,
      boolExpr (localOffset l om ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩ (tCell K L s))) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hs)))))))

theorem mem_cp_first (cp : TCopy) (hcp : cp ∈ copyList (dims M τ)) :
    (guardAt l om (2 ^ l.k - 1) 0 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩,
      Routing.Expr.read (some (localOffset l om ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩
        (dstCell K L cp)))) ∈ machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨cp, hcp, List.mem_cons_self⟩))))))

theorem mem_cp_pred (cp : TCopy) (hcp : cp ∈ copyList (dims M τ)) (t : ℕ) (ht : t < τ) :
    (guardAt l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩,
      Routing.Expr.add (.read (some (localOffset l om ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩
        (dstCell K L cp)))) (.read (some (laneCarry t ^^^ eta l 5 ^^^ eta l 1)))) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨cp, hcp, List.mem_cons_of_mem _
      (List.mem_map_of_mem (List.mem_range.mpr ht))⟩))))))

theorem mem_b3_early (b : ℕ) (hb : b < τ) :
    (guardAt l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 ⟨7, 0, 7, 1⟩,
      toRouting (tRead l om K L ⟨7, 0, 7, 1⟩) (outE M)) ∈ machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hb)))))))

theorem mem_b3_last :
    (guardAt l om (2 ^ l.k - 1) (2 ^ τ - 1) 0 ⟨7, 0, 7, 1⟩,
      toRouting (tRead l om K L ⟨7, 0, 7, 1⟩) (accE M)) ∈ machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _))))))

theorem mem_se (q : SEq) (hq : q ∈ sortEqList (dims M τ)) :
    (guardAt l om 0 0 (2 * l.k - 1) ⟨sTag M.w q, sBit M.w q, 2, 1⟩,
      toRouting (sRead l om M.w ⟨sTag M.w q, sBit M.w q, 2, 1⟩) (sortEq (dims M τ) q)) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map_of_mem hq))))

theorem mem_sb (s : SSlot) (hs : s ∈ sortSlotList (dims M τ)) :
    (guardAt l om 0 0 (2 * l.k - 1) ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩,
      boolExpr (localOffset l om ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩ (sCell M.w s))) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hs)))

theorem mem_b4_first (s : RecSlot)
    (hs : s ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)) :
    (guardAt l om (2 ^ l.k - 1) 0 (2 * l.k - 1)
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩,
      Routing.Expr.add (.read (some (localOffset l om
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ (sCell M.w (.prev s.1 s.2)))))
        (.const (if s.1 = .act then 1 else 0))) ∈ machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_self⟩))

theorem mem_b4_pred (s : RecSlot)
    (hs : s ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)) (t : ℕ) (ht : t < l.k) :
    (guardAt l om (2 ^ (t + 1) - 1) (2 ^ t) (2 * l.k - 1)
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩,
      Routing.Expr.add (.read (some (localOffset l om
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ (sCell M.w (.prev s.1 s.2)))))
        (.read (some (laneCarry t ^^^ areaMask l ^^^ eta l 6)))) ∈ machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs,
    List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.mpr ht))⟩))

theorem mem_b5_input (s : RecSlot) (hs : s ∈ recSlotList (dims M τ)) (E : Routing.Expr F)
    (hE : E ∈ inputEqs τ lam (.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) s) :
    (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩, E) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_append_left _ (List.mem_map_of_mem hE)⟩)

theorem mem_b5_dummy (s : RecSlot) (hs : s ∈ recSlotList (dims M τ)) (i : ℕ) (hi : i < τ - a) :
    (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩,
      Routing.Expr.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) ∈
      machineItems l om K L M kind τ a lam := by
  dsimp only [machineItems]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs,
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi))⟩)

end Mem

/-! ## Cells of copies and records -/

theorem dstCell_eq (K L : ℕ) (cp : TCopy) : dstCell K L cp = cellT K L cp.dst := by cases cp <;> rfl

theorem srcCell_eq (K L om : ℕ) (cp : TCopy) :
    (tCell K L cp.src).col om = (dstCell K L cp).col om ∧ (tCell K L cp.src).role = 1 ∧ (tCell K L cp.src).area = 1 := by
  cases cp <;> simp [tCell, dstCell, recCell, Cell.col, TCopy.src, TCopy.dst, RecField.tag]

theorem sentinel_eq {F : Type} [CommRing F] (f : RecField) : (sentinel f : F) = if f = .act then 1 else 0 := by
  cases f <;> simp [sentinel]

theorem mod_pred (i P Q : ℕ) (hQ : 1 ≤ Q) (h : (i + 1) % P = Q) : i % P = Q - 1 := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp only [Nat.mod_zero] at h ⊢; omega
  have h1 := Nat.mod_add_div (i + 1) P
  have h2 := Nat.mod_lt (i + 1) hP
  rw [h] at h1 h2
  rw [show i = (Q - 1) + P * ((i + 1) / P) by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem cellMask_testBit_lane (l : Layout) (x s c r a j : ℕ) (hx : x < 2 ^ l.k) (hj : j < l.k) :
    (cellMask l x s c r a).testBit j = x.testBit j := by
  unfold cellMask
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx, if_pos hj]


/-! ## The context's cells are in range -/

section CtxCells

variable {l : Layout} {om dt K L τ a : ℕ} {M : ACSP.Ram} (c : Ctx l om dt K L τ a M)
include c

theorem Ctx.inR {x s : ℕ} {h : Cell} (hx : x < 2 ^ (τ + 1)) (hs : s < 2 ^ l.ell) (hh : h.Ok om dt) :
    InRange l x s (h.col om) h.role h.area :=
  ⟨by rw [c.hk]; exact hx, hs, by rw [Layout.C, c.hq]; exact Cell.col_lt hh, hh.2.2.1, hh.2.2.2⟩

theorem Ctx.tOk (s : TSlot) (hs : s.Active (dims M τ)) : (tCell K L s).Ok om dt :=
  tCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF s hs

theorem Ctx.rOk (s : RecSlot) (hs : s.Active (dims M τ)) : (recCell s).Ok om dt :=
  recCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF s hs

theorem Ctx.sOk (s : SSlot) (hs : s.Active (dims M τ)) : (sCell M.w s).Ok om dt :=
  sCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF s hs

theorem Ctx.cellTOk (v : TVar) (hv : v.Active (dims M τ)) : (cellT K L v).Ok om dt := by
  cases v with
  | inl s => exact c.tOk s hv
  | inr s => exact c.rOk s hv

theorem Ctx.cellSOk (v : SVar) (hv : v.Active (dims M τ)) : (cellS M.w v).Ok om dt := by
  cases v with
  | inl s => exact c.sOk s hv
  | inr s => exact c.rOk s hv

theorem Ctx.lt_kk (x : ℕ) (hx : x < 2 ^ (τ + 1)) : x < 2 ^ l.k := by rw [c.hk]; exact hx

end CtxCells

theorem hostOk {om dt : ℕ} {h : Cell} (hc : h.Ok om dt) (rr : ℕ) (hr : rr < 8) :
    (⟨h.tag, h.bit, rr, 1⟩ : Cell).Ok om dt :=
  ⟨hc.1, hc.2.1, hr, show (1 : ℕ) < 2 by norm_num⟩

/-! ## Every clause of `Holds` -/

section Clauses

variable {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) {om dt K L τ a : ℕ} {M : ACSP.Ram}
  (c : Ctx l om dt K L τ a M) (kind : Fin M.ops → AluOp) (lam : ℕ → Routing.Expr F) (A : F → F)
  (hS : ∀ v, ∀ t ∈ machineItems l om K L M kind τ a lam, patternHolds t.1 v →
    Routing.evaluate l e A (cubeEval l.m e v) t.2.poly = 0)
include c

omit [CharP F 2] in
theorem cl_srcBit (hR : LocalRouting l e A) :
    ∀ x < 2 ^ (τ + 1), ∀ s : RecSlot, s.Active (dims M τ) → RAMTrace.IsBit ((traceOf e om K L M.w (2 * l.k - 1) A).src x s.1 s.2) := by
  intro x hx s hs
  have hc := (c.rOk s hs)
  have h := hR.1 0 (by have := l.k_pos; omega) (BitVec.ofNat l.k x)
    ⟨(recCell s).col om, by rw [Layout.C, c.hq]; exact Cell.col_lt hc⟩
  unfold dataValue at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)] at h
  exact h

omit [CharP F 2] in
theorem cl_dstBit (hR : LocalRouting l e A) :
    ∀ x < 2 ^ (τ + 1), ∀ s : RecSlot, s.Active (dims M τ) → RAMTrace.IsBit ((traceOf e om K L M.w (2 * l.k - 1) A).dst x s.1 s.2) := by
  intro x hx s hs
  have hc := (c.rOk s hs)
  have h := hR.1 (2 * l.k - 1) (by have := l.k_pos; omega) (BitVec.ofNat l.k x)
    ⟨(recCell s).col om, by rw [Layout.C, c.hq]; exact Cell.col_lt hc⟩
  unfold dataValue at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.lt_kk x hx)] at h
  exact h

include hS

theorem cl_timeBit : ∀ i < 2 ^ τ, ∀ s : TSlot, s.Active (dims M τ) → RAMTrace.IsBit ((traceOf e om K L M.w (2 * l.k - 1) A).time i s) := by
  intro i hi s hs
  have hm := mem_tb l om K L M kind τ a lam s (mem_timeSlotList_of_active _ s hs)
  have ok := c.tOk s hs
  have hok := hostOk ok ((tCell K L s).role + 3) (by have := (tCell_role K L s).1; omega)
  have hx : i < 2 ^ (τ + 1) := lt_trans hi (rk_time τ)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_time τ)) (c.lt_kk _ (rk_zero τ)) (Nat.two_pow_pos l.ell) hok
  have h0 := fire e om A hS hm g i (c.lt_kk i hx) ((lane_time i τ hx).mpr hi)
  rw [evaluate_bool_local e om A i 0 _ _ (c.inR hx (Nat.two_pow_pos l.ell) hok) (c.inR hx (Nat.two_pow_pos l.ell) ok)] at h0
  exact isBit_of_sq_add h0

theorem cl_sortBit :
    ∀ j < 2 ^ (τ + 1), ∀ s : SSlot, s.Active (dims M τ) → RAMTrace.IsBit ((traceOf e om K L M.w (2 * l.k - 1) A).sort j s) := by
  intro j hj s hs
  have hm := mem_sb l om K L M kind τ a lam s (mem_sortSlotList_of_active _ s hs)
  have ok := c.sOk s hs
  have hok := hostOk ok ((sCell M.w s).role + 3) (by have := (sCell_role M.w s).1; omega)
  have g := guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin hok
  have h0 := fire e om A hS hm g j (c.lt_kk j hj) (by simp)
  rw [evaluate_bool_local e om A j _ _ _ (c.inR hj c.hfin hok) (c.inR hj c.hfin ok)] at h0
  exact isBit_of_sq_add h0

theorem cl_timeEq : ∀ i < 2 ^ τ, ∀ q : TEq, q.Active (dims M τ) →
    (timeEq M kind τ q).eval ((traceOf e om K L M.w (2 * l.k - 1) A).timeRead i) = 0 := by
  intro i hi q hq
  have hm := mem_te l om K L M kind τ a lam q (mem_timeEqList_of_active _ q hq)
  have ok := tHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF q hq
  have hx : i < 2 ^ (τ + 1) := lt_trans hi (rk_time τ)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_time τ)) (c.lt_kk _ (rk_zero τ)) (Nat.two_pow_pos l.ell) ok
  have h0 := fire e om A hS hm g i (c.lt_kk i hx) ((lane_time i τ hx).mpr hi)
  rw [evaluate_place e om A i 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos l.ell) ok)
    (fun v hv => c.inR hx (Nat.two_pow_pos l.ell) (c.cellTOk v (timeEq_reads_active M kind τ (c.hw1) q hq v hv)))
    (fun v => tRead_eq om K L _ v)] at h0
  rw [show (traceOf e om K L M.w (2 * l.k - 1) A).timeRead i = fun v => cellAt e om A i 0 (cellT K L v) from
    funext (timeRead_traceOf e om K L M.w (2 * l.k - 1) A i)]
  exact h0

theorem cl_first : ∀ cp : TCopy, cp.Active (dims M τ) → (traceOf e om K L M.w (2 * l.k - 1) A).timeRead 0 cp.dst = 0 := by
  intro cp hcp
  have hm := mem_cp_first l om K L M kind τ a lam cp (mem_copyList_of_active _ cp hcp)
  have ok := dstCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF cp hcp
  have hok := hostOk ok 5 (by norm_num)
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (Nat.two_pow_pos _) (Nat.two_pow_pos l.ell) hok
  have h0 := fire e om A hS hm g 0 (Nat.two_pow_pos _) rfl
  rw [evaluate_local e om A 0 0 _ _ (c.inR (rk_zero τ) (Nat.two_pow_pos l.ell) hok) (c.inR (rk_zero τ) (Nat.two_pow_pos l.ell) ok)] at h0
  rw [timeRead_traceOf, ← dstCell_eq]
  exact h0

theorem cl_copy : ∀ i, i + 1 < 2 ^ τ → ∀ cp : TCopy, cp.Active (dims M τ) →
    (traceOf e om K L M.w (2 * l.k - 1) A).timeRead (i + 1) cp.dst = (traceOf e om K L M.w (2 * l.k - 1) A).time i cp.src := by
  intro i hi cp hcp
  obtain ⟨t, ht1, ht2⟩ := exists_low_bit (i + 1) (by omega)
  have htτ : t < τ := low_bit_lt (i + 1) τ t hi ht2
  have hm := mem_cp_pred l om K L M kind τ a lam cp (mem_copyList_of_active _ cp hcp) t htτ
  have ok := dstCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF cp hcp
  have hok := hostOk ok 5 (by norm_num)
  have hx : i + 1 < 2 ^ (τ + 1) := lt_trans hi (rk_time τ)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_lowTime τ t htτ)) (c.lt_kk _ (rk_pow τ t htτ.le))
    (Nat.two_pow_pos l.ell) hok
  have hlane : (i + 1) &&& (2 ^ (t + 1) - 1 + 2 ^ τ) = 2 ^ t &&& (2 ^ (t + 1) - 1 + 2 ^ τ) := by
    rw [Nat.add_comm (2 ^ (t + 1) - 1)]
    exact (lane_low_time (i + 1) (2 ^ t) (t + 1) τ htτ (Nat.pow_lt_pow_right (by norm_num) (by omega)) hx).mpr
      ⟨ht1, hi⟩
  have h0 := fire e om A hS hm g (i + 1) (c.lt_kk _ hx) hlane
  rw [evaluate_add, evaluate_local e om A (i + 1) 0 _ _ (c.inR hx (Nat.two_pow_pos l.ell) hok) (c.inR hx (Nat.two_pow_pos l.ell) ok),
    evaluate_pred5 e A (i + 1) 0 t _ (c.inR hx (Nat.two_pow_pos l.ell) hok) (by rw [c.hk]; omega) ht1] at h0
  rw [timeRead_traceOf, ← dstCell_eq, eq_of_add_eq_zero_two h0, Nat.add_sub_cancel]
  obtain ⟨e1, e2, e3⟩ := srcCell_eq K L om cp
  show _ = A (label l e i 0 ((tCell K L cp.src).col om) (tCell K L cp.src).role (tCell K L cp.src).area)
  rw [e1, e2, e3]
  rfl

theorem cl_out : ∀ i, i + 1 < 2 ^ τ → (outE M).eval ((traceOf e om K L M.w (2 * l.k - 1) A).timeRead i) = 0 := by
  intro i hi
  obtain ⟨b, hb1, hb2⟩ := exists_low_bit (i + 1) (by omega)
  have hbτ : b < τ := low_bit_lt (i + 1) τ b hi hb2
  have hi' : i % 2 ^ (b + 1) = 2 ^ b - 1 := mod_pred i _ _ Nat.one_le_two_pow hb1
  have hm := mem_b3_early l om K L M kind τ a lam b hbτ
  have hok : (⟨7, 0, 7, 1⟩ : Cell).Ok om dt :=
    ⟨Nat.two_pow_pos _, show 7 < 2 ^ dt by have := c.hF; omega, show (7 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have hx : i < 2 ^ (τ + 1) := by have := rk_time τ; omega
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_early τ b hbτ)) (c.lt_kk _ (rk_powSub τ b hbτ.le))
    (Nat.two_pow_pos l.ell) hok
  have hlane := (lane_low_time i (2 ^ b - 1) (b + 1) τ hbτ
    (by have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (show b < b + 1 by omega); omega) hx).mpr
    ⟨hi', by omega⟩
  have h0 := fire e om A hS hm g i (c.lt_kk i hx) hlane
  rw [evaluate_place e om A i 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos l.ell) hok)
    (fun v hv => c.inR hx (Nat.two_pow_pos l.ell) (c.cellTOk v (outE_reads M τ v hv)))
    (fun v => tRead_eq om K L _ v)] at h0
  rw [show (traceOf e om K L M.w (2 * l.k - 1) A).timeRead i = fun v => cellAt e om A i 0 (cellT K L v) from
    funext (timeRead_traceOf e om K L M.w (2 * l.k - 1) A i)]
  exact h0

theorem cl_acc : (accE M).eval ((traceOf e om K L M.w (2 * l.k - 1) A).timeRead (2 ^ τ - 1)) = 0 := by
  have hm := mem_b3_last l om K L M kind τ a lam
  have hok : (⟨7, 0, 7, 1⟩ : Cell).Ok om dt :=
    ⟨Nat.two_pow_pos _, show 7 < 2 ^ dt by have := c.hF; omega, show (7 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have hx : 2 ^ τ - 1 < 2 ^ (τ + 1) := rk_last τ
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (c.lt_kk _ (rk_last τ)) (Nat.two_pow_pos l.ell) hok
  have h0 := fire e om A hS hm g (2 ^ τ - 1) (c.lt_kk _ hx) rfl
  rw [evaluate_place e om A _ 0 _ _ (cellT K L) _ (c.inR hx (Nat.two_pow_pos l.ell) hok)
    (fun v hv => c.inR hx (Nat.two_pow_pos l.ell) (c.cellTOk v (accE_reads M τ v hv)))
    (fun v => tRead_eq om K L _ v)] at h0
  rw [show (traceOf e om K L M.w (2 * l.k - 1) A).timeRead (2 ^ τ - 1) = fun v => cellAt e om A (2 ^ τ - 1) 0 (cellT K L v) from
    funext (timeRead_traceOf e om K L M.w (2 * l.k - 1) A _)]
  exact h0

theorem cl_sortEq : ∀ j < 2 ^ (τ + 1), ∀ q : SEq, q.Active (dims M τ) →
    (sortEq (dims M τ) q).eval ((traceOf e om K L M.w (2 * l.k - 1) A).sortRead j) = 0 := by
  intro j hj q hq
  have hm := mem_se l om K L M kind τ a lam q (mem_sortEqList_of_active _ q hq)
  have ok : (⟨sTag M.w q, sBit M.w q, 2, 1⟩ : Cell).Ok om dt :=
    sHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF q hq
  have g := guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin ok
  have h0 := fire e om A hS hm g j (c.lt_kk j hj) (by simp)
  rw [evaluate_place e om A j _ _ _ (cellS M.w) _ (c.inR hj c.hfin ok)
    (fun v hv => c.inR hj c.hfin (c.cellSOk v (sortEq_reads_active _ c.hw1 q hq v hv)))
    (fun v => sRead_eq om M.w _ v)] at h0
  rw [show (traceOf e om K L M.w (2 * l.k - 1) A).sortRead j = fun v => cellAt e om A j (2 * l.k - 1) (cellS M.w v) from
    funext (sortRead_traceOf e om K L M.w (2 * l.k - 1) A j)]
  exact h0

theorem cl_sentinel : ∀ f k, (SSlot.prev f k).Active (dims M τ) → (traceOf e om K L M.w (2 * l.k - 1) A).sort 0 (.prev f k) = sentinel f := by
  intro f k hfk
  have hs := mem_prevSlots_of_active (dims M τ).w (dims M τ).τ f k hfk.1 hfk.2
  have hm := mem_b4_first l om K L M kind τ a lam (f, k) hs
  dsimp only at hm
  have ok := c.sOk _ hfk
  have hok := hostOk ok 6 (by norm_num)
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq hk1 (Nat.two_pow_pos _) c.hfin hok
  have h0 := fire e om A hS hm g 0 (Nat.two_pow_pos _) rfl
  rw [evaluate_add, evaluate_local e om A 0 _ _ _ (c.inR (rk_zero τ) c.hfin hok) (c.inR (rk_zero τ) c.hfin ok),
    evaluate_const] at h0
  rw [sentinel_eq]
  exact eq_of_add_eq_zero_two h0

theorem cl_prevCopy : ∀ j, j + 1 < 2 ^ (τ + 1) → ∀ f k, (SSlot.prev f k).Active (dims M τ) →
    (traceOf e om K L M.w (2 * l.k - 1) A).sort (j + 1) (.prev f k) = (traceOf e om K L M.w (2 * l.k - 1) A).dst j f k := by
  intro j hj f k hfk
  obtain ⟨t, ht1, ht2⟩ := exists_low_bit (j + 1) (by omega)
  have htk : t < l.k := low_bit_lt (j + 1) l.k t (c.lt_kk _ hj) ht2
  have hs := mem_prevSlots_of_active (dims M τ).w (dims M τ).τ f k hfk.1 hfk.2
  have hm := mem_b4_pred l om K L M kind τ a lam (f, k) hs t htk
  dsimp only at hm
  have ok := c.sOk _ hfk
  have hok := hostOk ok 6 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_low τ t (by rw [← c.hk]; exact htk)))
    (c.lt_kk _ (rk_pow τ t (by have := c.hk; omega))) c.hfin hok
  have hlane : (j + 1) &&& (2 ^ (t + 1) - 1) = 2 ^ t &&& (2 ^ (t + 1) - 1) := by
    rw [lane_low, ht1, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  have h0 := fire e om A hS hm g (j + 1) (c.lt_kk _ hj) hlane
  rw [evaluate_add, evaluate_local e om A (j + 1) _ _ _ (c.inR hj c.hfin hok) (c.inR hj c.hfin ok),
    evaluate_pred6 e A (j + 1) _ t _ (c.inR hj c.hfin hok) htk ht1] at h0
  show cellAt e om A (j + 1) (2 * l.k - 1) (sCell M.w (.prev f k)) = cellAt e om A j (2 * l.k - 1) (recCell (f, k))
  rw [eq_of_add_eq_zero_two h0, Nat.add_sub_cancel]
  rfl

end Clauses

section Clauses2

variable {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) {om dt K L τ a : ℕ} {M : ACSP.Ram}
  (c : Ctx l om dt K L τ a M) (kind : Fin M.ops → AluOp) (lam : ℕ → Routing.Expr F) (A : F → F)
  (hS : ∀ v, ∀ t ∈ machineItems l om K L M kind τ a lam, patternHolds t.1 v →
    Routing.evaluate l e A (cubeEval l.m e v) t.2.poly = 0)
include c hS

omit [CharP F 2] in
/-- An input-record equation fires on every input lane `T + c₀`, `c₀ < 2^a` (`app:affine-embedding` Position data: `INPUT`). -/
theorem fire_input (s : RecSlot) (hs : s.Active (dims M τ)) (c0 : ℕ) (hc0 : c0 < 2 ^ a) :
    ∀ E ∈ inputEqs τ lam (.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) s,
    Routing.evaluate l e A (label l e (2 ^ τ + c0) 0 ((⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).col om) 7 1)
      E.poly = 0 := by
  intro E hE
  have hm := mem_b5_input l om K L M kind τ a lam s (mem_recSlotList_of_active _ s hs) E hE
  have hok := hostOk (c.rOk s hs) 7 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_block τ a)) (c.lt_kk _ (rk_time τ)) (Nat.two_pow_pos _) hok
  have ha := Nat.pow_le_pow_right (show 0 < 2 by norm_num) c.ha
  have hx : 2 ^ τ + c0 < 2 ^ (τ + 1) := by rw [pow_succ]; omega
  exact fire e om A hS hm g _ (c.lt_kk _ hx) ((lane_input _ a τ c.ha hx).mpr ⟨by omega, by omega⟩)

/-- **(B5) input records** (`app:affine-embedding` B5 input/dummy: `act = rgn = 1`, `ph = ts = st = 0`, `ad[j] = λ_j(X)`; `va` from the
direct input subspace). -/
theorem cl_input (xbar : List Bool)
    (hlam : ∀ j < τ, ∀ u < 2 ^ l.m, Routing.evaluate l e A (maskEval l.m e u) (lam j).poly = if u.testBit j then 1 else 0)
    (hva : ∀ c0 < 2 ^ a, ∀ b < M.w,
      cellAt e om A (2 ^ τ + c0) 0 (recCell (.va, b)) = if xbar.getD (c0 * M.w + b) false then 1 else 0)
    (c0 : ℕ) (hc0 : c0 < 2 ^ a) :
    (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .act 0 = 1 ∧
    (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .rgn 0 = 1 ∧
    (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .ph 0 = 0 ∧
    (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .st 0 = 0 ∧
    (∀ j < τ, (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .ts j = 0) ∧
    (∀ j < M.w, (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .ad j = if c0.testBit j then 1 else 0) ∧
    (∀ b < M.w, (traceOf e om K L M.w (2 * l.k - 1) A).src (2 ^ τ + c0) .va b =
      if xbar.getD (c0 * M.w + b) false then 1 else 0) := by
  have ha := Nat.pow_le_pow_right (show 0 < 2 by norm_num) c.ha
  have hx : 2 ^ τ + c0 < 2 ^ (τ + 1) := by rw [pow_succ]; omega
  have Y : ∀ s : RecSlot, s.Active (dims M τ) →
      Routing.evaluate l e A (label l e (2 ^ τ + c0) 0 ((⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).col om) 7 1)
        (Routing.Expr.read (some (localOffset l om ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))).poly =
        cellAt e om A (2 ^ τ + c0) 0 (recCell s) := fun s hs =>
    evaluate_local e om A _ 0 _ _ (c.inR hx (Nat.two_pow_pos _) (hostOk (c.rOk s hs) 7 (by norm_num)))
      (c.inR hx (Nat.two_pow_pos _) (c.rOk s hs))
  have hw1 := c.hw1
  have hτw := c.hτw
  refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, hva c0 hc0⟩
  · have hs : RecSlot.Active (dims M τ) (.act, 0) := show 0 < 1 by norm_num
    have h0 := fire_input e c kind lam A hS (.act, 0) hs c0 hc0
    simp only [inputEqs, List.mem_singleton, forall_eq] at h0
    rw [evaluate_add, Y _ hs, evaluate_const] at h0
    exact eq_of_add_eq_zero_two h0
  · have hs : RecSlot.Active (dims M τ) (.rgn, 0) := show 0 < 1 by norm_num
    have h0 := fire_input e c kind lam A hS (.rgn, 0) hs c0 hc0
    simp only [inputEqs, List.mem_singleton, forall_eq] at h0
    rw [evaluate_add, Y _ hs, evaluate_const] at h0
    exact eq_of_add_eq_zero_two h0
  · have hs : RecSlot.Active (dims M τ) (.ph, 0) := show 0 < 1 by norm_num
    have h0 := fire_input e c kind lam A hS (.ph, 0) hs c0 hc0
    simp only [inputEqs, List.mem_singleton, forall_eq] at h0
    rw [Y _ hs] at h0
    exact h0
  · have hs : RecSlot.Active (dims M τ) (.st, 0) := show 0 < 1 by norm_num
    have h0 := fire_input e c kind lam A hS (.st, 0) hs c0 hc0
    simp only [inputEqs, List.mem_singleton, forall_eq] at h0
    rw [Y _ hs] at h0
    exact h0
  · have hs : RecSlot.Active (dims M τ) (.ts, j) := show j < τ from hj
    have h0 := fire_input e c kind lam A hS (.ts, j) hs c0 hc0
    simp only [inputEqs, List.mem_singleton, forall_eq] at h0
    rw [Y _ hs] at h0
    exact h0
  · have hs : RecSlot.Active (dims M τ) (.ad, j) := show j < (dims M τ).w from hj
    by_cases hjτ : j < τ
    · have h0 := fire_input e c kind lam A hS (.ad, j) hs c0 hc0
      simp only [inputEqs, hjτ, if_true, List.mem_singleton, forall_eq] at h0
      have hin := c.inR hx (Nat.two_pow_pos _) (hostOk (c.rOk _ hs) 7 (by norm_num))
      rw [evaluate_add, Y _ hs] at h0
      rw [show label l e (2 ^ τ + c0) 0 ((⟨(recCell (.ad, j)).tag, (recCell (.ad, j)).bit, 7, 1⟩ : Cell).col om) 7 1 =
          maskEval l.m e (cellMask l (2 ^ τ + c0) 0
            ((⟨(recCell (.ad, j)).tag, (recCell (.ad, j)).bit, 7, 1⟩ : Cell).col om) 7 1) from rfl,
        hlam j hjτ _ (LayoutFacts.cellMask_lt l _ _ _ _ _ hin),
        cellMask_testBit_lane l _ _ _ _ _ j hin.1 (by rw [c.hk]; omega),
        Nat.testBit_two_pow_add_gt hjτ] at h0
      exact eq_of_add_eq_zero_two h0
    · have h0 := fire_input e c kind lam A hS (.ad, j) hs c0 hc0
      simp only [inputEqs, hjτ, if_false, List.mem_singleton, forall_eq] at h0
      rw [Y _ hs] at h0
      have hb : c0.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hc0 (Nat.pow_le_pow_right (by norm_num) (by have := c.ha; omega)))
      show cellAt e om A (2 ^ τ + c0) 0 (recCell (.ad, j)) = _
      rw [h0, hb]
      simp

/-- **(B5) dummy records** (`app:affine-embedding`: On dummy lanes `x ≥ T + N_A` check every semantic REC bit `0`). -/
theorem cl_dummy : ∀ x, 2 ^ τ + 2 ^ a ≤ x → x < 2 ^ (τ + 1) → ∀ s : RecSlot, s.Active (dims M τ) →
    (traceOf e om K L M.w (2 * l.k - 1) A).src x s.1 s.2 = 0 := by
  intro x hx1 hx2 s hs
  have h2 : 2 ^ (τ + 1) = 2 * 2 ^ τ := two_pow_succ' τ
  set y := x - 2 ^ τ with hy
  have hy1 : 2 ^ a ≤ y := by omega
  have hy2 : y < 2 ^ τ := by omega
  have hy0 : y ≠ 0 := by have := Nat.two_pow_pos a; omega
  have hla : a ≤ Nat.log 2 y := Nat.le_log_of_pow_le (by norm_num) hy1
  have hlτ : Nat.log 2 y < τ := Nat.log_lt_of_lt_pow hy0 hy2
  have hp1 := Nat.pow_log_le_self 2 hy0
  have hp2 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) y
  have hi : Nat.log 2 y - a < τ - a := by omega
  have hai : a + (Nat.log 2 y - a) = Nat.log 2 y := by omega
  have hm := mem_b5_dummy l om K L M kind τ a lam s (mem_recSlotList_of_active _ s hs) _ hi
  have hok := hostOk (c.rOk s hs) 7 (by norm_num)
  have g := guardOk_of l om dt _ _ _ _ c.hq (c.lt_kk _ (rk_block τ (a + (Nat.log 2 y - a))))
    (c.lt_kk _ (rk_dummyV τ (a + (Nat.log 2 y - a)) (by omega))) (Nat.two_pow_pos _) hok
  have hlane := (lane_dummy x (a + (Nat.log 2 y - a)) τ (by omega) hx2).mpr (by
    rw [hai]; rw [Nat.succ_eq_add_one] at hp2; omega)
  have h0 := fire e om A hS hm g x (c.lt_kk _ hx2) hlane
  rw [evaluate_local e om A x 0 _ _ (c.inR hx2 (Nat.two_pow_pos _) hok) (c.inR hx2 (Nat.two_pow_pos _) (c.rOk s hs))]
    at h0
  exact h0

end Clauses2

/-- **(P) from routing soundness** (`thm:embedding` SOUNDNESS: one permutation of whole records, no distinctness). -/
theorem cl_perm {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) (hInd : Independent l.m e)
    {om dt K L τ a : ℕ} {M : ACSP.Ram} (c : Ctx l om dt K L τ a M) (A : F → F) (hR : LocalRouting l e A) :
    ∃ π : Equiv.Perm (Fin (2 ^ (τ + 1))), ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) →
      (traceOf e om K L M.w (2 * l.k - 1) A).dst (π x) s.1 s.2 = (traceOf e om K L M.w (2 * l.k - 1) A).src x s.1 s.2 := by
  obtain ⟨π, hπ⟩ := Routing.contract.soundness l e hInd A hR
  let eqv : Lane l.k ≃ Fin (2 ^ (τ + 1)) := BitVec.equivFin.toEquiv.trans (finCongr (by rw [c.hk]))
  refine ⟨eqv.symm.trans (π.trans eqv), fun x s hs => ?_⟩
  have hc := c.rOk s hs
  have hcol : (recCell s).col om < l.C := by rw [Layout.C, c.hq]; exact Cell.col_lt hc
  have h := hπ (eqv.symm x) ⟨(recCell s).col om, hcol⟩
  unfold dataValue at h
  exact h

end NearCubicGates.Adapters.RAMACSP

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Routing

/-- **E4 (generic): a table satisfying the emitted equations is an event trace** (`thm:embedding` Full embedding equivalence,
first half; `def:event-trace`). -/
theorem holds_of_table {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) (hInd : Independent l.m e)
    {om dt K L τ a : ℕ} {M : ACSP.Ram} (c : Ctx l om dt K L τ a M) (kind : Fin M.ops → AluOp)
    (lam : ℕ → Routing.Expr F) (A : F → F)
    (hS : ∀ v, ∀ t ∈ machineItems l om K L M kind τ a lam, patternHolds t.1 v →
      Routing.evaluate l e A (cubeEval l.m e v) t.2.poly = 0)
    (hR : LocalRouting l e A) (xbar : List Bool) (hNA : xbar.length / M.w = 2 ^ a)
    (hlam : ∀ j < τ, ∀ u < 2 ^ l.m, Routing.evaluate l e A (maskEval l.m e u) (lam j).poly = if u.testBit j then 1 else 0)
    (hva : ∀ c0 < 2 ^ a, ∀ b < M.w,
      cellAt e om A (2 ^ τ + c0) 0 (recCell (.va, b)) = if xbar.getD (c0 * M.w + b) false then 1 else 0) :
    Holds M kind τ xbar (traceOf e om K L M.w (2 * l.k - 1) A) := by
  unfold Holds
  dsimp only
  rw [hNA]
  exact ⟨cl_srcBit e c A hR, cl_dstBit e c A hR, cl_timeBit e c kind lam A hS, cl_sortBit e c kind lam A hS,
    cl_timeEq e c kind lam A hS, cl_first e c kind lam A hS, cl_copy e c kind lam A hS, cl_out e c kind lam A hS,
    cl_acc e c kind lam A hS, cl_sortEq e c kind lam A hS, cl_sentinel e c kind lam A hS,
    cl_prevCopy e c kind lam A hS, fun c0 hc0 => cl_input e c kind lam A hS xbar hlam hva c0 hc0,
    cl_dummy e c kind lam A hS, cl_perm e hInd c A hR⟩

end NearCubicGates.Adapters.RAMACSP
