import SourceAdapters.RAMACSP.CheckDegree
import SourceAdapters.RAMTrace.Catalog

/-!
# Every read of the emitted constraint is a bank offset

Paper: `app:affine-embedding`, "Neighbors" and "Placement". Each read is
a same-vertex translation in the 16C local bank, a previous-time copy,
a previous-sorted copy, or a routing edge. Active catalog cells satisfy
`tag < Ftags ≤ 2^d`, `bit < w`, `role < 8`, `area < 2`.
The equation trees read only the active slots of `def:event-trace`.

`itemsReadInBank`: every read of every item of `ownItems` lies in `Routing.globalBank` — the hypothesis of the
circuit correctness theorem `Routing.Circuit.compileTerms_correct`. With `CheckDegree.degreeBound` this gives the degree bound:
`degreeBound_own : IrreducibleChoice irrPoly → DegreeBound V irrPoly (ownCons V irrPoly)`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMTrace

theorem mem_timeEqList (d : Dims) : ∀ q ∈ timeEqList d, q.Active d := by
  simp only [timeEqList, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap, List.mem_range,
    List.forall_mem_cons, TEq.Active]
  repeat' apply And.intro
  all_goals (try intros) ; (try trivial) ; (try omega)

theorem mem_sortEqList (d : Dims) : ∀ q ∈ sortEqList d, q.Active d := by
  simp only [sortEqList, List.forall_mem_append, List.forall_mem_map, List.mem_range, List.forall_mem_cons,
    SEq.Active]
  repeat' apply And.intro
  all_goals (try intros) ; (try trivial)

theorem mem_timeSlotList (d : Dims) : ∀ s ∈ timeSlotList d, s.Active d := by
  simp only [timeSlotList, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap, List.mem_range,
    List.forall_mem_cons, TSlot.Active]
  repeat' apply And.intro
  all_goals (try intros) ; (try trivial) ; (try omega)

theorem mem_copyList (d : Dims) : ∀ c ∈ copyList d, c.Active d := by
  simp only [copyList, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap, List.mem_range,
    TCopy.Active]
  repeat' apply And.intro
  all_goals (try intros) ; (try trivial) ; (try omega)

theorem mem_sortSlotList (d : Dims) : ∀ s ∈ sortSlotList d, s.Active d := by
  intro s hs
  simp only [sortSlotList, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((((((h | h) | h) | h) | h | h) | h) | h | h)
  · obtain ⟨f, hf, j, hj, rfl⟩ := h
    refine ⟨?_, hj⟩
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨l, hl, rfl⟩ := h; exact hl
  · subst h; trivial
  · obtain ⟨l, hl, rfl⟩ := h; show l ≤ d.w; omega
  · subst h; trivial
  · subst h; trivial
  · obtain ⟨j, hj, rfl⟩ := h; exact hj
  · subst h; trivial
  · subst h; trivial

theorem mem_recSlotList (d : Dims) : ∀ s ∈ recSlotList d, s.Active d := by
  simp only [recSlotList, recFields, List.forall_mem_flatMap, List.forall_mem_map, List.mem_range, List.forall_mem_cons,
    RecSlot.Active]
  repeat' apply And.intro
  all_goals (try intros) ; (try trivial)

/-! ## Catalog cells are in range; the bank contains every read -/

/-- A catalog cell inside the column (`bit < 2^ω`, `tag < 2^d`), role and area ranges. -/
def Cell.Ok (om dt : ℕ) (c : Cell) : Prop := c.bit < 2 ^ om ∧ c.tag < 2 ^ dt ∧ c.role < 8 ∧ c.area < 2

theorem Cell.col_lt {om dt : ℕ} {c : Cell} (h : c.Ok om dt) : c.col om < 2 ^ (dt + om) := by
  unfold Cell.col
  obtain ⟨h1, h2, -, -⟩ := h
  have h3 : 2 ^ om * (c.tag + 1) ≤ 2 ^ om * 2 ^ dt := Nat.mul_le_mul_left _ h2
  have e : 2 ^ (dt + om) = 2 ^ om * 2 ^ dt := by rw [pow_add, Nat.mul_comm]
  rw [e]
  have e2 : 2 ^ om * (c.tag + 1) = 2 ^ om * c.tag + 2 ^ om := by ring
  omega

theorem local_mem_bank (l : Routing.Layout) (c r a : ℕ) (hc : c < l.C) (hr : r < 8) (ha : a < 2) :
    Routing.cellMask l 0 0 c r a ∈ Routing.globalBank l := by
  unfold Routing.globalBank
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  rw [List.mem_map]
  refine ⟨c + l.C * (r + 8 * a), List.mem_range.mpr ?_, ?_⟩
  · have h1 : l.C * (r + 8 * a) ≤ l.C * 15 := Nat.mul_le_mul_left _ (by omega)
    omega
  · unfold Routing.cellMask Routing.Layout.C
    rw [pow_add]; ring

theorem localOffset_mem (l : Routing.Layout) (om dt : ℕ) (hq : l.q = dt + om) (h c : Cell)
    (hh : h.Ok om dt) (hc : c.Ok om dt) : localOffset l om h c ∈ Routing.globalBank l := by
  unfold localOffset
  apply local_mem_bank
  · rw [Routing.Layout.C, hq]; exact Nat.xor_lt_two_pow (Cell.col_lt hh) (Cell.col_lt hc)
  · exact Nat.xor_lt_two_pow (n := 3) hh.2.2.1 hc.2.2.1
  · exact Nat.xor_lt_two_pow (n := 1) hh.2.2.2 hc.2.2.2

theorem pred5_mem (l : Routing.Layout) (t : ℕ) (ht : t < l.k) :
    Routing.laneCarry t ^^^ Routing.eta l 5 ^^^ Routing.eta l 1 ∈ Routing.globalBank l := by
  unfold Routing.globalBank
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))

theorem pred6_mem (l : Routing.Layout) (t : ℕ) (ht : t < l.k) :
    Routing.laneCarry t ^^^ Routing.areaMask l ^^^ Routing.eta l 6 ∈ Routing.globalBank l := by
  unfold Routing.globalBank
  exact List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

section Cells

variable (d : Dims) (K L om dt : ℕ) (hK : d.K = K) (hL : d.L = L) (hw : d.w = 2 ^ om) (hτ : d.τ < d.w)
  (hβ : d.β ≤ d.τ) (hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt)
include hK hL hw hτ hβ hF

theorem tCell_ok (s : TSlot) (hs : s.Active d) : (tCell K L s).Ok om dt := by
  cases s <;> simp only [tCell, Cell.Ok, blockBase, TSlot.Active] at hs ⊢ <;> omega

theorem recCell_ok (s : RecSlot) (hs : s.Active d) : (recCell s).Ok om dt := by
  obtain ⟨f, j⟩ := s
  cases f <;> simp only [recCell, Cell.Ok, RecField.tag, RecSlot.Active, RecField.width] at hs ⊢ <;> omega

omit hβ in
theorem sCell_ok (s : SSlot) (hs : s.Active d) : (sCell d.w s).Ok om dt := by
  have hw0 : 0 < d.w := by omega
  cases s with
  | prev f j =>
    obtain ⟨-, hj⟩ := hs
    have hjw : j < d.w := by cases f <;> simp only [RecField.width] at hj <;> omega
    cases f <;> simp only [sCell, Cell.Ok, RecField.tag] <;> omega
  | ob l =>
    have hl : l < d.w + d.τ + 2 := hs
    have h3 : l / d.w < 3 := (Nat.div_lt_iff_lt_mul hw0).mpr (by omega)
    have h4 : l % d.w < d.w := Nat.mod_lt _ hw0
    simp only [sCell, Cell.Ok]; omega
  | so l =>
    have hl : l ≤ d.w := hs
    simp only [sCell, Cell.Ok]
    split <;> simp only <;> omega
  | ev j =>
    have hj : j < d.w := hs
    simp only [sCell, Cell.Ok]; omega
  | _ => simp only [sCell, Cell.Ok]; omega

theorem tHost_ok (q : TEq) (hq : q.Active d) : (⟨tTag K L q, tBit q, 2, 1⟩ : Cell).Ok om dt := by
  cases q <;> simp only [Cell.Ok, tTag, tBit, TEq.Active] at hq ⊢ <;> omega

theorem dstCell_ok (cp : TCopy) (hcp : cp.Active d) : (dstCell K L cp).Ok om dt := by
  cases cp <;> simp only [dstCell, TCopy.dst] <;>
    first
    | exact tCell_ok d K L om dt hK hL hw hτ hβ hF _ hcp
    | exact recCell_ok d K L om dt hK hL hw hτ hβ hF _ hcp

omit hβ in
theorem sHost_ok (q : SEq) (hq : q.Active d) : (⟨sTag d.w q, sBit d.w q, 2, 1⟩ : Cell).Ok om dt := by
  have hw0 : 0 < d.w := by omega
  cases q with
  | borrow l =>
    have hl : l < d.w + d.τ + 2 := hq
    have h3 : l / d.w < 3 := (Nat.div_lt_iff_lt_mul hw0).mpr (by omega)
    have h4 : l % d.w < d.w := Nat.mod_lt _ hw0
    simp only [Cell.Ok, sTag, sBit]; omega
  | _ => simp only [Cell.Ok, sTag, sBit, SEq.Active] at hq ⊢; omega

end Cells

theorem tCell_role (K L : ℕ) (s : TSlot) : (tCell K L s).role ≤ 1 ∧ (tCell K L s).area = 1 := by
  cases s <;> simp [tCell]

theorem sCell_role (w : ℕ) (s : SSlot) : (sCell w s).role ≤ 1 ∧ (sCell w s).area = 1 := by
  cases s with
  | so l => simp only [sCell]; split <;> simp
  | _ => simp [sCell]

theorem eSet_reads (M : Ram) (τ : ℕ) (Q : Instr M.w M.k M.ops → Bool) :
    ∀ v ∈ (eSet M Q).vars, TVar.Active (dims M τ) v :=
  allVars_sumCode (TVar.Active (dims M τ)) _ M.code 0 (fun p I _ hp => by
    split_ifs
    · simp only [tv, allVars_var]; show p < M.code.length; omega
    · exact allVars_zero _)

theorem outE_reads (M : Ram) (τ : ℕ) : ∀ v ∈ (outE M).vars, TVar.Active (dims M τ) v := eSet_reads M τ _

theorem accE_reads (M : Ram) (τ : ℕ) : ∀ v ∈ (accE M).vars, TVar.Active (dims M τ) v := by
  intro v hv
  simp only [accE, Expr.vars, List.append_nil] at hv
  exact eSet_reads M τ _ v hv

section Reads

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem toRouting_reads {ι : Type} (bank : List ℕ) (rd : ι → ℕ) (E : RAMTrace.Expr ι)
    (h : ∀ v ∈ E.vars, rd v ∈ bank) : Routing.Circuit.ReadsIn bank (toRouting (F := F) rd E) := by
  induction E with
  | zero => trivial
  | one => trivial
  | var i => exact h i (by simp [Expr.vars])
  | add a b iha ihb =>
    exact ⟨iha fun v hv => h v (by simp [Expr.vars, hv]), ihb fun v hv => h v (by simp [Expr.vars, hv])⟩
  | mul a b iha ihb =>
    exact ⟨iha fun v hv => h v (by simp [Expr.vars, hv]), ihb fun v hv => h v (by simp [Expr.vars, hv])⟩

omit [CharP F 2] in
theorem inputEqs_reads (bank : List ℕ) (τ : ℕ) (lam : ℕ → Routing.Expr F)
    (hlam : ∀ j, Routing.Circuit.ReadsIn bank (lam j)) (Y : Routing.Expr F) (hY : Routing.Circuit.ReadsIn bank Y)
    (s : RecSlot) : ∀ E ∈ inputEqs τ lam Y s, Routing.Circuit.ReadsIn bank E := by
  intro E hE
  obtain ⟨f, j⟩ := s
  cases f with
  | va => simp [inputEqs] at hE
  | ad =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE
    split
    · exact ⟨hY, hlam j⟩
    · exact hY
  | ts | ph | st =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE; exact hY
  | act | rgn =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE; exact ⟨hY, trivial⟩

theorem rb_mem (l : Routing.Layout) (b : ℕ) (hb : b ∈ Routing.routingBank l) : b ∈ Routing.globalBank l := by
  unfold Routing.globalBank
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hb))

omit [Field F] [CharP F 2] in
theorem routingItem_reads (l : Routing.Layout) (it : Routing.RoutingItem) (hit : it ∈ Routing.routingItems l) :
    Routing.Circuit.ReadsIn (Routing.globalBank l) (it.expr (F := F) l) := by
  have h0 : (0 : ℕ) ∈ Routing.routingBank l := by unfold Routing.routingBank; simp
  have hS : ∀ j < Routing.switchCount l.k, Routing.stageDelta l j ∈ Routing.routingBank l := fun j hj => by
    unfold Routing.routingBank
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))))
  have hX : ∀ j < Routing.switchCount l.k,
      Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j ∈ Routing.routingBank l := fun j hj => by
    unfold Routing.routingBank
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))
  have hR : ∀ b ∈ [Routing.eta l 1, Routing.eta l 2, Routing.eta l 3 ^^^ Routing.eta l 1,
      Routing.eta l 4 ^^^ Routing.eta l 1], b ∈ Routing.routingBank l := fun b hb => by
    unfold Routing.routingBank
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))
  have hP : ∀ e < l.k, Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ e ∈ Routing.routingBank l := fun e he => by
    unfold Routing.routingBank
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩))
  have hC : ∀ t < l.q, Routing.columnCarry l t ∈ Routing.routingBank l := fun t ht => by
    unfold Routing.routingBank
    exact List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  simp only [Routing.routingItems, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hit
  rcases hit with ⟨j, hj, hit⟩ | ⟨j, hj, rfl⟩
  · have hd : Routing.dimension l.k j < l.k := by
      unfold Routing.switchCount at hj
      unfold Routing.dimension
      rcases le_total j (2 * l.k - 2 - j) with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    rcases hit with (rfl | rfl | rfl) | ⟨t, ht, rfl⟩
    · exact ⟨⟨rb_mem l _ h0, rb_mem l _ (hS j hj)⟩, rb_mem l _ (hR _ (by simp)),
        rb_mem l _ (hS j hj), rb_mem l _ (hX j hj)⟩
    · exact ⟨rb_mem l _ (hR _ (by simp)), rb_mem l _ (hR _ (by simp))⟩
    · exact ⟨rb_mem l _ (hR _ (by simp)), rb_mem l _ (hP _ hd)⟩
    · exact ⟨rb_mem l _ h0, rb_mem l _ (hC t ht)⟩
  · exact ⟨rb_mem l _ (hR _ (by simp)), rb_mem l _ (hR _ (by simp))⟩

end Reads

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ShortPCP

/-- **Every read of every item is a bank offset** (`app:affine-embedding` access census). -/
theorem itemsReadInBank (V : Verifier) : ItemsReadInBank V := by
  intro F _ _ r hn hnt lam hlam t ht
  have ht1 : 1 ≤ r.2 := by omega
  have hK : (dims (ownRam V r) (tau V r.2)).K = regCount V := rfl
  have hL : (dims (ownRam V r) (tau V r.2)).L = codeLen V := mnCode_length V _ _ _ _
  have hw : (dims (ownRam V r) (tau V r.2)).w = 2 ^ wordExp V r.2 := wordW_eq V r.2
  have hτ : (dims (ownRam V r) (tau V r.2)).τ < (dims (ownRam V r) (tau V r.2)).w := by
    simp only [dims]; exact tau_lt_wordW V r.2 ht1
  have hβ : (dims (ownRam V r) (tau V r.2)).β ≤ (dims (ownRam V r) (tau V r.2)).τ := by
    simp only [dims]; exact Nat.sub_le _ _
  have hF : 32 + 3 * regCount V + 2 * codeLen V ≤ 2 ^ tagExp V := by
    have := ftags_le V; unfold ftags at this; exact this
  have hq : (ownLayout V r.2).q = tagExp V + wordExp V r.2 := by simp only [ownLayout, colExp]
  have hk : (ownLayout V r.2).k = tau V r.2 + 1 := by simp only [ownLayout, laneExp]
  have hw1 : 1 ≤ (ownRam V r).w := by
    have : (dims (ownRam V r) (tau V r.2)).w = (ownRam V r).w := by simp only [dims]
    omega
  have hom : 0 < 2 ^ wordExp V r.2 := Nat.two_pow_pos _
  have mem := localOffset_mem (ownLayout V r.2) (wordExp V r.2) (tagExp V) hq
  have tok := tCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have rok := recCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have sok := sCell_ok _ _ _ _ _ hK hL hw hτ hF
  have thok := tHost_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have shok := sHost_ok _ _ _ _ _ hK hL hw hτ hF
  have dok := dstCell_ok _ _ _ _ _ hK hL hw hτ hβ hF
  have role3 : ∀ c : Cell, c.Ok (wordExp V r.2) (tagExp V) → c.role ≤ 1 → ∀ rr, rr < 8 →
      (⟨c.tag, c.bit, rr, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
    fun c hc _ rr hrr => ⟨hc.1, hc.2.1, hrr, show (1 : ℕ) < 2 by norm_num⟩
  rcases List.mem_append.mp ht with hr | hm
  · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hr
    exact routingItem_reads _ it hit
  simp only [machineItems, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_range,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((((h | h) | h) | h) | h) | h) | h) | h
  · -- (T1)–(T10)
    obtain ⟨q, hq', rfl⟩ := h
    have hqa := mem_timeEqList _ q hq'
    refine toRouting_reads _ _ _ fun v hv => ?_
    have hva := timeEq_reads_active _ _ _ hw1 q hqa v hv
    cases v with
    | inl s => exact mem _ _ (thok q hqa) (tok s hva)
    | inr s => exact mem _ _ (thok q hqa) (rok s hva)
  · -- Booleanity, time
    obtain ⟨s, hs, rfl⟩ := h
    have hc := tok s (mem_timeSlotList _ s hs)
    have hh := role3 _ hc (tCell_role _ _ s).1 ((tCell (regCount V) (codeLen V) s).role + 3)
      (by have := (tCell_role (regCount V) (codeLen V) s).1; omega)
    exact ⟨mem _ _ hh hc, mem _ _ hh hc⟩
  · -- (B1), (B2) copies
    obtain ⟨cp, hcp, h⟩ := h
    have hdc := dok cp (mem_copyList _ cp hcp)
    have hh : (⟨(dstCell (regCount V) (codeLen V) cp).tag, (dstCell (regCount V) (codeLen V) cp).bit, 5, 1⟩ :
        Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hdc.1, hdc.2.1, show (5 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with rfl | ⟨u, hu, rfl⟩
    · exact mem _ _ hh hdc
    · exact ⟨mem _ _ hh hdc, pred5_mem _ u (by rw [hk]; omega)⟩
  · -- (B2) e(Out), (B3) e(Acc)
    have hh : (⟨7, 0, 7, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hom, show 7 < 2 ^ tagExp V by omega, show (7 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with ⟨b, -, rfl⟩ | rfl
    · refine toRouting_reads _ _ _ fun v hv => ?_
      have hva := outE_reads _ (tau V r.2) v hv
      cases v with
      | inl s => exact mem _ _ hh (tok s hva)
      | inr s => exact mem _ _ hh (rok s hva)
    · refine toRouting_reads _ _ _ fun v hv => ?_
      have hva := accE_reads _ (tau V r.2) v hv
      cases v with
      | inl s => exact mem _ _ hh (tok s hva)
      | inr s => exact mem _ _ hh (rok s hva)
  · -- (S1)–(S5)
    obtain ⟨q, hq', rfl⟩ := h
    have hqa := mem_sortEqList _ q hq'
    refine toRouting_reads _ _ _ fun v hv => ?_
    have hva := sortEq_reads_active _ hw1 q hqa v hv
    cases v with
    | inl s => exact mem _ _ (shok q hqa) (sok s hva)
    | inr s => exact mem _ _ (shok q hqa) (rok s hva)
  · -- Booleanity, sorted
    obtain ⟨s, hs, rfl⟩ := h
    have hc := sok s (mem_sortSlotList _ s hs)
    have hh := role3 _ hc (sCell_role _ s).1 ((sCell (ownRam V r).w s).role + 3)
      (by have := (sCell_role (ownRam V r).w s).1; omega)
    exact ⟨mem _ _ hh hc, mem _ _ hh hc⟩
  · -- (B4)
    obtain ⟨s, hs, h⟩ := h
    obtain ⟨f, hf', j, hj', rfl⟩ := hs
    have hpa : (SSlot.prev f j).Active (dims (ownRam V r) (tau V r.2)) := by
      refine ⟨?_, hj'⟩
      rcases hf' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := sok _ hpa
    have hh : (⟨(sCell (ownRam V r).w (.prev f j)).tag, (sCell (ownRam V r).w (.prev f j)).bit, 6, 1⟩ : Cell).Ok
        (wordExp V r.2) (tagExp V) := ⟨hc.1, hc.2.1, show (6 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with rfl | ⟨u, hu, rfl⟩
    · exact ⟨mem _ _ hh hc, trivial⟩
    · exact ⟨mem _ _ hh hc, pred6_mem _ u hu⟩
  · -- (B5)
    obtain ⟨s, hs, h⟩ := h
    have hc := rok s (mem_recSlotList _ s hs)
    have hh : (⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).Ok (wordExp V r.2) (tagExp V) :=
      ⟨hc.1, hc.2.1, show (7 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
    rcases h with ⟨E, hE, rfl⟩ | ⟨u, -, rfl⟩
    · exact inputEqs_reads _ _ lam hlam (Routing.Expr.read (some (localOffset (ownLayout V r.2) (wordExp V r.2)
        ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ (recCell s)))) (mem _ _ hh hc) s E hE
    · exact mem _ _ hh hc

/-- **The weighted-degree bound** (`lem:acsp-degree`: `4·wdeg P ≤ 2^f` for the emitted constraint). -/
theorem degreeBound_own (V : Verifier) (irrPoly : ℕ → Polynomial (ZMod 2))
    (hI : Published.Shoup.IrreducibleChoice irrPoly) : DegreeBound V irrPoly (ownCons V irrPoly) :=
  degreeBound V irrPoly (itemsReadInBank V) hI

end NearCubicGates.Adapters.RAMACSP
