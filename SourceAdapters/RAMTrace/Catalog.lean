import SourceAdapters.RAMTrace.Defs

/-!
# The equation catalog reads only slots of `def:event-trace`

the active-slot convention in `def:event-trace` and `app:affine-embedding` (Every read is within the SAME lane and stage): every active equation of (T1)–(T10) reads
only active slots of its time row and routed record (`timeEq_reads_active`), and every active equation of
(S1)–(S5) only active slots of its sorted vertex (`sortEq_reads_active`). This is what makes (G) on the slots of
the slot catalog of `def:event-trace` enough to evaluate the equations bitwise (`RAMTrace.Transfer`), and what the constraint circuit's
emission needs (every read is a catalog slot).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr

/-- Every variable of `e` satisfies `P`. -/
def AllVars {ι : Type} (P : ι → Prop) (e : Expr ι) : Prop := ∀ v ∈ e.vars, P v

section AllVars

variable {ι : Type} (P : ι → Prop)

@[simp] theorem allVars_zero : AllVars P (Expr.zero : Expr ι) := by simp [AllVars, Expr.vars]
@[simp] theorem allVars_one : AllVars P (Expr.one : Expr ι) := by simp [AllVars, Expr.vars]
@[simp] theorem allVars_var (i : ι) : AllVars P (Expr.var i) ↔ P i := by simp [AllVars, Expr.vars]
@[simp] theorem allVars_add (a b : Expr ι) : AllVars P (Expr.add a b) ↔ AllVars P a ∧ AllVars P b := by
  simp only [AllVars, Expr.vars, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩
@[simp] theorem allVars_mul (a b : Expr ι) : AllVars P (Expr.mul a b) ↔ AllVars P a ∧ AllVars P b := by
  simp only [AllVars, Expr.vars, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩
@[simp] theorem allVars_bit (b : Bool) : AllVars P (Expr.bit b : Expr ι) := by
  cases b <;> simp [Expr.bit]
@[simp] theorem allVars_compl (a : Expr ι) : AllVars P (Expr.compl a) ↔ AllVars P a := by
  simp [Expr.compl]
@[simp] theorem allVars_maj (a b c : Expr ι) :
    AllVars P (Expr.maj a b c) ↔ AllVars P a ∧ AllVars P b ∧ AllVars P c := by
  simp only [Expr.maj, allVars_add, allVars_mul]; tauto

theorem allVars_sum (l : List (Expr ι)) (h : ∀ e ∈ l, AllVars P e) : AllVars P (Expr.sum l) := by
  induction l with
  | nil => simp [Expr.sum]
  | cons a l ih =>
    simp only [Expr.sum, allVars_add]
    exact ⟨h a (by simp), ih fun e he => h e (by simp [he])⟩

theorem allVars_sumCode {α : Type} (f : ℕ → α → Expr ι) :
    ∀ (l : List α) (p0 : ℕ), (∀ p I, p0 ≤ p → p < p0 + l.length → AllVars P (f p I)) →
      AllVars P (sumCode f p0 l)
  | [], _, _ => by simp [sumCode]
  | I :: l, p0, h => by
    simp only [sumCode, allVars_add]
    exact ⟨h p0 I le_rfl (by simp), allVars_sumCode f l (p0 + 1) fun p I h1 h2 => h p I (by omega)
      (by simp at h2 ⊢; omega)⟩

end AllVars

/-- **(T1)–(T10) read only slots of `def:event-trace`** (for `w ≥ 1`). -/
theorem timeEq_reads_active (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (hw : 1 ≤ M.w) (q : TEq)
    (hq : q.Active (dims M τ)) : ∀ v ∈ (timeEq M kind τ q).vars, v.Active (dims M τ) := by
  have hE : ∀ (Q : Instr M.w M.k M.ops → Bool), AllVars (TVar.Active (dims M τ)) (eSet M Q) := by
    intro Q
    apply allVars_sumCode
    intro p I _ hp
    split_ifs
    · simp only [tv, allVars_var]; show p < M.code.length; simpa using hp
    · simp
  have hD : ∀ (s : Instr M.w M.k M.ops → Expr TVar), (∀ I, AllVars (TVar.Active (dims M τ)) (s I)) →
      AllVars (TVar.Active (dims M τ)) (eDot M s) := by
    intro s hs
    apply allVars_sumCode
    intro p I _ hp
    simp only [tv, allVars_mul, allVars_var]
    exact ⟨by show p < M.code.length; simpa using hp, hs I⟩
  have hop : ∀ (x : Operand M.w M.k) (j : ℕ), j < M.w → AllVars (TVar.Active (dims M τ)) (opnd M x j) := by
    intro x j hj
    cases x with
    | reg r => simp only [opnd, tv, allVars_var]; exact ⟨r.isLt, hj⟩
    | pc => simp only [opnd, tv, allVars_var]; exact hj
    | const c => simp [opnd]
  have hX : ∀ I j, j < M.w → AllVars (TVar.Active (dims M τ)) (srcX M I j) := by
    intro I j hj
    cases I <;> simp only [srcX, allVars_zero] <;>
      first | exact hop _ j hj | (simp only [tv, allVars_var]; exact ⟨Fin.isLt _, hj⟩)
  have hY : ∀ I j, j < M.w → AllVars (TVar.Active (dims M τ)) (srcY M I j) := by
    intro I j hj
    cases I <;> simp only [srcY, allVars_zero] <;> exact hop _ j hj
  have hXF : ∀ I, AllVars (TVar.Active (dims M τ)) (srcXF M I) := by
    intro I
    cases I <;> simp only [srcXF, allVars_zero]
    simp only [tv, allVars_var]; exact Fin.isLt _
  have hP : ∀ p I j, p < M.code.length → j < M.w → AllVars (TVar.Active (dims M τ)) (pcTerm M p I j) := by
    intro p I j hp hj
    have he : TVar.Active (dims M τ) (.inl (.e p)) := hp
    have hoz : TVar.Active (dims M τ) (.inl (.OZ (M.w - 1))) := by show M.w - 1 < M.w; omega
    cases I <;> simp [pcTerm, tv, he, hoz]
  intro v hv
  revert v
  show AllVars (TVar.Active (dims M τ)) (timeEq M kind τ q)
  have hL := M.codeNonempty
  cases q with
  | flag r j => simp [timeEq, tv]; exact ⟨hq.1, hq⟩
  | decFirst =>
    simp only [timeEq, tv, allVars_add, allVars_var]
    exact ⟨show 0 < M.code.length by omega, show 0 < M.code.length by omega⟩
  | decRec p =>
    obtain ⟨h1, h2⟩ := hq
    simp only [timeEq, tv, allVars_add, allVars_var]
    have h2' : p < M.code.length := h2
    exact ⟨⟨h2, show p - 1 < M.code.length by omega⟩, h2⟩
  | decExcl p =>
    obtain ⟨h1, h2⟩ := hq
    simp only [timeEq, tv, allVars_mul, allVars_var]
    have h2' : p < M.code.length := h2
    exact ⟨h2, show p - 1 < M.code.length by omega⟩
  | decLast =>
    simp only [timeEq, tv, allVars_add, allVars_var, allVars_one]
    exact ⟨show M.code.length - 1 < M.code.length by omega, trivial⟩
  | decPc j =>
    simp only [timeEq, tv, allVars_add, allVars_var]
    refine ⟨hq, allVars_sumCode _ _ _ _ fun p I _ hp => ?_⟩
    split_ifs
    · simp only [allVars_var]; show p < M.code.length; simpa using hp
    · simp
  | opX j => simp only [timeEq, tv, allVars_add, allVars_var]; exact ⟨hq, hD _ fun I => hX I j hq⟩
  | opY j => simp only [timeEq, tv, allVars_add, allVars_var]; exact ⟨hq, hD _ fun I => hY I j hq⟩
  | opXF => simp only [timeEq, tv, allVars_add, allVars_var]; exact ⟨trivial, hD _ hXF⟩
  | sumAD j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, caE, allVars_add, allVars_var]
    refine ⟨⟨⟨hj, hj⟩, hj⟩, ?_⟩
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < M.w; omega
  | carry j =>
    have hj : j + 1 < M.w := hq
    simp only [timeEq, tv, caE, allVars_add, allVars_var, allVars_maj]
    refine ⟨hj, by show j < M.w; omega, by show j < M.w; omega, ?_⟩
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < M.w; omega
  | sumSB j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, boE, allVars_add, allVars_var]
    refine ⟨⟨⟨hj, hj⟩, hj⟩, ?_⟩
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j < M.w; omega
  | borrow j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, boE, allVars_add, allVars_var, allVars_mul, allVars_compl]
    have hb : AllVars (TVar.Active (dims M τ)) (if j = 0 then zero else tv (.BO (j - 1))) := by
      rcases j with _ | j
      · simp
      · simp only [Nat.add_one_ne_zero, if_false, tv, allVars_var]; show j < M.w; omega
    exact ⟨hj, ⟨hj, hj, hb⟩, hj, hb⟩
  | andAN j => have hj : j < M.w := hq; simp only [timeEq, tv, allVars_add, allVars_var, allVars_mul]; exact ⟨hj, hj, hj⟩
  | ozFirst =>
    simp only [timeEq, tv, allVars_add, allVars_var]
    exact ⟨by show 0 < M.w; omega, by show 0 < M.w; omega⟩
  | ozRec j =>
    obtain ⟨h1, h2⟩ := hq
    simp only [timeEq, tv, allVars_add, allVars_var, allVars_mul]
    have h2' : j < M.w := h2
    have h3 : TVar.Active (dims M τ) (.inl (.OZ (j - 1))) := by show j - 1 < M.w; omega
    exact ⟨h2, ⟨h3, h2⟩, h3, h2⟩
  | gt =>
    simp only [timeEq, tv, allVars_add, allVars_var, allVars_mul, allVars_compl]
    exact ⟨trivial, by show M.w - 1 < M.w; omega, by show M.w - 1 < M.w; omega⟩
  | rfFlag j => simp only [timeEq, tv, allVars_mul, allVars_var]; exact ⟨trivial, hq⟩
  | store j => simp only [timeEq, tv, allVars_mul, allVars_add, allVars_var]; exact ⟨hE _, hq, hq⟩
  | res j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, allVars_add, allVars_var]
    refine ⟨hj, allVars_sum _ _ ?_⟩
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [allVars_mul, allVars_var]; exact ⟨hE _, hj⟩
    · simp only [allVars_mul, allVars_var]; exact ⟨hE _, hj⟩
    · simp only [allVars_mul, allVars_var]; exact ⟨hE _, hj⟩
    · simp only [allVars_mul, cmpE]
      refine ⟨hE _, ?_⟩
      split_ifs <;> simp only [tv, allVars_add, allVars_var] <;>
        first | exact ⟨by show M.w - 1 < M.w; omega, trivial⟩ | trivial
    · simp only [allVars_mul, allVars_var]; exact ⟨hE _, hj⟩
    · simp only [allVars_mul, allVars_var]; exact ⟨hE _, hj⟩
    · split_ifs
      · simp only [allVars_mul, allVars_var]; exact ⟨hE _, trivial⟩
      · simp
  | resF => simp only [timeEq, tv, allVars_add, allVars_mul, allVars_var]; exact ⟨trivial, hE _, trivial⟩
  | reg r j =>
    simp only [timeEq, tv, allVars_add, allVars_mul, allVars_var, allVars_compl]
    exact ⟨hq, ⟨hE _, hq.2⟩, hE _, hq⟩
  | regF r =>
    simp only [timeEq, tv, allVars_add, allVars_mul, allVars_var, allVars_compl]
    exact ⟨hq, ⟨hE _, trivial⟩, hE _, hq⟩
  | pcNext j =>
    simp only [timeEq, tv, allVars_add, allVars_var]
    exact ⟨hq, allVars_sumCode _ _ _ _ fun p I _ hp => hP p I j (by simpa using hp) hq⟩
  | recAct =>
    simp only [timeEq, tv, rv, allVars_add, allVars_var]
    exact ⟨by show 0 < 1; omega, ⟨hE _, hE _⟩, trivial⟩
  | recRgn => simp only [timeEq, tv, rv, allVars_add, allVars_var]; exact ⟨by show 0 < 1; omega, trivial⟩
  | recAd j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, rv, allVars_add, allVars_mul, allVars_var]
    refine ⟨hj, ⟨⟨hE _, hE _⟩, hj⟩, ?_⟩
    split_ifs with h
    · simp only [allVars_mul, allVars_var]; exact ⟨trivial, h⟩
    · simp
  | recPh => simp only [timeEq, rv, allVars_add, allVars_var, allVars_one]; exact ⟨by show 0 < 1; omega, trivial⟩
  | recVa j =>
    have hj : j < M.w := hq
    simp only [timeEq, tv, rv, allVars_add, allVars_mul, allVars_var]
    exact ⟨hj, ⟨⟨hE _, hE _⟩, hj⟩, trivial, hj⟩
  | recSt => simp only [timeEq, rv, allVars_add, allVars_var]; exact ⟨by show 0 < 1; omega, hE _⟩
  | tsn j =>
    have hj : j < τ := hq
    simp only [timeEq, tv, rv, tcE, allVars_add, allVars_var]
    refine ⟨⟨hj, hj⟩, ?_⟩
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < τ; omega
  | tc j =>
    have hj : j + 1 < τ := hq
    simp only [timeEq, tv, rv, tcE, allVars_add, allVars_mul, allVars_var]
    refine ⟨hj, by show j < τ; omega, ?_⟩
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < τ; omega
  | aA =>
    simp only [timeEq, tv, allVars_add, allVars_mul, allVars_var, allVars_compl]; exact ⟨trivial, hE _, trivial⟩
  | can j =>
    have hj : j < τ := hq
    simp only [timeEq, tv, acE, allVars_add, allVars_var]
    refine ⟨⟨hj, hj⟩, ?_⟩
    rcases j with _ | j
    · simp only [if_true, allVars_var]; trivial
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < τ; omega
  | ac j =>
    have hj : j + 1 < τ := hq
    simp only [timeEq, tv, acE, allVars_add, allVars_mul, allVars_var]
    refine ⟨hj, by show j < τ; omega, ?_⟩
    rcases j with _ | j
    · simp only [if_true, allVars_var]; trivial
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j + 1 < τ; omega
  | aB =>
    simp only [timeEq, tv, allVars_add, allVars_mul, allVars_var, allVars_compl]; exact ⟨trivial, hE _, trivial⟩
  | cbn j =>
    have hj : j ≤ (dims M τ).β := hq
    simp only [timeEq, tv, bcE, allVars_add, allVars_var]
    refine ⟨⟨hj, hj⟩, ?_⟩
    rcases j with _ | j
    · simp only [if_true, allVars_var]; trivial
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j < (dims M τ).β; omega
  | bc j =>
    have hj : j < (dims M τ).β := hq
    simp only [timeEq, tv, bcE, allVars_add, allVars_mul, allVars_var]
    refine ⟨hj, by show j ≤ (dims M τ).β; omega, ?_⟩
    rcases j with _ | j
    · simp only [if_true, allVars_var]; trivial
    · simp only [Nat.add_one_ne_zero, if_false, allVars_var]; show j < (dims M τ).β; omega
  | bound =>
    simp only [timeEq, tv, allVars_mul, allVars_var]
    exact ⟨trivial, le_refl _⟩

/-- **(S1)–(S5) read only slots of `def:event-trace`** (for `w ≥ 1`). -/
theorem sortEq_reads_active (d : Dims) (hw : 1 ≤ d.w) (q : SEq) (hq : q.Active d) :
    ∀ v ∈ (sortEq d q).vars, v.Active d := by
  have hk : ∀ l, l < d.κ → SVar.Active d (.inr (keySlot d l)) ∧
      SVar.Active d (.inl (.prev (keySlot d l).1 (keySlot d l).2)) := by
    intro l hl
    unfold Dims.κ at hl
    unfold keySlot
    split_ifs with h1 h2 h3
    · exact ⟨h1, by simp, h1⟩
    · exact ⟨by show 0 < 1; omega, by simp, by show 0 < 1; omega⟩
    · exact ⟨by show _ < d.w; omega, by simp, by show _ < d.w; omega⟩
    · exact ⟨by show 0 < 1; omega, by simp, by show 0 < 1; omega⟩
  have h01 : ∀ f : RecField, f ≠ .st → f ≠ .va → f ≠ .ad → f ≠ .ts →
      SVar.Active d (.inl (.prev f 0)) ∧ SVar.Active d (.inr (f, 0)) := by
    intro f h1 h2 h3 h4
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
      exact ⟨⟨by decide, by show 0 < 1; omega⟩, by show 0 < 1; omega⟩
  have hst : SVar.Active d (.inr (.st, 0)) := by show 0 < 1; omega
  intro v hv
  revert v
  show AllVars (SVar.Active d) (sortEq d q)
  cases q with
  | act =>
    simp only [sortEq, sv, srv, allVars_mul, allVars_compl, allVars_var]
    exact ⟨(h01 .act (by decide) (by decide) (by decide) (by decide)).1,
      (h01 .act (by decide) (by decide) (by decide) (by decide)).2⟩
  | both =>
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    exact ⟨trivial, (h01 .act (by decide) (by decide) (by decide) (by decide)).2,
      (h01 .act (by decide) (by decide) (by decide) (by decide)).1⟩
  | borrow l =>
    have hl : l < d.κ := hq
    simp only [sortEq, sv, keyE, pkeyE, obE, allVars_add, allVars_mul, allVars_compl, allVars_var]
    have hob : AllVars (SVar.Active d) (if l = 0 then zero else sv (.ob (l - 1))) := by
      rcases l with _ | l
      · simp
      · simp only [Nat.add_one_ne_zero, if_false, sv, allVars_var]; show l < d.κ; omega
    exact ⟨hl, ⟨(hk l hl).2, (hk l hl).1, hob⟩, (hk l hl).1, hob⟩
  | strict =>
    simp only [sortEq, sv, obE, allVars_mul, allVars_compl, allVars_var]
    refine ⟨trivial, ?_⟩
    split_ifs with h
    · simp
    · simp only [allVars_var]; show _ < d.κ; omega
  | soFirst =>
    simp only [sortEq, sv, srv, allVars_add, allVars_var]
    exact ⟨Nat.zero_le _, (h01 .rgn (by decide) (by decide) (by decide) (by decide)).1,
      (h01 .rgn (by decide) (by decide) (by decide) (by decide)).2⟩
  | soNext j =>
    have hj : j < d.w := hq
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    have ha : SVar.Active d (.inl (.prev .ad j)) := ⟨by decide, hj⟩
    have hb : SVar.Active d (.inr (.ad, j)) := hj
    have hs : SVar.Active d (.inl (.so j)) := by show j ≤ d.w; omega
    exact ⟨hj, ⟨hs, ha, hb⟩, hs, ha, hb⟩
  | u =>
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_compl, allVars_var]
    exact ⟨trivial, (h01 .act (by decide) (by decide) (by decide) (by decide)).2,
      (h01 .rgn (by decide) (by decide) (by decide) (by decide)).2⟩
  | g =>
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_compl, allVars_var]
    exact ⟨trivial, trivial, hst⟩
  | ev j =>
    have hj : j < d.w := hq
    simp only [sortEq, sv, allVars_add, allVars_mul, allVars_compl, allVars_var]
    exact ⟨hj, le_refl _, by decide, hj⟩
  | load j =>
    have hj : j < d.w := hq
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    exact ⟨trivial, hj, hj⟩
  | gA1 =>
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    exact ⟨trivial, (h01 .act (by decide) (by decide) (by decide) (by decide)).2,
      (h01 .rgn (by decide) (by decide) (by decide) (by decide)).2⟩
  | gA =>
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    exact ⟨trivial, trivial, (h01 .ph (by decide) (by decide) (by decide) (by decide)).2⟩
  | same => simp only [sortEq, sv, allVars_mul, allVars_var]; exact ⟨trivial, le_refl _⟩
  | phase =>
    simp only [sortEq, sv, allVars_mul, allVars_var]
    exact ⟨trivial, (h01 .ph (by decide) (by decide) (by decide) (by decide)).1⟩
  | value j =>
    have hj : j < d.w := hq
    simp only [sortEq, sv, srv, allVars_add, allVars_mul, allVars_var]
    exact ⟨trivial, hj, by decide, hj⟩

end NearCubicGates.Adapters.RAMTrace
