import SourceAdapters.RAMTrace.Defs
import SourceAdapters.RAMACSP.ConstraintCatalog
import SourceAdapters.Routing.CircuitExpr

/-!
# Sizes of the equation trees (for `lem:generator`)

Paper: `lem:generator`. Each degree-two equation is emitted from its
fixed expression tree, with every variable read resolved to its bank offset;
the gate bound counts this literal expression.

`esize` counts the nodes of an equation tree; `toRouting` keeps it (`gateCount_toRouting`). Every time-row equation has
at most `30 L + 60` nodes (`L` the code length; `timeEq_size_le`), every sorted-vertex equation at most `30`
(`sortEq_size_le`), `e(Out)`, `e(Acc) + 1` at most `2L + 3`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMTrace
open RAMTrace.Expr

/-- The number of nodes of an equation tree. -/
def esize {ι : Type} : RAMTrace.Expr ι → ℕ
  | .zero => 1
  | .one => 1
  | .var _ => 1
  | .add a b => esize a + esize b + 1
  | .mul a b => esize a + esize b + 1

theorem gateCount_toRouting {F : Type} [Field F] [CharP F 2] {ι : Type} (rd : ι → ℕ) :
    ∀ e : RAMTrace.Expr ι, Routing.Circuit.gateCount (toRouting (F := F) rd e) = esize e
  | .zero => rfl
  | .one => rfl
  | .var _ => rfl
  | .add a b => by simp [toRouting, Routing.Circuit.gateCount, esize, gateCount_toRouting rd a, gateCount_toRouting rd b]
  | .mul a b => by simp [toRouting, Routing.Circuit.gateCount, esize, gateCount_toRouting rd a, gateCount_toRouting rd b]

section Generic

variable {ι : Type}

theorem esize_sumCode_le {α : Type} (f : ℕ → α → RAMTrace.Expr ι) (B : ℕ) (h : ∀ p I, esize (f p I) ≤ B) :
    ∀ (l : List α) (p0 : ℕ), esize (sumCode f p0 l) ≤ l.length * (B + 1) + 1
  | [], _ => by simp [sumCode, esize]
  | I :: l, p0 => by
    have := esize_sumCode_le f B h l (p0 + 1)
    have := h p0 I
    simp only [sumCode, esize, List.length_cons]
    nlinarith

theorem esize_sum_le (B : ℕ) : ∀ (l : List (RAMTrace.Expr ι)), (∀ e ∈ l, esize e ≤ B) →
    esize (RAMTrace.Expr.sum l) ≤ l.length * (B + 1) + 1
  | [], _ => by simp [RAMTrace.Expr.sum, esize]
  | a :: l, h => by
    have := esize_sum_le B l fun e he => h e (by simp [he])
    have := h a (by simp)
    simp only [RAMTrace.Expr.sum, esize, List.length_cons]
    nlinarith

theorem esize_bit (b : Bool) : esize (RAMTrace.Expr.bit b : RAMTrace.Expr ι) = 1 := by cases b <;> rfl

end Generic

section Time

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ)

theorem esize_eSet (Q : Instr M.w M.k M.ops → Bool) : esize (eSet M Q) ≤ 2 * M.code.length + 1 := by
  have := esize_sumCode_le (fun p I => if Q I then tv (.e p) else (zero : RAMTrace.Expr TVar)) 1
    (fun p I => by split_ifs <;> simp [esize]) M.code 0
  unfold eSet; omega

theorem esize_opnd (x : Operand M.w M.k) (j : ℕ) : esize (opnd M x j) ≤ 1 := by
  cases x <;> simp [opnd, esize, esize_bit]

theorem esize_eDot (s : Instr M.w M.k M.ops → RAMTrace.Expr TVar) (h : ∀ I, esize (s I) ≤ 1) :
    esize (eDot M s) ≤ 4 * M.code.length + 1 := by
  have := esize_sumCode_le (fun p I => mul (tv (.e p)) (s I)) 3 (fun p I => by
    simp only [esize]; have := h I; omega) M.code 0
  unfold eDot; omega

theorem esize_srcX (I : Instr M.w M.k M.ops) (j : ℕ) : esize (srcX M I j) ≤ 1 := by
  cases I <;> simp only [srcX, esize] <;> first | exact esize_opnd M _ j | omega

theorem esize_srcY (I : Instr M.w M.k M.ops) (j : ℕ) : esize (srcY M I j) ≤ 1 := by
  cases I <;> simp only [srcY, esize] <;> first | exact esize_opnd M _ j | omega

theorem esize_srcXF (I : Instr M.w M.k M.ops) : esize (srcXF M I) ≤ 1 := by
  cases I <;> simp [srcXF, esize]

theorem esize_pcTerm (p : ℕ) (I : Instr M.w M.k M.ops) (j : ℕ) : esize (pcTerm M p I j) ≤ 13 := by
  cases I <;> simp [pcTerm, esize, esize_bit]

theorem esize_cin (j : ℕ) : esize (caE j) ≤ 1 ∧ esize (boE j) ≤ 1 ∧ esize (tcE j) ≤ 1 ∧ esize (acE j) ≤ 1 ∧
    esize (bcE j) ≤ 1 ∧ esize (cmpE M j) ≤ 3 := by
  unfold caE boE tcE acE bcE cmpE
  split_ifs <;> simp [esize]

/-- **(T1)–(T10) have at most `30 L + 60` nodes.** -/
theorem timeEq_size_le (q : TEq) : esize (timeEq M kind τ q) ≤ 30 * M.code.length + 60 := by
  have e := fun Q => esize_eSet M Q
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ : esize (eSet M isLd) ≤ 2 * M.code.length + 1 ∧
      esize (eSet M isSt) ≤ 2 * M.code.length + 1 ∧ esize (eSet M isRd) ≤ 2 * M.code.length + 1 ∧
      esize (eSet M isRdA) ≤ 2 * M.code.length + 1 ∧ esize (eSet M isRdB) ≤ 2 * M.code.length + 1 ∧
      esize (eSet M isEof) ≤ 2 * M.code.length + 1 ∧ esize (eSet M (isAr kind .add)) ≤ 2 * M.code.length + 1 ∧
      esize (eSet M (isAr kind .sub)) ≤ 2 * M.code.length + 1 ∧ esize (eSet M (isAr kind .and)) ≤ 2 * M.code.length + 1 ∧
      esize (eSet M (isAr kind .cmp)) ≤ 2 * M.code.length + 1 := ⟨e _, e _, e _, e _, e _, e _, e _, e _, e _, e _⟩
  cases q with
  | decPc j =>
    have := esize_sumCode_le (fun p (_ : Instr M.w M.k M.ops) => if p.testBit j then tv (.e p) else
      (zero : RAMTrace.Expr TVar)) 1 (fun p I => by split_ifs <;> simp [esize]) M.code 0
    simp only [timeEq, esize]; omega
  | opX j => have := esize_eDot M _ fun I => esize_srcX M I j; simp only [timeEq, esize]; omega
  | opY j => have := esize_eDot M _ fun I => esize_srcY M I j; simp only [timeEq, esize]; omega
  | opXF => have := esize_eDot M (fun I => srcXF M I) fun I => esize_srcXF M I; simp only [timeEq, esize]; omega
  | res j =>
    have ec := (esize_cin M j).2.2.2.2.2
    simp only [timeEq, esize]
    have := esize_sum_le (2 * M.code.length + 5) [mul (eSet M (isAr kind .add)) (tv (.AD j)),
       mul (eSet M (isAr kind .sub)) (tv (.SB j)),
       mul (eSet M (isAr kind .and)) (tv (.AN j)),
       mul (eSet M (isAr kind .cmp)) (cmpE M j),
       mul (eSet M isLd) (tv (.MV j)),
       mul (eSet M isRd) (tv (.RV j)),
       if j = 0 then mul (eSet M isEof) (tv .XF) else zero] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try split_ifs) <;> simp only [esize] <;> omega)
    simp only [List.length_cons, List.length_nil] at this
    omega
  | pcNext j =>
    have := esize_sumCode_le _ 13 (fun p I => esize_pcTerm M p I j) M.code 0
    simp only [timeEq, esize]; omega
  | reg r j =>
    have := e (writes r)
    simp only [timeEq, esize, RAMTrace.Expr.compl]; omega
  | regF r =>
    have := e (writes r)
    simp only [timeEq, esize, RAMTrace.Expr.compl]; omega
  | recAd j =>
    simp only [timeEq, esize]
    split_ifs <;> simp only [esize] <;> omega
  | _ =>
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := esize_cin M 0
    simp only [timeEq, esize, RAMTrace.Expr.compl, RAMTrace.Expr.maj]
    try split_ifs
    all_goals first
      | omega
      | (rename_i j; obtain ⟨d1, d2, d3, d4, d5, d6⟩ := esize_cin M j; omega)

theorem outE_size_le : esize (outE M) ≤ 2 * M.code.length + 3 := by
  have := esize_eSet M isOut; unfold outE; omega

theorem accE_size_le : esize (accE M) ≤ 2 * M.code.length + 3 := by
  have := esize_eSet M isAcc; simp only [accE, esize]; omega

end Time

/-- **(S1)–(S5) have at most `30` nodes.** -/
theorem sortEq_size_le (d : Dims) (q : SEq) : esize (sortEq d q) ≤ 30 := by
  have hob : ∀ l, esize (obE l : RAMTrace.Expr SVar) ≤ 1 := by
    intro l; unfold obE; split_ifs <;> simp [esize]
  have hk : ∀ l, esize (keyE d l) ≤ 1 ∧ esize (pkeyE d l) ≤ 1 := by
    intro l; unfold keyE pkeyE; simp [esize]
  cases q with
  | borrow l =>
    have := hob l; have := hk l
    simp only [sortEq, esize, RAMTrace.Expr.compl, sv]; omega
  | strict =>
    have := hob d.κ
    simp only [sortEq, esize, RAMTrace.Expr.compl, sv]; omega
  | _ =>
    simp only [sortEq, esize, RAMTrace.Expr.compl, sv, srv]
    all_goals omega

end NearCubicGates.Adapters.RAMACSP.Gen
