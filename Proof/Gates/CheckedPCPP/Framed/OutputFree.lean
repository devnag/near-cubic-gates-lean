import Proof.Gates.CheckedPCPP.Framed.Bridge

/-! # The bridge without the output-length term

A corollary of the bridge. One Mathlib TM2 step executes one statement tree, which pushes
at most `stmtSize` symbols, so after `N` steps the stacks hold at most `|input| + N · maxStmtSize`
symbols (`iter_stackSize`). In particular the output of a `TM2ComputableInTime` machine has length
at most `|ea a| + time (ea a).length · maxStmtSize` (`output_length_le`), and the bridge's budget
`simConstant · (T + n + m + 1)` is at most `simConstant · (maxStmtSize + 2) · (T + n + 1)`
(`tm2ToOrdinaryOutputFree`).
-/

namespace NearCubicGates.Close.FramedSim
open NearCubicWires
open LocalBitMultitape RepairOrdinary Turing StateTransition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section Size
variable (tm : FinTM2)

/-- Total number of symbols on all stacks. -/
def stackSize (S : ∀ k, List (tm.Γ k)) : ℕ := ∑ k, (S k).length

theorem stackSize_update (S : ∀ k, List (tm.Γ k)) (k : tm.K) (x : List (tm.Γ k)) :
    stackSize tm (Function.update S k x) + (S k).length = stackSize tm S + x.length := by
  classical
  unfold stackSize
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun k => (S k).length) (Finset.mem_univ k)]
  have hrest : ∑ k' ∈ Finset.univ.erase k, (Function.update S k x k').length =
      ∑ k' ∈ Finset.univ.erase k, (S k').length :=
    Finset.sum_congr rfl (fun k' hk' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')])
  rw [hrest, Function.update_self]
  omega

theorem stepAux_stackSize : ∀ (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
    stackSize tm (TM2.stepAux q v S).stk ≤ stackSize tm S + stmtSize tm q
  | .push k f q, v, S => by
      have ih := stepAux_stackSize q v (Function.update S k (f v :: S k))
      have hu := stackSize_update tm S k (f v :: S k)
      simp only [TM2.stepAux, stmtSize]
      simp only [List.length_cons] at hu
      omega
  | .peek k f q, v, S => by
      have ih := stepAux_stackSize q (f v (S k).head?) S
      simp only [TM2.stepAux, stmtSize]
      omega
  | .pop k f q, v, S => by
      have ih := stepAux_stackSize q (f v (S k).head?) (Function.update S k (S k).tail)
      have hu := stackSize_update tm S k (S k).tail
      have ht : (S k).tail.length ≤ (S k).length := by simp
      simp only [TM2.stepAux, stmtSize]
      omega
  | .load a q, v, S => by
      have ih := stepAux_stackSize q (a v) S
      simp only [TM2.stepAux, stmtSize]
      omega
  | .branch p q₁ q₂, v, S => by
      have ih₁ := stepAux_stackSize q₁ v S
      have ih₂ := stepAux_stackSize q₂ v S
      simp only [TM2.stepAux, stmtSize]
      cases p v <;> simp only [cond_false, cond_true] <;> omega
  | .goto _, _, _ => by simp [TM2.stepAux, stmtSize]
  | .halt, _, _ => by simp [TM2.stepAux, stmtSize]

theorem iter_stackSize : ∀ (N : ℕ) (c d : TM2.Cfg tm.Γ tm.Λ tm.σ),
    (flip bind (FinTM2.step tm))^[N] (some c) = some d →
    stackSize tm d.stk ≤ stackSize tm c.stk + N * maxStmtSize tm
  | 0, c, d, h => by
      simp only [Function.iterate_zero, id] at h
      have hcd := Option.some.inj h
      subst hcd
      simp
  | N + 1, c, d, h => by
      rw [Function.iterate_succ_apply] at h
      cases hl : c.l with
      | none =>
          have hnone : flip bind (FinTM2.step tm) (some c) = none := by
            obtain ⟨l0, v0, S0⟩ := c
            simp only at hl
            subst hl
            rfl
          rw [hnone, iterate_none] at h
          exact absurd h (by simp)
      | some l =>
          have hstep : flip bind (FinTM2.step tm) (some c) =
              some (TM2.stepAux (tm.m l) c.var c.stk) := by
            obtain ⟨l0, v0, S0⟩ := c
            simp only at hl
            subst hl
            rfl
          rw [hstep] at h
          have h1 := stepAux_stackSize tm (tm.m l) c.var c.stk
          have h2 := iter_stackSize N _ d h
          have h3 := stmtSize_le_max tm l
          rw [Nat.add_mul, Nat.one_mul]
          omega

theorem initList_stackSize (l : List (tm.Γ tm.k₀)) :
    stackSize tm (initList tm l).stk = l.length := by
  classical
  unfold stackSize
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp [initList, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem haltList_length_le (l : List (tm.Γ tm.k₁)) :
    l.length ≤ stackSize tm (haltList tm l).stk := by
  classical
  unfold stackSize
  have := Finset.single_le_sum (f := fun k => ((haltList tm l).stk k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ tm.k₁)
  simpa [haltList] using this

end Size

/-- The output length is at most `|input| + time · maxStmtSize`. -/
theorem output_length_le {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + h.time (ea a).length * maxStmtSize h.tm := by
  have ho := h.outputsFun a
  have hs := iter_stackSize h.tm ho.steps _ _ ho.evals_in_steps
  have hl := haltList_length_le h.tm (List.map h.outputAlphabet.invFun (eb (f a)))
  have hi := initList_stackSize h.tm (List.map h.inputAlphabet.invFun (ea a))
  have hT := Nat.mul_le_mul_right (maxStmtSize h.tm) ho.steps_le_m
  simp only [List.length_map] at hl hi
  omega

/-- **The bridge without the output term**: budget `simConstant · (maxStmtSize + 2) · (T + n + 1)`. -/
noncomputable def tm2ToOrdinaryOutputFree {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInTime ea eb f) :
    RepairSource.OrdinaryWordFunction α ea (fun a => pairs (eb (f a)))
      (fun a => simConstant h.tm * (maxStmtSize h.tm + 2) * (h.time (ea a).length + (ea a).length + 1)) :=
  RepairOrdinary.WordFunction.enlargeBudget (tm2ToOrdinary h) (fun a => by
    have hm := output_length_le h a
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith [Nat.zero_le (maxStmtSize h.tm * (ea a).length), Nat.zero_le (maxStmtSize h.tm)])

theorem tm2_to_ordinary_outputFree {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInTime ea eb f) :
    ∃ C : ℕ, Nonempty (RepairSource.OrdinaryWordFunction α ea (fun a => pairs (eb (f a)))
      (fun a => C * (h.time (ea a).length + (ea a).length + 1))) :=
  ⟨simConstant h.tm * (maxStmtSize h.tm + 2), ⟨tm2ToOrdinaryOutputFree h⟩⟩

/-! ## The constant in terms of labels, states and statement sizes -/

section Constant
variable (tm : FinTM2)

theorem card_stmts₁_le : ∀ q : TM2.Stmt tm.Γ tm.Λ tm.σ, (TM2.stmts₁ q).card ≤ stmtSize tm q
  | .push k f q => by
      classical
      have := card_stmts₁_le q
      simp only [TM2.stmts₁, stmtSize]
      exact (Finset.card_insert_le _ _).trans (by omega)
  | .peek k f q => by
      classical
      have := card_stmts₁_le q
      simp only [TM2.stmts₁, stmtSize]
      exact (Finset.card_insert_le _ _).trans (by omega)
  | .pop k f q => by
      classical
      have := card_stmts₁_le q
      simp only [TM2.stmts₁, stmtSize]
      exact (Finset.card_insert_le _ _).trans (by omega)
  | .load a q => by
      classical
      have := card_stmts₁_le q
      simp only [TM2.stmts₁, stmtSize]
      exact (Finset.card_insert_le _ _).trans (by omega)
  | .branch p q₁ q₂ => by
      classical
      have h1 := card_stmts₁_le q₁
      have h2 := card_stmts₁_le q₂
      have hu := Finset.card_union_le (TM2.stmts₁ q₁) (TM2.stmts₁ q₂)
      simp only [TM2.stmts₁, stmtSize]
      exact (Finset.card_insert_le _ _).trans (by omega)
  | .goto _ => by simp [TM2.stmts₁, stmtSize]
  | .halt => by simp [TM2.stmts₁, stmtSize]

/-- Program points: at most `|Λ| · maxStmtSize`. -/
theorem card_Pt_le : Fintype.card (Pt tm) ≤ Fintype.card tm.Λ * maxStmtSize tm := by
  classical
  rw [Fintype.card_coe]
  unfold allStmts
  refine (Finset.card_biUnion_le).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset tm.Λ), (TM2.stmts₁ (tm.m l)).card ≤ maxStmtSize tm :=
    fun l _ => (card_stmts₁_le tm (tm.m l)).trans (stmtSize_le_max tm l)
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- **The constant, explicitly**: with `L = |Λ|` labels, `s = |σ|` states and `S` the largest
statement tree, `simConstant ≤ (2B' + 3)·S + 3B' + 7` where `B' = 2 + L·S·s`. It does not
depend on the number of stacks or on the stack alphabets. -/
theorem simConstant_le_explicit :
    simConstant tm ≤ (2 * (2 + Fintype.card tm.Λ * maxStmtSize tm * Fintype.card tm.σ) + 3) *
      maxStmtSize tm + 3 * (2 + Fintype.card tm.Λ * maxStmtSize tm * Fintype.card tm.σ) + 8 := by
  have hB : codeWidth tm ≤ 2 + Fintype.card tm.Λ * maxStmtSize tm * Fintype.card tm.σ := by
    rw [codeWidth_eq]
    have := Nat.mul_le_mul_right (Fintype.card tm.σ) (card_Pt_le tm)
    omega
  rw [simConstant_eq]
  have := Nat.mul_le_mul_right (maxStmtSize tm) (show 2 * codeWidth tm + 3 ≤
    2 * (2 + Fintype.card tm.Λ * maxStmtSize tm * Fintype.card tm.σ) + 3 by omega)
  omega

end Constant

end NearCubicGates.Close.FramedSim
