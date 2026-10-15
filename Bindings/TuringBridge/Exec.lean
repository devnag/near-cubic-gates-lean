import Bindings.TuringBridge.Machine

/-! # One TM2 step, and a whole TM2 run, on the simulating bit machine

Stages 2 and 3 of the bridge.

* `StackRel S C`: every TM2 stack `S k` sits on repo tape `stkTape k` as a code layout
  (`lay`, `Bindings.TuringBridge.Core`) whose codes decode to `S k`, with the head on the top flag; the output
  tape is still fresh.
* `SimRel c C`: additionally the control of `C` is the resting control of the TM2 configuration `c`
  (`exec` at the label's statement, or the output phase once `c` has halted).
* `stmt_sim`: executing a TM2 statement tree (`TM2.stepAux`, i.e. one Mathlib TM2 `step`) takes
  EXACTLY `stmtCost` repo steps and re-establishes `SimRel` for the resulting configuration.
* `stmtCost_le`: `stmtCost ≤ (2·codeWidth + 3) · stmtSize`.
* `iter_sim`: `N` Mathlib steps `(flip bind tm.step)^[N]` are simulated in at most
  `N · stepBound tm` repo steps.
-/

namespace NearCubicWires.Bindings.Sim
open LocalBitMultitape RepairOrdinary Turing
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section Exec
variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)

/-- Configurations of the simulating machine. -/
abbrev Cf := Configuration (nT tm) (Fintype.card (C tm))

/-- Stack `S` of stack `k` on a tape, head `h`: codes decoding to `S`, head on the top flag. -/
def StackTape (k : tm.K) (S : List (tm.Γ k)) (h : ℕ) (T : List Bool) : Prop :=
  ∃ cs : List (Src tm), cs.map (val tm ein k) = S.map some ∧
    h = cs.length * (codeWidth tm + 1) ∧ Agrees T (lay (enc tm) cs)

/-- All stacks on their tapes, output tape fresh. -/
def StackRel (S : ∀ k, List (tm.Γ k)) (C0 : Cf tm) : Prop :=
  (∀ k, StackTape tm ein k (S k) (C0.heads (stkTape tm k)) (C0.tapes (stkTape tm k))) ∧
    C0.tapes (outTape tm) = [] ∧ C0.heads (outTape tm) = 0

/-- The resting control of a TM2 configuration. -/
noncomputable def ctlOf (c : TM2.Cfg tm.Γ tm.Λ tm.σ) : C tm :=
  match c.l with
  | some l => .at (.exec (mkPt tm (tm.m l)) c.var)
  | none => .at (.popAt (stkTape tm tm.k₁) .out)

/-- The simulation relation. -/
def SimRel (c : TM2.Cfg tm.Γ tm.Λ tm.σ) (C0 : Cf tm) : Prop :=
  C0.control = code tm (ctlOf tm c) ∧ StackRel tm ein c.stk C0

/-! ## Exact cost of a statement -/

/-- Pop macro cost. -/
def popCost {α : Type} (B : ℕ) : List α → ℕ
  | [] => 1
  | _ :: _ => 1 + B

/-- Peek macro cost. -/
def peekCost {α : Type} (B : ℕ) : List α → ℕ
  | [] => 1
  | _ :: _ => 1 + B + (B + 1)

/-- Exact repo steps to execute a statement tree from state `v` on stacks `S`
(one dispatch step per node, plus the node's stack macro). -/
noncomputable def stmtCost : TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → (∀ k, List (tm.Γ k)) → ℕ
  | .push k f q, v, S =>
      1 + (codeWidth tm + 2) + stmtCost q v (Function.update S k (f v :: S k))
  | .peek k f q, v, S => 1 + peekCost (codeWidth tm) (S k) + stmtCost q (f v (S k).head?) S
  | .pop k f q, v, S =>
      1 + popCost (codeWidth tm) (S k) + stmtCost q (f v (S k).head?) (Function.update S k (S k).tail)
  | .load a q, v, S => 1 + stmtCost q (a v) S
  | .branch f q₁ q₂, v, S => 1 + cond (f v) (stmtCost q₁ v S) (stmtCost q₂ v S)
  | .goto _, _, _ => 1
  | .halt, _, _ => 1

/-- Number of nodes of a statement tree. -/
def stmtSize {Γ : tm.K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtSize q
  | .peek _ _ q => 1 + stmtSize q
  | .pop _ _ q => 1 + stmtSize q
  | .load _ q => 1 + stmtSize q
  | .branch _ q₁ q₂ => 1 + stmtSize q₁ + stmtSize q₂
  | .goto _ => 1
  | .halt => 1

/-- The largest statement tree of the program. -/
noncomputable def maxStmtSize : ℕ := Finset.univ.sup fun l => stmtSize tm (tm.m l)

/-- Repo steps per TM2 step. -/
noncomputable def stepBound : ℕ := (2 * codeWidth tm + 3) * maxStmtSize tm

theorem stmtCost_le : ∀ (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
    stmtCost tm q v S ≤ (2 * codeWidth tm + 3) * stmtSize tm q
  | .push k f q, v, S => by
      have := stmtCost_le q v (Function.update S k (f v :: S k))
      simp only [stmtCost, stmtSize, Nat.mul_add, Nat.mul_one]
      omega
  | .peek k f q, v, S => by
      have := stmtCost_le q (f v (S k).head?) S
      have hp : peekCost (codeWidth tm) (S k) ≤ 2 * codeWidth tm + 2 := by
        cases S k <;> simp [peekCost]; omega
      simp only [stmtCost, stmtSize, Nat.mul_add, Nat.mul_one]
      omega
  | .pop k f q, v, S => by
      have := stmtCost_le q (f v (S k).head?) (Function.update S k (S k).tail)
      have hp : popCost (codeWidth tm) (S k) ≤ 2 * codeWidth tm + 2 := by
        cases S k <;> simp [popCost]; omega
      simp only [stmtCost, stmtSize, Nat.mul_add, Nat.mul_one]
      omega
  | .load a q, v, S => by
      have := stmtCost_le q (a v) S
      simp only [stmtCost, stmtSize, Nat.mul_add, Nat.mul_one]
      omega
  | .branch f q₁ q₂, v, S => by
      have h1 := stmtCost_le q₁ v S
      have h2 := stmtCost_le q₂ v S
      simp only [stmtCost, stmtSize, Nat.mul_add, Nat.mul_one]
      cases f v <;> simp only [cond_false, cond_true] <;> omega
  | .goto _, _, _ => by simp [stmtCost, stmtSize]
  | .halt, _, _ => by simp [stmtCost, stmtSize]

theorem stmtSize_le_max (l : tm.Λ) : stmtSize tm (tm.m l) ≤ maxStmtSize tm :=
  Finset.le_sup (f := fun l => stmtSize tm (tm.m l)) (Finset.mem_univ l)

/-! ## Relation lemmas -/

theorem StackRel.congr {S : ∀ k, List (tm.Γ k)} {C0 C1 : Cf tm} (h : StackRel tm ein S C0)
    (hh : C1.heads = C0.heads) (ht : C1.tapes = C0.tapes) : StackRel tm ein S C1 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun k => by rw [hh, ht]; exact h1 k, by rw [ht]; exact h2, by rw [hh]; exact h3⟩

/-- Changing one stack tape re-establishes the relation for the updated stack family. -/
theorem StackRel.update {S : ∀ k, List (tm.Γ k)} {C0 C1 : Cf tm} (h : StackRel tm ein S C0)
    (k : tm.K) (x : List (tm.Γ k))
    (hoth : ∀ j, j ≠ stkTape tm k → C1.heads j = C0.heads j ∧ C1.tapes j = C0.tapes j)
    (hk : StackTape tm ein k x (C1.heads (stkTape tm k)) (C1.tapes (stkTape tm k))) :
    StackRel tm ein (Function.update S k x) C1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have ho := hoth (outTape tm) (stkTape_ne_out tm k).symm
  refine ⟨fun k' => ?_, by rw [ho.2]; exact h2, by rw [ho.1]; exact h3⟩
  by_cases hkk : k' = k
  · subst hkk
    simpa using hk
  · have hne : stkTape tm k' ≠ stkTape tm k := fun he => hkk (stkTape_injective tm he)
    rw [Function.update_of_ne hkk, (hoth _ hne).1, (hoth _ hne).2]
    exact h1 k'

/-! ## One statement -/

theorem dispatch (q : Pt tm) (v : tm.σ) (C0 : Cf tm)
    (hC : C0.control = code tm (.at (.exec q v))) :
    Runs (machine tm ein eout) 1 C0 ⟨code tm (execNext tm q.1 q v), C0.heads, C0.tapes⟩ := by
  have hl := (loc tm ein eout (.at (.exec q v)) rfl).runs C0 hC
  simpa [rule, act_none_stay] using hl

theorem stmt_sim : ∀ (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : q ∈ allStmts tm) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (C0 : Cf tm), C0.control = code tm (.at (.exec ⟨q, hq⟩ v)) →
    StackRel tm ein S C0 →
    ∃ C', Runs (machine tm ein eout) (stmtCost tm q v S) C0 C' ∧
      SimRel tm ein (TM2.stepAux q v S) C'
  | .push k f q, hq, v, S, C0, hC, hrel => by
      have hq' : q ∈ allStmts tm := mem_allStmts_of tm (by
        classical
        simp only [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      obtain ⟨cs, hmap, hh, ha⟩ := hrel.1 k
      obtain ⟨C1, r1, hc1, hh1, ha1, hoth1⟩ :=
        push_op tm ein eout (stkTape tm k) (.inr (⟨_, hq⟩, v)) (.exec (mkPt tm q) v) cs
          ⟨code tm (execNext tm (TM2.Stmt.push k f q) ⟨_, hq⟩ v), C0.heads, C0.tapes⟩ rfl hh ha
      have hrel1 : StackRel tm ein (Function.update S k (f v :: S k)) C1 := by
        refine StackRel.update tm ein (hrel.congr tm ein (C1 := ⟨_, C0.heads, C0.tapes⟩) rfl rfl)
          k _ hoth1 ⟨.inr (⟨_, hq⟩, v) :: cs, ?_, ?_, ha1⟩
        · simp [hmap, val_push]
        · rw [hh1]; simp
      rw [mkPt_of_mem tm hq'] at hc1
      obtain ⟨C2, r2, hs2⟩ := stmt_sim q hq' v _ C1 hc1 hrel1
      refine ⟨C2, (Runs.trans (Runs.trans r0 r1) r2).of_eq ?_, ?_⟩
      · simp [stmtCost]
      · simpa using hs2
  | .peek k f q, hq, v, S, C0, hC, hrel => by
      have hq' : q ∈ allStmts tm := mem_allStmts_of tm (by
        classical
        simp only [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      obtain ⟨cs, hmap, hh, ha⟩ := hrel.1 k
      set C0' : Cf tm := ⟨code tm (execNext tm (TM2.Stmt.peek k f q) ⟨_, hq⟩ v), C0.heads, C0.tapes⟩
        with hC0'
      have hrel0 : StackRel tm ein S C0' := hrel.congr tm ein rfl rfl
      cases cs with
      | nil =>
          have hS : S k = [] := by simpa using hmap.symm
          have r1 := pop_op_nil tm ein eout (stkTape tm k) (.peek ⟨_, hq⟩ v) C0' rfl
            (by rw [hC0']; simpa using hh) ha
          have hrel1 : StackRel tm ein S
              ⟨code tm (resume tm ein (.peek ⟨_, hq⟩ v) none), C0'.heads, C0'.tapes⟩ :=
            hrel0.congr tm ein rfl rfl
          simp only [resume, resumePeek, mkPt_of_mem tm hq'] at r1 hrel1
          obtain ⟨C2, r2, hs2⟩ := stmt_sim q hq' (f v none) S _ rfl hrel1
          refine ⟨C2, (Runs.trans (Runs.trans r0 r1) r2).of_eq ?_, ?_⟩
          · simp [stmtCost, hS, peekCost]
          · simpa [hS] using hs2
      | cons c cs' =>
          obtain ⟨x, xs, hS, hx, hxs⟩ : ∃ x xs, S k = x :: xs ∧ val tm ein k c = some x ∧
              cs'.map (val tm ein k) = xs.map some := by
            cases hSk : S k with
            | nil => rw [hSk] at hmap; simp at hmap
            | cons x xs =>
                rw [hSk] at hmap
                simp only [List.map_cons, List.cons.injEq] at hmap
                exact ⟨x, xs, rfl, hmap.1, hmap.2⟩
          obtain ⟨C1, r1, hc1, hh1, ht1, hoth1⟩ :=
            pop_op_cons tm ein eout (stkTape tm k) (.peek ⟨_, hq⟩ v) c cs' C0' rfl
              (by rw [hC0']; simpa using hh) ha
          simp only [resume, resumePeek, hx] at hc1
          obtain ⟨C2, r2, hc2, hh2, ht2, hoth2⟩ :=
            back_op tm ein eout (stkTape tm k) (.exec (mkPt tm q) (f v (some x))) C1 hc1
          have hheads : C2.heads = C0'.heads := by
            funext j
            by_cases hj : j = stkTape tm k
            · subst hj
              rw [hh2, hh1, hC0']
              simp only [List.length_cons] at hh
              rw [hh]; ring
            · rw [hoth2 j hj, hoth1 j hj]
          have hrel2 : StackRel tm ein S C2 := hrel0.congr tm ein hheads (by rw [ht2, ht1])
          rw [mkPt_of_mem tm hq'] at hc2
          obtain ⟨C3, r3, hs3⟩ := stmt_sim q hq' (f v (some x)) S C2 hc2 hrel2
          refine ⟨C3, (Runs.trans (Runs.trans (Runs.trans r0 r1) r2) r3).of_eq ?_, ?_⟩
          · simp [stmtCost, hS, peekCost]; omega
          · simpa [hS] using hs3
  | .pop k f q, hq, v, S, C0, hC, hrel => by
      have hq' : q ∈ allStmts tm := mem_allStmts_of tm (by
        classical
        simp only [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      obtain ⟨cs, hmap, hh, ha⟩ := hrel.1 k
      set C0' : Cf tm := ⟨code tm (execNext tm (TM2.Stmt.pop k f q) ⟨_, hq⟩ v), C0.heads, C0.tapes⟩
        with hC0'
      have hrel0 : StackRel tm ein S C0' := hrel.congr tm ein rfl rfl
      cases cs with
      | nil =>
          have hS : S k = [] := by simpa using hmap.symm
          have r1 := pop_op_nil tm ein eout (stkTape tm k) (.pop ⟨_, hq⟩ v) C0' rfl
            (by rw [hC0']; simpa using hh) ha
          have hupd : Function.update S k (S k).tail = S := by
            rw [hS]; simp only [List.tail_nil]; rw [← hS]; exact Function.update_eq_self k S
          have hrel1 : StackRel tm ein (Function.update S k (S k).tail)
              ⟨code tm (resume tm ein (.pop ⟨_, hq⟩ v) none), C0'.heads, C0'.tapes⟩ := by
            rw [hupd]; exact hrel0.congr tm ein rfl rfl
          simp only [resume, resumePop, mkPt_of_mem tm hq', Option.bind_none] at r1 hrel1
          obtain ⟨C2, r2, hs2⟩ := stmt_sim q hq' (f v none) _ _ rfl hrel1
          refine ⟨C2, (Runs.trans (Runs.trans r0 r1) r2).of_eq ?_, ?_⟩
          · simp [stmtCost, hS, popCost]
          · simpa [hS] using hs2
      | cons c cs' =>
          obtain ⟨x, xs, hS, hx, hxs⟩ : ∃ x xs, S k = x :: xs ∧ val tm ein k c = some x ∧
              cs'.map (val tm ein k) = xs.map some := by
            cases hSk : S k with
            | nil => rw [hSk] at hmap; simp at hmap
            | cons x xs =>
                rw [hSk] at hmap
                simp only [List.map_cons, List.cons.injEq] at hmap
                exact ⟨x, xs, rfl, hmap.1, hmap.2⟩
          obtain ⟨C1, r1, hc1, hh1, ht1, hoth1⟩ :=
            pop_op_cons tm ein eout (stkTape tm k) (.pop ⟨_, hq⟩ v) c cs' C0' rfl
              (by rw [hC0']; simpa using hh) ha
          simp only [resume, resumePop, Option.bind_some, hx, mkPt_of_mem tm hq'] at hc1
          have hrel1 : StackRel tm ein (Function.update S k (S k).tail) C1 := by
            rw [hS]
            refine StackRel.update tm ein hrel0 k xs
              (fun j hj => ⟨hoth1 j hj, by rw [ht1]⟩) ⟨cs', hxs, hh1, ?_⟩
            rw [ht1]
            exact ha.tail (enc tm)
          obtain ⟨C2, r2, hs2⟩ := stmt_sim q hq' (f v (some x)) _ C1 hc1 hrel1
          refine ⟨C2, (Runs.trans (Runs.trans r0 r1) r2).of_eq ?_, ?_⟩
          · simp [stmtCost, hS, popCost]
          · simpa [hS] using hs2
  | .load a q, hq, v, S, C0, hC, hrel => by
      have hq' : q ∈ allStmts tm := mem_allStmts_of tm (by
        classical
        simp only [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      simp only [execNext, mkPt_of_mem tm hq'] at r0
      obtain ⟨C2, r2, hs2⟩ := stmt_sim q hq' (a v) S
        ⟨code tm (.at (.exec ⟨q, hq'⟩ (a v))), C0.heads, C0.tapes⟩ rfl (hrel.congr tm ein rfl rfl)
      refine ⟨C2, (Runs.trans r0 r2).of_eq ?_, ?_⟩
      · simp [stmtCost]
      · simpa using hs2
  | .branch p q₁ q₂, hq, v, S, C0, hC, hrel => by
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      simp only [execNext] at r0
      cases hp : p v with
      | true =>
          have hq' : q₁ ∈ allStmts tm := mem_allStmts_of tm (by
            classical
            simp only [TM2.stmts₁]
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self)) hq
          simp only [hp, cond_true, mkPt_of_mem tm hq'] at r0
          obtain ⟨C2, r2, hs2⟩ := stmt_sim q₁ hq' v S
            ⟨code tm (.at (.exec ⟨q₁, hq'⟩ v)), C0.heads, C0.tapes⟩ rfl (hrel.congr tm ein rfl rfl)
          refine ⟨C2, (Runs.trans r0 r2).of_eq ?_, ?_⟩
          · simp [stmtCost, hp]
          · simpa [hp] using hs2
      | false =>
          have hq' : q₂ ∈ allStmts tm := mem_allStmts_of tm (by
            classical
            simp only [TM2.stmts₁]
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self)) hq
          simp only [hp, cond_false, mkPt_of_mem tm hq'] at r0
          obtain ⟨C2, r2, hs2⟩ := stmt_sim q₂ hq' v S
            ⟨code tm (.at (.exec ⟨q₂, hq'⟩ v)), C0.heads, C0.tapes⟩ rfl (hrel.congr tm ein rfl rfl)
          refine ⟨C2, (Runs.trans r0 r2).of_eq ?_, ?_⟩
          · simp [stmtCost, hp]
          · simpa [hp] using hs2
  | .goto f, hq, v, S, C0, hC, hrel => by
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      refine ⟨_, r0.of_eq (by simp [stmtCost]), ?_, hrel.congr tm ein rfl rfl⟩
      simp [execNext, ctlOf]
  | .halt, hq, v, S, C0, hC, hrel => by
      have r0 := dispatch tm ein eout ⟨_, hq⟩ v C0 hC
      refine ⟨_, r0.of_eq (by simp [stmtCost]), ?_, hrel.congr tm ein rfl rfl⟩
      simp [execNext, ctlOf]

/-! ## One TM2 step, and many -/

theorem step_sim (c : TM2.Cfg tm.Γ tm.Λ tm.σ) (l : tm.Λ) (hl : c.l = some l) (C0 : Cf tm)
    (hs : SimRel tm ein c C0) :
    ∃ C', Runs (machine tm ein eout) (stmtCost tm (tm.m l) c.var c.stk) C0 C' ∧
      SimRel tm ein (TM2.stepAux (tm.m l) c.var c.stk) C' := by
  obtain ⟨hc, hrel⟩ := hs
  have hc' : C0.control = code tm (.at (.exec ⟨tm.m l, mem_allStmts_self tm l⟩ c.var)) := by
    rw [hc]; simp [ctlOf, hl, mkPt_of_mem tm (mem_allStmts_self tm l)]
  exact stmt_sim tm ein eout (tm.m l) _ c.var c.stk C0 hc' hrel

theorem iterate_none {α : Type} (f : α → Option α) :
    ∀ N, (flip bind f)^[N] (none : Option α) = none
  | 0 => rfl
  | N + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none f N

/-- `N` Mathlib TM2 steps cost at most `N · stepBound` repo steps. -/
theorem iter_sim : ∀ (N : ℕ) (c d : TM2.Cfg tm.Γ tm.Λ tm.σ) (C0 : Cf tm),
    (flip bind (FinTM2.step tm))^[N] (some c) = some d → SimRel tm ein c C0 →
    ∃ n C', Runs (machine tm ein eout) n C0 C' ∧ SimRel tm ein d C' ∧ n ≤ N * stepBound tm
  | 0, c, d, C0, h, hs => by
      simp only [Function.iterate_zero, id] at h
      have hcd := Option.some.inj h
      subst hcd
      exact ⟨0, C0, Runs.refl _ C0, hs, by simp⟩
  | N + 1, c, d, C0, h, hs => by
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
          obtain ⟨C1, r1, hs1⟩ := step_sim tm ein eout c l hl C0 hs
          obtain ⟨n, C2, r2, hs2, hn⟩ := iter_sim N _ d C1 h hs1
          refine ⟨_, C2, Runs.trans r1 r2, hs2, ?_⟩
          have hc := stmtCost_le tm (tm.m l) c.var c.stk
          have hm := stmtSize_le_max tm l
          have hb : stmtCost tm (tm.m l) c.var c.stk ≤ stepBound tm := by
            unfold stepBound
            exact hc.trans (Nat.mul_le_mul_left _ hm)
          rw [Nat.add_mul, Nat.one_mul]
          omega

end Exec

end NearCubicWires.Bindings.Sim
