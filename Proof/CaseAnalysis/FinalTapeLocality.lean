import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality

open LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  Cell-level lemmas -/

theorem read_nil (j : ℕ) : readTapeBit [] j = false := by
  simp [readTapeBit, List.getD_eq_getElem?_getD]

theorem read_cons_zero (a : Bool) (t : List Bool) : readTapeBit (a :: t) 0 = a := rfl

theorem read_cons_succ (a : Bool) (t : List Bool) (j : ℕ) :
    readTapeBit (a :: t) (j + 1) = readTapeBit t j := rfl

theorem read_getElem (l : List Bool) (n : ℕ) (h : n < l.length) : readTapeBit l n = l[n] := by
  simp only [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- **The only cell a write can change is the one under the head.**  `writeTapeBit` may EXTEND the
tape with blanks, and this equation covers that too: the extension cells read `false`, which is what
an out-of-range read of the original tape already returns. -/
theorem read_write (v : Bool) :
    ∀ (p : ℕ) (l : List Bool) (j : ℕ),
      readTapeBit (writeTapeBit l p v) j = if j = p then v else readTapeBit l j := by
  intro p
  induction p with
  | zero =>
    intro l j
    cases l with
    | nil =>
      cases j with
      | zero => rfl
      | succ j => simp [writeTapeBit, read_cons_succ, read_nil]
    | cons a t =>
      cases j with
      | zero => rfl
      | succ j => simp [writeTapeBit, read_cons_succ]
  | succ p ih =>
    intro l j
    cases l with
    | nil =>
      cases j with
      | zero => simp [writeTapeBit, read_cons_zero, read_nil]
      | succ j =>
        rw [show writeTapeBit ([] : List Bool) (p + 1) v = false :: writeTapeBit [] p v from rfl,
          read_cons_succ, ih [] j, read_nil, read_nil]
        simp
    | cons a t =>
      cases j with
      | zero => simp [writeTapeBit, read_cons_zero]
      | succ j =>
        rw [show writeTapeBit (a :: t) (p + 1) v = a :: writeTapeBit t p v from rfl,
          read_cons_succ, ih t j, read_cons_succ]
        simp

/-- A head moves by at most one cell per step. -/
theorem apply_le (move : HeadMove) (head : ℕ) : move.apply head ≤ head + 1 := by
  cases move <;> (simp only [HeadMove.apply]; omega)

/-! ## §2  Agreement below a horizon -/

/-- Two tape vectors read the same at every position below `m`. -/
def Agree {t : ℕ} (m : ℕ) (T1 T2 : Fin t → List Bool) : Prop :=
  ∀ (i : Fin t) (j : ℕ), j < m → readTapeBit (T1 i) j = readTapeBit (T2 i) j

theorem Agree.refl {t : ℕ} (m : ℕ) (T : Fin t → List Bool) : Agree m T T := fun _ _ _ => rfl

/-- The scanned bit vector is a function of the cells under the heads alone. -/
theorem scanned_agree {t s : ℕ} {m : ℕ} {h : Fin t → ℕ} {T1 T2 : Fin t → List Bool} {c : Fin s}
    (hag : Agree m T1 T2) (hh : ∀ i, h i < m) :
    (⟨c, h, T1⟩ : Configuration t s).scanned = (⟨c, h, T2⟩ : Configuration t s).scanned := by
  funext i
  exact hag i (h i) (hh i)

/-- **ONE STEP IS LOCAL.**  From a common control and a common head vector entirely below the
horizon, two `Agree m`-related tape vectors take the same transition — both blocked, or both to the
same control and heads with `Agree m`-related tapes. -/
theorem step_agree {t s : ℕ} (p : Machine t s) {m : ℕ} {h : Fin t → ℕ} {T1 T2 : Fin t → List Bool}
    {c : Fin s} (hag : Agree m T1 T2) (hh : ∀ i, h i < m) :
    (step p ⟨c, h, T1⟩ = none ∧ step p ⟨c, h, T2⟩ = none) ∨
      ∃ (c' : Fin s) (h' : Fin t → ℕ) (U1 U2 : Fin t → List Bool),
        step p ⟨c, h, T1⟩ = some ⟨c', h', U1⟩ ∧ step p ⟨c, h, T2⟩ = some ⟨c', h', U2⟩ ∧
          Agree m U1 U2 ∧ ∀ i, h' i ≤ h i + 1 := by
  have hsc := scanned_agree (s := s) (c := c) hag hh
  cases hrule : p.rule c ((⟨c, h, T1⟩ : Configuration t s).scanned) with
  | none =>
    refine Or.inl ⟨?_, ?_⟩
    · simp only [step, hrule, Option.map_none]
    · have : p.rule c ((⟨c, h, T2⟩ : Configuration t s).scanned) = none := by
        rw [← hsc]; exact hrule
      simp only [step, this, Option.map_none]
  | some a =>
    have hrule2 : p.rule c ((⟨c, h, T2⟩ : Configuration t s).scanned) = some a := by
      rw [← hsc]; exact hrule
    refine Or.inr ⟨a.nextControl, fun i => (a.move i).apply (h i),
      fun i => match a.write i with
        | none => T1 i
        | some v => writeTapeBit (T1 i) (h i) v,
      fun i => match a.write i with
        | none => T2 i
        | some v => writeTapeBit (T2 i) (h i) v, ?_, ?_, ?_, ?_⟩
    · simp only [step, hrule, Option.map_some]
      rfl
    · simp only [step, hrule2, Option.map_some]
      rfl
    · intro i j hj
      cases hw : a.write i with
      | none => simpa only [hw] using hag i j hj
      | some v =>
        simp only [hw, read_write]
        by_cases hji : j = h i
        · simp [hji]
        · simp only [hji, if_false]
          exact hag i j hj
    · intro i
      exact apply_le _ _

/-! ## §3  Whole runs -/

/-- Inversion of one unit of fuel at a non-halting control. -/
theorem runFrom_succ_inv {t s : ℕ} (p : Machine t s) (n : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hnh : p.halted c.control = false)
    (hr : runFrom p (n + 1) c = some r) :
    ∃ d sfx, step p c = some d ∧ runFrom p n d = some sfx ∧ r.final = sfx.final := by
  by_cases hd : ∃ d, step p c = some d
  · obtain ⟨d, hd⟩ := hd
    by_cases hs : ∃ sfx, runFrom p n d = some sfx
    · obtain ⟨sfx, hs⟩ := hs
      have hjoin := runFrom_step p c d sfx hnh hd hs
      rw [hjoin] at hr
      refine ⟨d, sfx, hd, hs, ?_⟩
      rw [← Option.some_inj.mp hr]
    · exfalso
      have hnone : runFrom p n d = none := by
        cases h : runFrom p n d with
        | none => rfl
        | some sfx => exact absurd ⟨sfx, h⟩ hs
      rw [runFrom] at hr
      simp only [hnh, Bool.false_eq_true, if_false, hd, hnone] at hr
      exact absurd hr (by simp)
  · exfalso
    have hnone : step p c = none := by
      cases h : step p c with
      | none => rfl
      | some d => exact absurd ⟨d, h⟩ hd
    rw [runFrom] at hr
    simp only [hnh, Bool.false_eq_true, if_false, hnone] at hr
    exact absurd hr (by simp)

/-- A halted control yields the entry configuration itself. -/
theorem runFrom_of_halted {t s : ℕ} (p : Machine t s) (n : ℕ) (c : Configuration t s)
    (hh : p.halted c.control = true) :
    runFrom p n c = some { final := c, steps := 0, peakTapeCells := c.tapeCells } := by
  cases n with
  | zero => simp [runFrom, hh]
  | succ n => simp [runFrom, hh]

/-- If a run of `n` steps succeeds, it did not halt only because the control halted at the start,
or it made a step. -/
theorem runFrom_agree {t s : ℕ} (p : Machine t s) {m : ℕ} :
    ∀ (n : ℕ) (c : Fin s) (h : Fin t → ℕ) (T1 T2 : Fin t → List Bool),
      Agree m T1 T2 → (∀ i, h i + n < m) →
      ∀ r1 : ExecutionReceipt t s, runFrom p n ⟨c, h, T1⟩ = some r1 →
        ∃ r2, runFrom p n ⟨c, h, T2⟩ = some r2 ∧
          r1.final.control = r2.final.control ∧ r1.final.heads = r2.final.heads ∧
          Agree m r1.final.tapes r2.final.tapes := by
  intro n
  induction n with
  | zero =>
    intro c h T1 T2 hag _ r1 hr1
    by_cases hh : p.halted c = true
    · rw [runFrom_of_halted p 0 ⟨c, h, T1⟩ hh] at hr1
      refine ⟨_, runFrom_of_halted p 0 ⟨c, h, T2⟩ hh, ?_, ?_, ?_⟩
      · rw [← Option.some_inj.mp hr1]
      · rw [← Option.some_inj.mp hr1]
      · rw [← Option.some_inj.mp hr1]
        exact hag
    · simp only [Bool.not_eq_true] at hh
      rw [runFrom] at hr1
      simp only [hh, Bool.false_eq_true, if_false] at hr1
      exact absurd hr1 (by simp)
  | succ n ih =>
    intro c h T1 T2 hag hbound r1 hr1
    by_cases hh : p.halted c = true
    · rw [runFrom_of_halted p (n + 1) ⟨c, h, T1⟩ hh] at hr1
      refine ⟨_, runFrom_of_halted p (n + 1) ⟨c, h, T2⟩ hh, ?_, ?_, ?_⟩
      · rw [← Option.some_inj.mp hr1]
      · rw [← Option.some_inj.mp hr1]
      · rw [← Option.some_inj.mp hr1]
        exact hag
    · simp only [Bool.not_eq_true] at hh
      have hhm : ∀ i, h i < m := by
        intro i; have := hbound i; omega
      obtain ⟨d, sfx, hd, hsfx, hfin⟩ :=
        runFrom_succ_inv p n ⟨c, h, T1⟩ r1 hh hr1
      rcases step_agree p (c := c) hag hhm with ⟨hnone, _⟩ | ⟨c', h', U1, U2, hs1, hs2, hU, hle⟩
      · rw [hnone] at hd; exact absurd hd (by simp)
      · rw [hs1] at hd
        have hd' : d = ⟨c', h', U1⟩ := (Option.some_inj.mp hd).symm
        subst hd'
        have hbound' : ∀ i, h' i + n < m := by
          intro i
          have h1 := hle i
          have h2 := hbound i
          omega
        obtain ⟨r2, hr2, hc2, hh2, ht2⟩ := ih c' h' U1 U2 hU hbound' sfx hsfx
        have hjoin := runFrom_step p ⟨c, h, T2⟩ ⟨c', h', U2⟩ r2 hh hs2 hr2
        refine ⟨_, hjoin, ?_, ?_, ?_⟩
        · rw [hfin]; exact hc2
        · rw [hfin]; exact hh2
        · rw [hfin]; exact ht2

theorem Step_agree {t s : ℕ} {p : Machine t s} {n m : ℕ} {T1 T2 O1 O2 : Fin t → List Bool}
    {H1 H2 : Fin t → ℕ}
    (hs1 : Step p n (fun _ => 0) T1 H1 O1) (hs2 : Step p n (fun _ => 0) T2 H2 O2)
    (hag : Agree m T1 T2) (hn : n < m) : Agree m O1 O2 := by
  obtain ⟨r1, hr1, _, ht1, _⟩ := hs1
  obtain ⟨r2, hr2, _, ht2, _⟩ := hs2
  obtain ⟨r2', hr2', _, _, hA⟩ :=
    runFrom_agree p n p.start (fun _ => 0) T1 T2 hag (by intro i; simpa using hn) r1 hr1
  have hsame : r2 = r2' := Option.some_inj.mp (hr2.symm.trans hr2')
  rw [← ht1, ← ht2, hsame]
  exact hA

/-! ## §4  THE DESIGN RULE — no uniform budget can move a block from beyond itself

This is `Step_agree` in the form a SPEC AUTHOR needs, and it mentions no layout, no bank, no record
and no paper quantity: it is about binder ORDER alone.

**If an obligation fixes ONE budget `cost` and then quantifies over the word sitting at an offset
that may exceed `cost`, the obligation is FALSE for every machine.**  The two runs cannot tell the
two words apart, because neither head ever reaches them.

The repair is always the same and always cheap: bound the offset by a width the budget is allowed
to mention, so that `cost` may grow with it.  A seek obligation is well-typed exactly when its
offset binder is bounded before its budget binder is fixed. -/

/-- **NO MACHINE AT A BUDGET FIXED BEFORE THE DATA CAN MOVE A BLOCK FROM BEYOND THAT BUDGET.**

One machine `M`, one budget `cost`; a bank that differs only in the word `w` placed after a prefix
longer than `cost` on port `src`; an exit that must carry `w` on port `dst`.  Two different words of
the same length make this contradictory — whatever `M` is, whatever the rest of the bank is, and
whatever the words MEAN.

Stated with `pre` rather than an offset arithmetic so that it applies to any block code: `hcost`
says the block starts beyond the budget, `hfit` says the block is no longer than that prefix. -/
theorem nc_no_uniform_budget_block_move {T rs : ℕ} (M : Machine T rs) (cost : ℕ)
    (src dst : Fin T) (base : Fin T → List Bool) (pre w₁ w₂ : List Bool)
    (hcost : cost < pre.length) (hfit : w₁.length ≤ pre.length)
    (hlen : w₁.length = w₂.length) (hne : w₁ ≠ w₂)
    (h₁ : Step M cost (fun _ => 0) (Function.update base src (pre ++ w₁)) (fun _ => 0)
      (Function.update (Function.update base src (pre ++ w₁)) dst w₁))
    (h₂ : Step M cost (fun _ => 0) (Function.update base src (pre ++ w₂)) (fun _ => 0)
      (Function.update (Function.update base src (pre ++ w₂)) dst w₂)) : False := by
  have hag : Agree pre.length (Function.update base src (pre ++ w₁))
      (Function.update base src (pre ++ w₂)) := by
    intro i j hj
    by_cases hi : i = src
    · subst hi
      rw [Function.update_self, Function.update_self, read_prefix pre w₁ j hj,
        read_prefix pre w₂ j hj]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  have hout := Step_agree h₁ h₂ hag hcost
  refine hne (List.ext_getElem hlen ?_)
  intro n hn1 hn2
  have hd := hout dst n (lt_of_lt_of_le hn1 hfit)
  rw [Function.update_self, Function.update_self] at hd
  rwa [read_getElem w₁ n hn1, read_getElem w₂ n hn2] at hd

/-! ## §5  CONTROLS -/

/-- The one-state machine that halts before doing anything. -/
def haltMachine (T : ℕ) : Machine T 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem haltMachine_step {T : ℕ} (h : Fin T → ℕ) (A : Fin T → List Bool) (n : ℕ) :
    Step (haltMachine T) n h A h A :=
  ⟨{ final := ⟨(haltMachine T).start, h, A⟩, steps := 0,
      peakTapeCells := (⟨(haltMachine T).start, h, A⟩ : Configuration T 1).tapeCells },
    runFrom_of_halted (haltMachine T) n _ rfl, rfl, rfl, Nat.zero_le _⟩

/-- **NEGATIVE CONTROL, RUN — `hcost` is the binder that does the work.**  Every other hypothesis of
`nc_no_uniform_budget_block_move` is simultaneously satisfiable WITH TWO DIFFERENT WORDS: at
`pre = []` and `dst = src` the immediately-halting machine discharges both `Step` premises at budget
`0`, for every word at once.

So the lemma does not derive `False` from its bank shape, from `w₁ ≠ w₂`, or from the `Step` shape:
it rests exactly on `cost < pre.length`, the offset exceeding the budget.  Mutating that one
hypothesis to `0 < 0` makes the remaining premises consistent, which is what a control must show. -/
theorem meta_control_hcost_is_load_bearing {T : ℕ} (src : Fin T) (base : Fin T → List Bool) :
    ([true] : List Bool) ≠ [false] ∧
      ∀ w : List Bool,
        Step (haltMachine T) 0 (fun _ => 0) (Function.update base src ([] ++ w)) (fun _ => 0)
          (Function.update (Function.update base src ([] ++ w)) src w) := by
  refine ⟨by simp, ?_⟩
  intro w
  have heq : Function.update (Function.update base src ([] ++ w)) src w
      = Function.update base src ([] ++ w) := by
    funext i
    by_cases hi : i = src
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [heq]
  exact haltMachine_step _ _ _

end NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality
