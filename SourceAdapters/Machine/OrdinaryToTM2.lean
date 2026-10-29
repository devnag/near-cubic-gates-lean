import SourceAdapters.Machine.StackRun
import SourceAdapters.Joins.OrdinaryToTM2

/-!
# X1: an ordinary word function is a Mathlib TM2 machine

`app:short-pcp-proof`, "The exact Lean interface": "A fixed multitape implementation can be simulated by finitely many stacks in polynomial time,
giving the Mathlib TM2 machine required by the interface; clearing work stacks and restoring its final control
state also take polynomial time."
`app:sources`, "Full-range amplification interface": "The usual polynomial-overhead simulation into TM2 preserves this bound."

`stackMachine_reach` is the whole run: from Mathlib's `initList` on the RAW input `w` the machine reaches
Mathlib's `haltList` on the ordinary output in at most `9 · (|w| + fuel + 1)` steps (linear overhead):
framing `2|w| + 2`, simulation one step per ordinary step, output transfer and cleanup at most `3·(2|w| + 2s + 2)`.
The join theorems `ordinaryToTM2InTime` and `ordinaryToTM2PolyTime` (`Joins/OrdinaryToTM2.lean`) follow.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Machine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary Turing

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]; omega

theorem initList_stackMachine (p : Program) (w : List Bool) :
    initList (stackMachine p) w =
      (⟨some .frameRev, Var.init _, stackOf w [] (fun _ => ([], []))⟩ : SCfg p.tapeCount p.stateCount) := by
  simp only [initList, stackMachine]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_stackMachine (p : Program) (out : List Bool) :
    haltList (stackMachine p) out =
      (⟨none, Var.init _, stackOf [] out (fun _ => ([], []))⟩ : SCfg p.tapeCount p.stateCount) := by
  simp only [haltList, stackMachine]
  congr 1
  funext k
  cases k <;> rfl

/-- **The whole run** (`app:short-pcp-proof`, "The exact Lean interface"): framing front end, step-by-step simulation, output transfer, cleanup to
`haltList`, within `9 · (|w| + fuel + 1)` TM2 steps. -/
theorem stackMachine_reach (p : Program) (w out : List Bool) (fuel : ℕ)
    (r : ExecutionReceipt p.tapeCount p.stateCount)
    (hr : run p.machine fuel (p.inputTapes w) = some r) (hout : r.final.tapes p.outputTape = out) :
    ∃ n ≤ 9 * (w.length + fuel + 1),
      Reach (stackMachine p).step (initList (stackMachine p) w) (some (haltList (stackMachine p) out)) n := by
  set M := p.machine
  set t0 := tape0 p
  set o := p.outputTape
  set tp0 : Fin p.tapeCount → List (Option Bool) × List (Option Bool) := fun _ => ([], [])
  show ∃ n ≤ _, Reach (sstep M t0 o) _ _ n
  rw [initList_stackMachine, haltList_stackMachine]
  -- framing
  obtain ⟨v1, h1⟩ := frameRev_run M t0 o w (Var.init _) [] tp0 [] rfl
  obtain ⟨v2, h2⟩ := frameEmit_run M t0 o w.reverse v1 [] []
    (Function.update tp0 t0 ((w.map some).reverse ++ [], [some false])) [some false]
    (by simp [List.map_reverse])
  set tpA : Fin p.tapeCount → List (Option Bool) × List (Option Bool) :=
    Function.update tp0 t0 ([], (frame w).map some) with htpA
  have hA : Function.update (Function.update tp0 t0 ((w.map some).reverse ++ [], [some false])) t0
      ([], frameCells w.reverse.reverse [some false]) = tpA := by
    simp [htpA, frameCells_false]
  rw [hA] at h2
  -- the initial ordinary configuration is represented
  set c0 := initialConfiguration M (p.inputTapes w)
  have hrep0 : ∀ j, TapeRep (tpA j) (c0.tapes j) (c0.heads j) := by
    intro j
    by_cases hj : j = t0
    · subst hj
      refine ⟨?_, rfl⟩
      simp [htpA, c0, initialConfiguration, Program.inputTapes, t0, tape0, decode_map_some]
    · have hj' : j.val ≠ 0 := fun h => hj (Fin.ext (by simp [t0, tape0, h]))
      refine ⟨?_, ?_⟩
      · simp [htpA, hj, tp0, c0, initialConfiguration, Program.inputTapes, hj']
      · simp [htpA, hj, tp0, c0, initialConfiguration]
  have hsz0 : ∀ j, (tpA j).1.length + (tpA j).2.length ≤ 2 * w.length + 1 := by
    intro j
    by_cases hj : j = t0
    · subst hj; simp [htpA, frame_length]
    · simp [htpA, hj, tp0]
  -- simulation
  obtain ⟨v3, tp3, h3, hrep3, hsz3, hhalt, hle⟩ :=
    sim_run M t0 o fuel c0 r hr v2 tpA (2 * w.length + 1) hrep0 hsz0
  have h4 := halted_step M t0 o r.final.control hhalt v3 (stackOf [] [] tp3)
  -- output transfer
  obtain ⟨v5, h5⟩ := gather_run M t0 o (tp3 o).2 (tp3 o).1 v3 [] [] tp3 rfl
  set A := (tp3 o).2.reverse ++ (tp3 o).1 with hAdef
  obtain ⟨v6, h6⟩ := emit_run M t0 o A v5 [] [] (Function.update tp3 o (A, [])) (by simp)
  have hdec : A.foldl (fun d c => consCell c d) [] = out := by
    have := foldl_consCell_reverse ((tp3 o).1.reverse ++ (tp3 o).2)
    rw [List.reverse_append, List.reverse_reverse] at this
    rw [hAdef, this, (hrep3 o).1, hout]
  rw [hdec] at h6
  -- cleanup
  set m := 2 * w.length + 1 + 2 * r.steps
  obtain ⟨n7, hn7, h7⟩ := wipe_run M t0 o m v6 [] out (Function.update (Function.update tp3 o (A, [])) o ([], []))
    (by
      intro j
      by_cases hj : j = o
      · subst hj; simp
      · have := hsz3 j; simp [hj]; omega)
  have hRo : (tp3 o).2.length ≤ m := by have := hsz3 o; omega
  have hAo : A.length ≤ m := by have := hsz3 o; simp [hAdef]; omega
  refine ⟨_, ?_, Reach.trans h1 (Reach.trans h2 (Reach.trans h3 (Reach.trans (Reach.single h4)
    (Reach.trans h5 (Reach.trans h6 h7)))))⟩
  have := frame_length w
  have := List.length_reverse (as := w)
  omega

theorem map_refl_inp (p : Program) (w : List Bool) :
    (List.map (Equiv.refl Bool).invFun w : List ((stackMachine p).Γ (stackMachine p).k₀)) = w :=
  List.map_id w

theorem map_refl_out (p : Program) (w : List Bool) :
    (List.map (Equiv.refl Bool).invFun w : List ((stackMachine p).Γ (stackMachine p).k₁)) = w :=
  List.map_id w

/-- The Mathlib `TM2ComputableInTime` structure of a budgeted ordinary word function (linear time). -/
noncomputable def tm2InTime {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {budget : α → ℕ} (W : WordFunction α ea (fun a => eb (f a)) budget) (B : ℕ → ℕ)
    (hB : ∀ a, budget a ≤ B (ea a).length) : TM2ComputableInTime ea eb f where
  tm := stackMachine W.program
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time n := 9 * (n + B n + 1)
  outputsFun a := Classical.choice (by
    obtain ⟨r, hr, hout⟩ := W.realizes a
    obtain ⟨n, hn, hR⟩ := stackMachine_reach W.program (ea a) (eb (f a)) (budget a) r hr hout
    rw [map_refl_inp, map_refl_out]
    exact ⟨⟨⟨n, hR⟩, show n ≤ _ by have := hB a; omega⟩⟩)

theorem tm2InTime_time {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {budget : α → ℕ} (W : WordFunction α ea (fun a => eb (f a)) budget) (B : ℕ → ℕ)
    (hB : ∀ a, budget a ≤ B (ea a).length) (n : ℕ) : (tm2InTime W B hB).time n = 9 * (n + B n + 1) := rfl

/-- **X1, explicit-time form** (the join `Joins.OrdinaryToTM2InTime`; `app:sources`, "Full-range amplification interface", `app:short-pcp-proof`, "The exact Lean interface"). -/
theorem ordinaryToTM2InTime : Joins.OrdinaryToTM2InTime := by
  intro α β ea eb f budget B hW hB
  obtain ⟨W⟩ := hW
  refine ⟨9, 1, tm2InTime W B hB, fun n => ?_⟩
  rw [tm2InTime_time, pow_one]
  omega

theorem poly_bound (K e n : ℕ) :
    9 * (n + K * (n + 1) ^ e + 1) ≤ 9 * (K + 1) * (n + 1) ^ (e + 1) := by
  have h1 : n + 1 ≤ (n + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
  have h2 : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : K * (n + 1) ^ e ≤ K * (n + 1) ^ (e + 1) := Nat.mul_le_mul_left _ h2
  nlinarith

/-- **X1, polynomial form** (the join `Joins.OrdinaryToTM2PolyTime`; `app:sources`, "Uniform three-query PCPP and code interfaces",, `app:short-pcp-proof`, "The exact Lean interface"). -/
theorem ordinaryToTM2PolyTime : Joins.OrdinaryToTM2PolyTime := by
  intro α β ea eb f budget hW hK
  obtain ⟨W⟩ := hW
  obtain ⟨K, e, hK⟩ := hK
  let M := tm2InTime W (fun n => K * (n + 1) ^ e) hK
  refine ⟨{ toTM2ComputableAux := M.toTM2ComputableAux
            time := Polynomial.C (9 * (K + 1)) * (Polynomial.X + 1) ^ (e + 1)
            outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo, ?_⟩ }⟩
  refine le_trans (M.outputsFun a).steps_le_m ?_
  simp only [M, tm2InTime_time, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact poly_bound K e _

end NearCubicGates.Adapters.Machine
