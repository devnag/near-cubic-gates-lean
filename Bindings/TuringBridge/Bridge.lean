import Bindings.TuringBridge.InputOutput
import Proof.Foundations.SourceCore

/-! # The bridge: Mathlib's standard TM model ⇒ the repo's ordinary word functions, linear overhead

`tm2ToOrdinary` turns any `Turing.TM2ComputableInTime ea eb f` with Boolean input and output
alphabets (Mathlib, `Computability/TuringMachine/Computable.lean`: a finite multi-stack machine
`FinTM2`, input on stack `k₀` via `initList`, halting with the output on stack `k₁` via
`haltList`, within `time (ea a).length` applications of `FinTM2.step`) into the repo's
`RepairSource.OrdinaryWordFunction α ea (fun a => eb (f a)) budget`
(`Proof/Foundations/SourceCore.lean`, `= RepairOrdinary.WordFunction`, `Proof/Foundations/OrdinaryMachine.lean`):
one finite-control local bit multitape machine that, started on `frame (ea a)`, halts within
`budget a` steps with the output tape EQUAL to `eb (f a)`, where

  `budget a = simConstant tm * (time (ea a).length + (ea a).length + (eb (f a)).length + 1)`,

  `simConstant tm = (2·B + 3) · maxStmtSize tm + 3·B + 7`,  `B = codeWidth tm = 2 + |Pt tm| · |σ|`,

with `Pt tm` the statement subtrees of the program (`|Pt tm| ≤ Σ_l stmtSize (tm.m l)`) and
`maxStmtSize tm` the largest statement tree. The overhead is LINEAR in the TM2 time: one TM2 step
(a whole statement tree, `TM2.stepAux`) costs at most `(2B+3)·maxStmtSize` bit-machine steps.
-/

namespace NearCubicWires.Bindings.Sim
open LocalBitMultitape RepairOrdinary Turing StateTransition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The explicit simulation constant (depends only on the machine). -/
noncomputable def simConstant (tm : FinTM2) : ℕ := stepBound tm + 3 * codeWidth tm + 7

theorem simConstant_eq (tm : FinTM2) :
    simConstant tm = (2 * codeWidth tm + 3) * maxStmtSize tm + 3 * codeWidth tm + 7 := rfl

theorem codeWidth_eq (tm : FinTM2) :
    codeWidth tm = 2 + Fintype.card (Pt tm) * Fintype.card tm.σ := by
  simp [codeWidth, Fintype.card_sum, Fintype.card_prod]

section Bridge
variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)

/-- The repo program. -/
noncomputable def program : Program where
  tapeCount := nT tm
  stateCount := Fintype.card (C tm)
  twoTapes := by show 2 ≤ Fintype.card tm.K + 3; omega
  machine := machine tm ein eout
  outputTape := outTape tm
  outputFresh := outTape_ne_zero tm

theorem budget_arith (B SB n m T e : ℕ) (he : e ≤ T * SB) :
    n * (B + 4) + 1 + (n * (2 * B + 3) + 1) + e + (m * (B + 2) + 1) ≤
      (SB + 3 * B + 7) * (T + n + m + 1) := by
  nlinarith [Nat.zero_le (SB * n), Nat.zero_le (SB * m), Nat.zero_le (B * T), Nat.zero_le (B * m),
    Nat.zero_le SB, Nat.zero_le (B * n), Nat.zero_le T, Nat.zero_le m]

/-- **The whole run.** From the framed input, the bit machine halts with the output tape equal to
the output word, within `simConstant · (T + |w| + |out| + 1)` steps. -/
theorem run_of_outputs (w out : List Bool) (T : ℕ)
    (h : TM2OutputsInTime tm (w.map ein.invFun) (some (out.map eout.invFun)) T) :
    ∃ n C', Runs (machine tm ein eout) n
        (initialConfiguration (machine tm ein eout) ((program tm ein eout).inputTapes w)) C' ∧
      (machine tm ein eout).halted C'.control = true ∧ C'.tapes (outTape tm) = out ∧
      n ≤ simConstant tm * (T + w.length + out.length + 1) := by
  set C0 := initialConfiguration (machine tm ein eout) ((program tm ein eout).inputTapes w) with hC0
  have hin : ∀ j : Fin (nT tm), j.val ≠ 0 → C0.tapes j = [] := by
    intro j hj
    simp [hC0, initialConfiguration, program, Program.inputTapes, hj]
  -- loading invariant at the start
  have hinv0 : LoadInv tm w 0 C0 := by
    refine ⟨by simp [hC0, initialConfiguration, program, Program.inputTapes, inTape],
      by simp [hC0, initialConfiguration], by simp [hC0, initialConfiguration], ?_, ?_, ?_, ?_⟩
    · rw [hin (tmpTape tm) (by simp [tmpTape])]
      simpa [loadCodes] using agrees_nil_lay (enc tm)
    · intro k
      exact ⟨by simp [hC0, initialConfiguration],
        hin _ (by simp [stkTape])⟩
    · exact hin _ (outTape_ne_zero tm)
    · simp [hC0, initialConfiguration]
  obtain ⟨C1, r1, hinv1, hc1⟩ :=
    scan_loop tm ein eout w w.length 0 C0 (by simp) (by rw [hC0]; rfl) hinv0
  have r2 := scan_end tm ein eout w C1 hc1 hinv1
  obtain ⟨_, _, hth1, hta1, hfr1⟩ := hinv1
  obtain ⟨C3, r3, hc3, hh3, ha3, hoth3⟩ :=
    transfer_loop tm ein eout (loadCodes tm w w.length) []
      ⟨code tm (.at (.popAt (tmpTape tm) .tr)), C1.heads, C1.tapes⟩ rfl
      (by simpa [loadCodes_length tm w w.length le_rfl] using hth1) hta1
      (by simpa using (hfr1.1 tm.k₀).1) (by rw [(hfr1.1 tm.k₀).2]; exact agrees_nil_lay (enc tm))
  have hfull : (loadCodes tm w w.length).reverse ++ [] = w.map Sum.inl := by
    simp [loadCodes, List.map_reverse]
  have hother : ∀ k, k ≠ tm.k₀ →
      C3.heads (stkTape tm k) = 0 ∧ C3.tapes (stkTape tm k) = [] := by
    intro k hk
    have hne : stkTape tm k ≠ stkTape tm tm.k₀ := fun he => hk (stkTape_injective tm he)
    rw [(hoth3 _ (stkTape_ne_tmp tm k) hne).1, (hoth3 _ (stkTape_ne_tmp tm k) hne).2]
    exact hfr1.1 k
  have hsim : SimRel tm ein (initList tm (w.map ein.invFun)) C3 := by
    refine ⟨?_, fun k => ?_, ?_, ?_⟩
    · rw [hc3]
      simp [ctlOf, initList, mkPt_of_mem tm (mem_allStmts_self tm tm.main), mainPt]
    · by_cases hk : k = tm.k₀
      · subst hk
        refine ⟨w.map Sum.inl, ?_, ?_, ?_⟩
        · simp [initList, List.map_map, Function.comp_def, val_inl_k₀]
        · rw [hh3, hfull]
        · rw [← hfull]; exact ha3
      · refine ⟨[], by simp [initList, hk], by simp [(hother k hk).1], ?_⟩
        rw [(hother k hk).2]
        exact agrees_nil_lay (enc tm)
    · rw [(hoth3 _ (tmpTape_ne_out tm).symm (stkTape_ne_out tm tm.k₀).symm).2]
      exact hfr1.2.1
    · rw [(hoth3 _ (tmpTape_ne_out tm).symm (stkTape_ne_out tm tm.k₀).symm).1]
      exact hfr1.2.2
  -- the TM2 run
  obtain ⟨n4, C4, r4, hsim4, hn4⟩ :=
    iter_sim tm ein eout h.steps _ (haltList tm (out.map eout.invFun)) C3 h.evals_in_steps hsim
  obtain ⟨hc4, hrel4, hout4, houth4⟩ := hsim4
  obtain ⟨cs, hmap, hh, ha⟩ := hrel4 tm.k₁
  have hmap' : cs.map (val tm ein tm.k₁) = (out.map eout.symm).map some := by
    simpa [haltList] using hmap
  have hlen : cs.length = out.length := by
    have := congrArg List.length hmap'
    simpa using this
  obtain ⟨C5, r5, hc5, ht5⟩ := out_loop tm ein eout cs [] C4
    (by rw [hc4]; simp [ctlOf, haltList]) (by simpa [haltList] using hh)
    (by simpa [haltList] using ha) hout4 houth4
  refine ⟨_, C5, Runs.trans (Runs.trans (Runs.trans (Runs.trans r1 r2) r3) r4) r5, ?_, ?_, ?_⟩
  · rw [hc5]; exact machine_halted_done tm ein eout
  · rw [ht5, List.nil_append]
    exact outBit_map tm ein eout cs out hmap'
  · have he : n4 ≤ T * stepBound tm :=
      hn4.trans (Nat.mul_le_mul_right _ h.steps_le_m)
    have := budget_arith (codeWidth tm) (stepBound tm) w.length out.length T n4 he
    rw [hlen]
    simpa [simConstant, loadCodes_length tm w w.length le_rfl] using this

end Bridge

/-- **The bridge.** A Mathlib `TM2ComputableInTime` machine with Boolean alphabets is an ordinary
word function of the repo, at linear overhead `simConstant · (T + |input| + |output| + 1)`. -/
noncomputable def tm2ToOrdinary {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInTime ea eb f) :
    RepairSource.OrdinaryWordFunction α ea (fun a => eb (f a))
      (fun a => simConstant h.tm * (h.time (ea a).length + (ea a).length + (eb (f a)).length + 1))
    where
  program := program h.tm h.inputAlphabet h.outputAlphabet
  realizes := by
    intro a
    obtain ⟨n, C', hr, hhalt, hout, hn⟩ :=
      run_of_outputs h.tm h.inputAlphabet h.outputAlphabet (ea a) (eb (f a)) _ (h.outputsFun a)
    obtain ⟨r, hrun, hfin⟩ := hr.runFrom hhalt
      (simConstant h.tm * (h.time (ea a).length + (ea a).length + (eb (f a)).length + 1) - n)
    refine ⟨r, ?_, ?_⟩
    · rw [Nat.add_sub_cancel' hn] at hrun
      exact hrun
    · rw [hfin]
      exact hout

/-- The bridge as an existence statement: some constant `C` (depending only on the machine). -/
theorem tm2_to_ordinary {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInTime ea eb f) :
    ∃ C : ℕ, Nonempty (RepairSource.OrdinaryWordFunction α ea (fun a => eb (f a))
      (fun a => C * (h.time (ea a).length + (ea a).length + (eb (f a)).length + 1))) :=
  ⟨simConstant h.tm, ⟨tm2ToOrdinary h⟩⟩

/-- The polynomial-time form (`TM2ComputableInPolyTime`), budget at the polynomial's value. -/
noncomputable def tm2PolyToOrdinary {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    RepairSource.OrdinaryWordFunction α ea (fun a => eb (f a))
      (fun a => simConstant h.tm *
        (h.time.eval (ea a).length + (ea a).length + (eb (f a)).length + 1)) :=
  tm2ToOrdinary h.toTM2ComputableInTime

/-- Non-vacuity: Mathlib's identity machine on Boolean words (`idComputableInPolyTime`) is an
instance of the hypothesis, so the bridge produces an actual ordinary word function. -/
theorem identity_nonvacuous : ∃ budget : List Bool → ℕ,
    Nonempty (RepairSource.OrdinaryWordFunction (List Bool) (fun w => w) (fun w => w) budget) :=
  ⟨_, ⟨tm2PolyToOrdinary (idComputableInPolyTime (fun w : List Bool => w))⟩⟩

end NearCubicWires.Bindings.Sim
