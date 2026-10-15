import Proof.MachineModel.OrdinaryOracleComposeHandoff

/-! Closed ordinary-oracle sequential composition from the literal source
run contracts. The five executed calls pay for both resets, both framed
copies, shared-query erasure, and every finite-control handoff. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compose_runs {o : ℕ → Bool} {p q : OrdinaryOracleProgram}
    {input middle output : List Bool} {b1 b2 : ℕ}
    (h1 : OrdinaryOracleRuns o p input middle b1)
    (h2 : OrdinaryOracleRuns o q middle output b2) :
    OrdinaryOracleRuns o (compose p q) input output (16 * (b1 + b2 + 1)) := by
  classical
  obtain ⟨c1, n1, f1, hc1, hn1, tr1, halt1, out1, heads1, clock1, _log1, query1, width1⟩ :=
    clocked_runs h1
  obtain ⟨c2, n2, f2, hc2, hn2, tr2, halt2, out2, heads2, _clock2, _log2, _query2, width2⟩ :=
    clocked_runs h2
  let startTapes := (compose p q).base.inputTapes input
  let a := install (firstSlot p q) startTapes f1.tapes
  have ra : Ready o ((ports p q).program (pieces p q 0)) (c1 + n1 + 2) startTapes a := by
    have h : Ready o (clocked p) (c1 + n1 + 2) ((clocked p).base.inputTapes input) f1.tapes :=
      ⟨f1, tr1, halt1, heads1, rfl⟩
    exact h.focus (ports p q) (firstSlot p q) (first_injective p q) rfl startTapes
      (by intro i; simp [startTapes, Program.inputTapes, firstSlot])
  have afirst (i : Fin (clocked p).base.tapeCount) : a (firstSlot p q i) = f1.tapes i :=
    install_slot _ (first_injective p q) _ _ i
  have aextra (j : Fin 4) : a (extraSlot p q j) = [] := by
    rw [show a (extraSlot p q j) = startTapes (extraSlot p q j) from
      install_other _ _ _ _ (fun i => first_ne_extra p q i j)]
    have hp := (clocked p).base.twoTapes
    simp [startTapes, Program.inputTapes, extraSlot, show (clocked p).base.tapeCount ≠ 0 by omega]
  have asecond (j : Fin (clocked q).base.tapeCount) (hj : j ≠ (clocked q).queryTape) :
      a (secondSlot p q j) = [] := by
    rw [show a (secondSlot p q j) = startTapes (secondSlot p q j) from
      install_other _ _ _ _ (fun i h => hj ((banks_meet p q i j).mp h).2)]
    have hp := (clocked p).base.twoTapes
    simp [startTapes, Program.inputTapes, secondSlot, hj, show (clocked p).base.tapeCount ≠ 0 by omega]
  let b := Function.update (Function.update a (secondSlot p q (zeroTape q)) (frame middle))
    (extraSlot p q 0) (List.replicate (2 * middle.length + 1) false)
  have rb : Ready o ((ports p q).program (pieces p q 1)) (4 * middle.length + 4) a b := by
    apply Ready.ordinary (ports p q)
    exact copy_ready (copySlots p q) (copy_injective p q) a middle []
      (by simpa [copySlots] using (afirst (clocked p).base.outputTape).trans out1)
      (asecond (zeroTape q) (zero_ne_query q)) (aextra 0)
  have first_ne_second_zero (i : Fin (clocked p).base.tapeCount) :
      firstSlot p q i ≠ secondSlot p q (zeroTape q) := by
    intro h
    exact zero_ne_query q ((banks_meet p q _ _).mp h).2
  have bfirst (i : Fin (clocked p).base.tapeCount) : b (firstSlot p q i) = f1.tapes i := by
    simp only [b, Function.update_apply, first_ne_extra p q i 0, first_ne_second_zero i, if_false]
    exact afirst i
  have bextra (j : Fin 4) (hj : j ≠ 0) : b (extraSlot p q j) = [] := by
    have he : extraSlot p q j ≠ extraSlot p q 0 := fun h => hj (extra_injective p q h)
    simp only [b, Function.update_apply, he, Ne.symm (second_ne_extra p q (zeroTape q) j), if_false]
    exact aextra j
  let c := Function.update (Function.update b (firstSlot p q (clocked p).queryTape)
    (List.replicate n1 false)) (extraSlot p q 1) (List.replicate (n1 + 1) false)
  have rc : Ready o ((ports p q).program (pieces p q 2)) (2 * n1 + 4) b c := by
    apply Ready.ordinary (ports p q)
    exact clear_ready (clearSlots p q) (clear_injective p q) b n1
      (by simpa [clearSlots, bfirst] using query1)
      ((bfirst (clockTape p)).trans clock1) (bextra 1 (by decide))
  let caps : Fin (clocked q).base.tapeCount → ℕ := fun i =>
    if i = (clocked q).queryTape then n1 else 0
  have csecond (j : Fin (clocked q).base.tapeCount) : c (secondSlot p q j) =
      ZeroPadding.pad (caps j) (((clocked q).base.inputTapes middle) j) := by
    have he1 := second_ne_extra p q j 1
    have he0 := second_ne_extra p q j 0
    by_cases hj : j = (clocked q).queryTape
    · subst j
      simp [c, second_query, Function.update, first_ne_extra, caps,
        Program.inputTapes, (clocked q).queryFresh, ZeroPadding.pad]
    · have hq : secondSlot p q j ≠ firstSlot p q (clocked p).queryTape := by
        intro h
        exact hj ((banks_meet p q _ _).mp h.symm).2
      have hj0 : j = zeroTape q ↔ j.val = 0 := by
        constructor
        · intro h; exact congrArg Fin.val h
        · intro h; exact Fin.ext h
      have hslots : secondSlot p q j = secondSlot p q (zeroTape q) ↔ j = zeroTape q :=
        ⟨fun h => second_injective p q h, congrArg (secondSlot p q)⟩
      simp only [c, b, Function.update_apply, he1, hq, he0, if_false, hslots, hj0,
        caps, hj, ZeroPadding.pad_zero, Program.inputTapes, asecond j hj]
  have cextra (j : Fin 4) (hj0 : j ≠ 0) (hj1 : j ≠ 1) : c (extraSlot p q j) = [] := by
    have he1 : extraSlot p q j ≠ extraSlot p q 1 := fun h => hj1 (extra_injective p q h)
    simp only [c, Function.update_apply, he1,
      Ne.symm (first_ne_extra p q (clocked p).queryTape j), if_false]
    exact bextra j hj0
  let d := install (secondSlot p q) c (fun j => ZeroPadding.pad (caps j) (f2.tapes j))
  have rd : Ready o ((ports p q).program (pieces p q 3)) (c2 + n2 + 2) c d := by
    have h : Ready o (clocked q) (c2 + n2 + 2) ((clocked q).base.inputTapes middle) f2.tapes :=
      ⟨f2, tr2, halt2, heads2, rfl⟩
    exact (h.padding caps).focus (ports p q) (secondSlot p q) (second_injective p q)
      (second_query p q) c csecond
  have dsecond : d (secondSlot p q (clocked q).base.outputTape) =
      ZeroPadding.pad (caps (clocked q).base.outputTape) (frame output) := by
    exact (install_slot _ (second_injective p q) _ _ _).trans
      (congrArg (ZeroPadding.pad (caps (clocked q).base.outputTape)) out2)
  have dextra (j : Fin 4) (hj0 : j ≠ 0) (hj1 : j ≠ 1) : d (extraSlot p q j) = [] := by
    exact (install_other _ _ _ _ (fun i => second_ne_extra p q i j)).trans (cextra j hj0 hj1)
  let e := Function.update (Function.update d (extraSlot p q 3) (frame output))
    (extraSlot p q 2) (List.replicate (2 * output.length + 1) false)
  have re : Ready o ((ports p q).program (pieces p q 4)) (4 * output.length + 4) d e := by
    apply Ready.ordinary (ports p q)
    exact copy_ready (outputSlots p q) (output_injective p q) d output
      (List.replicate (caps (clocked q).base.outputTape - (frame output).length) false)
      dsecond (dextra 3 (by decide) (by decide)) (dextra 2 (by decide) (by decide))
  have ta := ra.call (ports p q) (pieces p q) 0 (next p q) 0 1 (by intro state; rfl)
  have tb := rb.call (ports p q) (pieces p q) 0 (next p q) 1 2 (by intro state; rfl)
  have tc := rc.call (ports p q) (pieces p q) 0 (next p q) 2 3 (by intro state; rfl)
  have td := rd.call (ports p q) (pieces p q) 0 (next p q) 3 4 (by intro state; rfl)
  have te := re.stop (ports p q) (pieces p q) 0 (next p q) 4 (by intro state; rfl)
  have total := trans (trans (trans (trans ta tb) tc) td) te
  refine ⟨_, _, ?_, total, ?_, ?_⟩
  · simp only [frame_length] at width1 width2
    omega
  · simp [RecoveryCalls.stopped, compose, graph, RecoveryCalls.machine]
  · change e (extraSlot p q 3) = frame output
    have he : extraSlot p q 3 ≠ extraSlot p q 2 := by
      intro h
      have hc := extra_injective p q h
      exact (by decide : (3 : Fin 4) ≠ 2) hc
    simp [e, Function.update, he]

end NearCubicWires.RepairSource.OrdinaryOracleCompose
