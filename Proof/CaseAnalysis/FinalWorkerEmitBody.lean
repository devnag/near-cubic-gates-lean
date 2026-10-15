import Proof.CaseAnalysis.FinalWorkerEmitLoader

/-! # W2 -- the estimator body, closed to ONE loader

Paper C.10.1 (paper.tex 4130):

> In addition to validity, the machine estimates `mu = E_{i,u} F_i(u)` **by
> expanding it into AND-four supplier calls**, and accepts a branch only if
> `mu~ >= theta_acc := (c_p + s_p)/2`.

`RepairCloseoutFinalC10WorkerDockBody.body_runs` closes the body to TWO loader
hypotheses.  The second (`hemit`) is refuted as written
(`CloseoutFinalC10WorkerEmitShape.emit_over_arbitrary_exit_refuted`) and
discharged in its corrected form by an actual machine
(`CloseoutFinalC10WorkerEmitLoader.emit_loader_step`).  This module joins the
two: `body_runs_of_loader` produces `BodyRuns` -- hence `EstimatorBody` --
from ONE hypothesis, the prologue that turns P4's gate exit into the ready
bank.

`dock_exit` is `RepairCloseoutFinalC10WorkerDock.dock_step` with the two
projections the emit loader needs and which the existential of `dock_step`
hides: the exit heads are zero away from the fold's source tape `76` and its
unread driver tape `186`, and the twenty-nine answer slots `187 .. 215` come
through the docked multiply stage and the docked fold untouched.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The dock's exit, with the two projections the emitter needs -/

/-- **`dock_step`, with its head profile and its untouched answer slots.**  The
proof is `RepairCloseoutFinalC10WorkerDock.dock_step`'s, with the two extra
port projections read off the same `install`/`dockH` bookkeeping. -/
theorem dock_exit (entryWidth : ℕ) (entries : List Entry) (bank : Fin 218 → List Bool)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (hready : DockReady entryWidth entries bank) :
    ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step dockBody (dockBudget entryWidth entries.length) (fun _ => 0) bank heads exit ∧
        CompetitorSumFold.Store (joinScalarWidth entryWidth entries.length)
          (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
          (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
            (contributions entries))
          (fun i : Fin 94 => exit (foldSlot (i.castAdd 1))) ∧
        (∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → heads i = 0) ∧
        (∀ j : Fin 29, exit (answerSlot j) = bank (answerSlot j)) := by
  classical
  have hjoin : joinScalarWidth entryWidth entries.length = joinWidth entryWidth entries :=
    joinScalarWidth_eq entryWidth entries
  obtain ⟨multiplyExit, hmultiply, hterm, _hshort, _hdriver, hvalid⟩ :=
    CloseoutRowsEstimatorCoefficients.EntryMachine.ready_stream_run entryWidth
      (joinScalarWidth entryWidth entries.length) entries hentries
      (by rw [hjoin]; exact width_le_joinWidth entryWidth entries)
      (by rw [hjoin]; exact length_le_joinWidth entryWidth entries)
  have hmultiplyStep :
      Step CompetitorMonomialEntry.machine
        (CompetitorMonomialEntry.readyBudget (joinScalarWidth entryWidth entries.length)
          entries.length)
        (fun _ => 0)
        (CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput entryWidth
          (joinScalarWidth entryWidth entries.length) entries)
        (fun _ => 0) multiplyExit := by
    obtain ⟨r, hr, ht, hh, hs⟩ := hmultiply
    exact ⟨r, hr, funext hh, ht, hs⟩
  have hmultiplyDock :=
    hmultiplyStep.dock entrySlot entrySlot_injective (fun _ => 0) bank
      (fun _ => rfl) hready.multiply
  rw [dockH_existing entrySlot (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at hmultiplyDock
  set middle : Fin 218 → List Bool := install entrySlot bank multiplyExit with hmiddle
  have hmiddleSource : middle (entrySlot 74) =
      CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
        (contributions entries) := by
    rw [hmiddle, install_slot entrySlot entrySlot_injective bank multiplyExit 74, hterm]
    rfl
  obtain ⟨receipt, foldOut, hrun, hsteps, htapes, hheads, hstore, _hvalue⟩ :=
    CompetitorSumEntry.uniform_cold_sum_run
      (CompetitorRationalDecision.width entryWidth) (contributions entries) hvalid
  have hwidth : CompetitorSumWidth.width (contributions entries).length
      (CompetitorRationalDecision.width entryWidth) =
      joinScalarWidth entryWidth entries.length := by
    rw [joinScalarWidth, contributions_length]
  rw [hwidth] at hrun hsteps hstore
  have hfoldStep :
      Step CompetitorSumEntry.machine
        (CompetitorSumEntry.budget (joinScalarWidth entryWidth entries.length)
          (contributions entries).length)
        (fun _ => 0)
        (CompetitorSumEntry.input (joinScalarWidth entryWidth entries.length)
          (contributions entries))
        receipt.final.heads receipt.final.tapes :=
    Step.of_run hrun rfl rfl
  have hfoldIn : ∀ j : Fin 95, middle (foldSlot j) =
      CompetitorSumEntry.input (joinScalarWidth entryWidth entries.length)
        (contributions entries) j := by
    intro j
    by_cases hj : j.val = 88
    · have hjs : j = foldSource := Fin.ext (by rw [hj]; rfl)
      subst hjs
      rw [foldSlot_source, hmiddleSource, foldInput_source]
    · rw [hmiddle,
        install_other entrySlot bank multiplyExit (foldSlot j)
          (fun k => entrySlot_ne_foldSlot j hj k)]
      exact hready.fold j hj
  have hfoldDock :=
    hfoldStep.dock foldSlot foldSlot_injective (fun _ => 0) middle (fun _ => rfl) hfoldIn
  have hcount : (contributions entries).length = entries.length := contributions_length entries
  rw [hcount] at hfoldDock
  refine ⟨dockH foldSlot (fun _ => 0) receipt.final.heads,
    install foldSlot middle receipt.final.tapes, hmultiplyDock.seq hfoldDock, ?_, ?_, ?_⟩
  · have hproject : (fun i : Fin 94 =>
        install foldSlot middle receipt.final.tapes (foldSlot (i.castAdd 1))) = foldOut := by
      funext i
      rw [install_slot foldSlot foldSlot_injective middle receipt.final.tapes (i.castAdd 1)]
      exact htapes i
    rw [hproject]
    exact hstore
  · intro i h76 h186
    cases hp : RecoveryFocus.pick foldSlot i with
    | none => simp only [dockH, hp]
    | some j =>
      simp only [dockH, hp]
      have hji : foldSlot j = i := RecoveryFocus.slot_of_pick foldSlot hp
      have hjv : (foldSlot j).val = i.val := congrArg Fin.val hji
      rw [foldSlot_val] at hjv
      have hj88 : j.val ≠ 88 := by intro h; rw [if_pos h] at hjv; omega
      have hjlt : j.val < 94 := by
        rcases Nat.lt_or_ge j.val 94 with h | h
        · exact h
        · have := j.isLt
          have hj94 : j.val = 94 := by omega
          rw [if_neg hj88] at hjv
          omega
      have hcast : j = (⟨j.val, hjlt⟩ : Fin 94).castAdd 1 := Fin.ext rfl
      rw [hcast, hheads ⟨j.val, hjlt⟩]
      simp only [CompetitorSumFold.heads, hj88, if_false]
  · intro j
    rw [install_other foldSlot middle receipt.final.tapes (answerSlot j)
      (fun k => answerSlot_ne_foldSlot k j), hmiddle,
      install_other entrySlot bank multiplyExit (answerSlot j)
        (fun k => answerSlot_ne_entrySlot k j)]

/-! ## §2 The body, closed to one loader -/

/-- **The estimator body runs, from one loader receipt.**  `hemit` is gone: the
emitter's operand ports are produced by `emitLoader`, an actual machine, from
the fold's stored accumulator.  What remains is the prologue `hloader`, whose
own obligation is the ready bank plus the emitter's three CONSTANT ports. -/
theorem body_runs_of_loader {loaderStates : ℕ}
    (onset entryWidth : ℕ) (loader : Machine 218 loaderStates) (loaderFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank)
    (hloader : Step loader (loaderFuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (fullBody loader emitLoader))
          dockTapes_two result).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) bank) :
    BodyRuns onset entryWidth loader emitLoader loaderFuel
      (fun _ => emitFuel (joinScalarWidth entryWidth entries.length)) len x bits entries := by
  obtain ⟨dockHeads, dockExit, hdock, hstore, hzero, hanswerPorts⟩ :=
    dock_exit entryWidth entries bank hentries hready
  have hvalid : CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (joinScalarWidth entryWidth entries.length) := by
    rw [joinScalarWidth_eq entryWidth entries]
    exact CloseoutFinalC10WorkerWidth.answer_valid (CompetitorRationalDecision.width entryWidth)
      entries (contributions_valid entryWidth entries hentries)
  have hexitEntry : EmitEntry (joinScalarWidth entryWidth entries.length) dockExit := by
    intro j
    rw [hanswerPorts j]
    exact hentry j
  obtain ⟨operandHeads, operands, hemitStep, hoperandHeads, hoperands⟩ :=
    emit_loader_step (joinScalarWidth entryWidth entries.length)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
        (contributions entries))
      dockHeads dockExit hstore hvalid hzero hexitEntry
  obtain ⟨answerHeads, answerExit, hanswer, hencoded⟩ :=
    answer_step (joinScalarWidth entryWidth entries.length)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      operandHeads operands hoperandHeads hoperands
  have hwidth : joinScalarWidth entryWidth entries.length =
      foldWidth (CompetitorRationalDecision.width entryWidth) entries :=
    joinScalarWidth_eq entryWidth entries
  rw [hwidth] at hencoded
  exact ⟨answerHeads, answerExit,
    (hloader.seq hdock).seq (hemitStep.seq hanswer), hencoded⟩

/-! ## §3 The junction -/

/-- **`EstimatorBody`, from one loader receipt.**  Everything semantic is S1's
(`hcalls`) and W1's (`hfolded`, via `WorkerWidth.answer_valid`); everything
physical is `body_runs_of_loader`. -/
noncomputable def estimator_body_of_loader {Atom : Type} {loaderStates : ℕ}
    (onset entryWidth : ℕ) (loader : Machine 218 loaderStates) (loaderFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (supplier : List Atom → ℚ) (polynomial : CircuitPolynomial Atom 4)
    (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank)
    (hloader : Step loader (loaderFuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (fullBody loader emitLoader))
          dockTapes_two result).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) bank) :
    EstimatorBody (fullBody loader emitLoader) onset inputTape flag result port
      dockTapes_two
      (fullBodyFuel loaderFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
        entryWidth entries.length)
      (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
      (CompetitorRationalDecision.width entryWidth) supplier polynomial len x bits :=
  estimator_body_of_runs onset entryWidth loader emitLoader loaderFuel
    (fun _ => emitFuel (joinScalarWidth entryWidth entries.length)) len x bits supplier
    polynomial entries hcalls hentries
    (body_runs_of_loader onset entryWidth loader loaderFuel len x bits entries hentries
      bank hready hentry hloader)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody
