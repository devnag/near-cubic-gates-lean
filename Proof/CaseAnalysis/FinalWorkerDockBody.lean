import Proof.CaseAnalysis.FinalWorkerDock

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The emitter's slots -/

theorem answerSlot_val (j : Fin 29) : (answerSlot j).val = 187 + j.val := rfl

theorem answerSlot_injective : Function.Injective answerSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [answerSlot_val, answerSlot_val] at hv
  exact Fin.ext (by omega)

theorem port_eq : port = answerSlot 28 := rfl

theorem answer_step (scalarWidth : ℕ) (estimate : CompetitorValidity.Estimate)
    (heads : Fin 218 → ℕ) (bank : Fin 218 → List Bool)
    (hheads : ∀ j : Fin 29, heads (answerSlot j) = 0)
    (hbank : ∀ j : Fin 29,
      bank (answerSlot j) =
        CloseoutRowsEstimatorCoefficients.Append.input scalarWidth estimate 1 1 j) :
    ∃ (exitHeads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine)
        (CompetitorCountRecordAppend.budget scalarWidth) heads bank exitHeads exit ∧
      exit port =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord scalarWidth estimate 1 1 := by
  obtain ⟨receipt, hrun, _hsteps, hword⟩ := result_record_run scalarWidth estimate
  have hstep :
      Step CompetitorCountRecordAppend.machine
        (CompetitorCountRecordAppend.budget scalarWidth) (fun _ => 0)
        (CloseoutRowsEstimatorCoefficients.Append.input scalarWidth estimate 1 1)
        receipt.final.heads receipt.final.tapes :=
    Step.of_run hrun rfl rfl
  have hdock := hstep.dock answerSlot answerSlot_injective heads bank hheads hbank
  refine ⟨dockH answerSlot heads receipt.final.heads,
    install answerSlot bank receipt.final.tapes, hdock, ?_⟩
  rw [port_eq, install_slot answerSlot answerSlot_injective bank receipt.final.tapes 28]
  exact hword

/-! ## §2 The whole estimator body -/

/-- The estimator body: the loader, the docked multiply stage and fold, the
emitter's loader, and the docked emitter. -/
noncomputable def fullBody {loaderStates emitStates : ℕ}
    (loader : Machine 218 loaderStates) (emitLoader : Machine 218 emitStates) :=
  Composition.machine (Composition.machine loader dockBody)
    (Composition.machine emitLoader
      (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine))

/-- The body's fuel: four `n`-determined summands and the three paid bridge
steps of `Composition.machine`.  No summand mentions the witness length. -/
def fullBodyFuel (loaderFuel emitFuel : ℕ → ℕ) (entryWidth callCount : ℕ) : ℕ → ℕ :=
  fun n =>
    (loaderFuel n + 1 + dockBudget entryWidth callCount) + 1 +
      (emitFuel n + 1 +
        CompetitorCountRecordAppend.budget (joinScalarWidth entryWidth callCount))

/-! ## §3 The body's run, as one Prop -/

/-- Every contribution of the call stream is valid at the fold's scalar width. -/
theorem contributions_valid (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry) :
    ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate
        (CompetitorRationalDecision.width entryWidth) := by
  intro estimate hestimate
  rcases List.mem_map.mp hestimate with ⟨entry, hentry, rfl⟩
  exact CloseoutRowsEstimatorCoefficients.Stream.Entry.valid_estimate entryWidth entry
    (hentries entry hentry)

def BodyRuns {loaderStates emitStates : ℕ} (onset entryWidth : ℕ)
    (loader : Machine 218 loaderStates) (emitLoader : Machine 218 emitStates)
    (loaderFuel emitFuel : ℕ → ℕ) (len : ℕ) (x : BitInput len) (bits : List Bool)
    (entries : List Entry) : Prop :=
  ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
    Step (fullBody loader emitLoader)
      (fullBodyFuel loaderFuel emitFuel entryWidth entries.length len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (fullBody loader emitLoader))
          dockTapes_two result).inputTapes (List.ofFn x) bits) 0 true) heads exit ∧
    exit port =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1

/-- **W2's physical half.**  The loader, the docked multiply stage, the cold
fold, the emitter's loader and the docked emitter, composed into one machine on
one bank behind P4's length gate.  The multiply-to-fold handoff is a port
projection (`RepairCloseoutFinalC10WorkerDock.dock_step`); the emitter's output
port `215` is read off by `install_slot`. -/
theorem body_runs {loaderStates emitStates : ℕ}
    (onset entryWidth : ℕ) (loader : Machine 218 loaderStates)
    (emitLoader : Machine 218 emitStates) (loaderFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hloader : Step loader (loaderFuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (fullBody loader emitLoader))
          dockTapes_two result).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) bank)
    (hemit : ∀ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      CompetitorSumFold.Store (joinScalarWidth entryWidth entries.length)
          (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
          (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
            (contributions entries))
          (fun i : Fin 94 => exit (foldSlot (i.castAdd 1))) →
        ∃ (operandHeads : Fin 218 → ℕ) (operands : Fin 218 → List Bool),
          Step emitLoader (emitFuel len) heads exit operandHeads operands ∧
          (∀ j : Fin 29, operandHeads (answerSlot j) = 0) ∧
          (∀ j : Fin 29,
            operands (answerSlot j) =
              CloseoutRowsEstimatorCoefficients.Append.input
                (joinScalarWidth entryWidth entries.length)
                (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
                1 1 j)) :
    BodyRuns onset entryWidth loader emitLoader loaderFuel emitFuel len x bits entries := by
  obtain ⟨dockHeads, dockExit, hdock, hstore, _hsource⟩ :=
    dock_step entryWidth entries bank hentries hready
  obtain ⟨operandHeads, operands, hemitStep, hoperandHeads, hoperands⟩ :=
    hemit dockHeads dockExit hstore
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

/-! ## §4 The junction, closed -/

noncomputable def estimator_body_of_runs {Atom : Type} {loaderStates emitStates : ℕ}
    (onset entryWidth : ℕ) (loader : Machine 218 loaderStates)
    (emitLoader : Machine 218 emitStates) (loaderFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (supplier : List Atom → ℚ) (polynomial : CircuitPolynomial Atom 4)
    (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (hruns : BodyRuns onset entryWidth loader emitLoader loaderFuel emitFuel len x bits
      entries) :
    EstimatorBody (fullBody loader emitLoader) onset inputTape flag result port
      dockTapes_two (fullBodyFuel loaderFuel emitFuel entryWidth entries.length)
      (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
      (CompetitorRationalDecision.width entryWidth) supplier polynomial len x bits :=
  estimatorBody_ofFoldWidth entries hruns.choose hruns.choose_spec.choose hcalls
    (contributions_valid entryWidth entries hentries)
    hruns.choose_spec.choose_spec.1 hruns.choose_spec.choose_spec.2

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
