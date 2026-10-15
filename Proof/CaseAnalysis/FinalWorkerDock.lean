import Proof.CaseAnalysis.FinalSupplierCalls
import Proof.MachineModel.Layout

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
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

/-! ## §1 The bank -/

/-- The estimator bank's tape count.  Fixed here so that S1, W2 and the final
assembly cannot disagree about a layout. -/
abbrev dockTapes : ℕ := 218

/-- The multiply stage's ninety tapes. -/
def entrySlot (j : Fin 90) : Fin 218 := ⟨2 + j.val, by omega⟩

/-- The fold's source tape, as an index of its own bank. -/
def foldSource : Fin 95 := (⟨88, by omega⟩ : Fin 94).castAdd 1

/-- The fold's ninety-five tapes.  Its source tape is the multiply stage's
output port; every other tape is fresh. -/
def foldSlot (j : Fin 95) : Fin 218 :=
  if j.val = 88 then ⟨76, by omega⟩ else ⟨92 + j.val, by omega⟩

/-- The answer emitter's twenty-nine tapes. -/
def answerSlot (j : Fin 29) : Fin 218 := ⟨187 + j.val, by omega⟩

/-- The phase output port: the emitter's own output tape. -/
def port : Fin 218 := answerSlot 28

/-- The gate's scratch slot. -/
def flag : Fin 218 := ⟨216, by omega⟩

/-- The gate's verdict slot. -/
def result : Fin 218 := ⟨217, by omega⟩

/-- The verifier's framed input tape. -/
def inputTape : Fin 218 := ⟨0, by omega⟩

theorem inputTape_val : inputTape.val = 0 := rfl

theorem dockTapes_two : 2 ≤ (218 : ℕ) := by omega

theorem entrySlot_val (j : Fin 90) : (entrySlot j).val = 2 + j.val := rfl

theorem foldSlot_val (j : Fin 95) :
    (foldSlot j).val = if j.val = 88 then 76 else 92 + j.val := by
  unfold foldSlot
  split <;> rfl

theorem entrySlot_injective : Function.Injective entrySlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, entrySlot_val] at hv
  exact Fin.ext (by omega)

theorem foldSlot_injective : Function.Injective foldSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [foldSlot_val, foldSlot_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  refine Fin.ext ?_
  by_cases hA : a.val = 88
  · by_cases hB : b.val = 88
    · omega
    · rw [if_pos hA, if_neg hB] at hv; omega
  · by_cases hB : b.val = 88
    · rw [if_neg hA, if_pos hB] at hv; omega
    · rw [if_neg hA, if_neg hB] at hv; omega

/-- **The handoff, as a slot identity.**  The fold's source tape IS the
multiply stage's output port `74`.  Nothing is copied between the stages. -/
theorem foldSlot_source : foldSlot foldSource = entrySlot 74 := by
  apply Fin.ext
  rw [foldSlot_val, entrySlot_val]
  rfl

/-- Every other fold tape is fresh: no multiply-stage tape lands on it. -/
theorem entrySlot_ne_foldSlot (j : Fin 95) (hj : j.val ≠ 88) (k : Fin 90) :
    entrySlot k ≠ foldSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, foldSlot_val, if_neg hj] at hv
  have := k.isLt
  omega

/-! ## §2 The scalar width and the budget -/

/-- The scalar width at which the two stages agree, as a function of the
record width and the NUMBER OF CALLS.  This is `WorkerJoin.joinWidth`, keyed
by the call count rather than by the list. -/
def joinScalarWidth (entryWidth callCount : ℕ) : ℕ :=
  CompetitorSumWidth.width callCount (CompetitorRationalDecision.width entryWidth)

theorem joinScalarWidth_eq (entryWidth : ℕ) (entries : List Entry) :
    joinScalarWidth entryWidth entries.length = joinWidth entryWidth entries := by
  unfold joinScalarWidth joinWidth foldWidth
  rw [contributions_length]

def dockBudget (entryWidth callCount : ℕ) : ℕ :=
  CompetitorMonomialEntry.readyBudget (joinScalarWidth entryWidth callCount) callCount + 1 +
    CompetitorSumEntry.budget (joinScalarWidth entryWidth callCount) callCount

/-! ## §3 The docked body -/

/-- **The estimator body: one machine on one bank.**  The multiply stage and
the cold fold, each docked by its own slot map, composed by
`Composition.machine`. -/
noncomputable def dockBody :=
  Composition.machine
    (RecoveryFocus.machine entrySlot CompetitorMonomialEntry.machine)
    (RecoveryFocus.machine foldSlot CompetitorSumEntry.machine)

/-- **The bank the body starts from.**  Each stage's own input, at its own
slots -- except the fold's source tape, which the multiply stage produces and
which therefore does NOT appear here.  Every condition is a port projection. -/
structure DockReady (entryWidth : ℕ) (entries : List Entry)
    (bank : Fin 218 → List Bool) : Prop where
  /-- The multiply stage's input, including S1's call-record stream. -/
  multiply : ∀ j : Fin 90,
    bank (entrySlot j) =
      CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput entryWidth
        (joinScalarWidth entryWidth entries.length) entries j
  /-- The fold's input, except its source tape. -/
  fold : ∀ j : Fin 95, j.val ≠ 88 →
    bank (foldSlot j) =
      CompetitorSumEntry.input (joinScalarWidth entryWidth entries.length)
        (contributions entries) j

theorem foldInput_castAdd (scalarWidth : ℕ)
    (terms : List CompetitorValidity.Estimate) (i : Fin 94) :
    CompetitorSumEntry.input scalarWidth terms (i.castAdd 1) =
      CompetitorSumFold.coldInput scalarWidth
        (CompetitorSumFold.words scalarWidth terms) i := by
  simp [CompetitorSumEntry.input, CompetitorSumEntry.extendTapes]

/-- The fold's source tape carries the term stream. -/
theorem foldInput_source (scalarWidth : ℕ)
    (terms : List CompetitorValidity.Estimate) :
    CompetitorSumEntry.input scalarWidth terms foldSource =
      CompetitorSumFold.words scalarWidth terms := by
  rw [foldSource, foldInput_castAdd]
  rfl

/-! ## §4 The docked chain -/

/-- **W2's core.**  One `Step` of the docked body, from a ready bank, at a
budget that is a function of the record width and the call count alone.  The
fold's stored accumulator is read off the exit bank BY PORT PROJECTION, and it
is the exact signed-rational fold of the AND-four supplier call stream.

The multiply-to-fold handoff is not assumed: the fold's source tape is the
multiply stage's output port (`foldSlot_source`), so `install_slot` supplies
it from the predecessor's exit. -/
theorem dock_step (entryWidth : ℕ) (entries : List Entry)
    (bank : Fin 218 → List Bool)
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
        exit (entrySlot 74) =
          CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
            (contributions entries) := by
  classical
  have hjoin : joinScalarWidth entryWidth entries.length = joinWidth entryWidth entries :=
    joinScalarWidth_eq entryWidth entries
  -- the multiply stage, on its own bank
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
  -- the bank after the multiply stage
  set middle : Fin 218 → List Bool := install entrySlot bank multiplyExit with hmiddle
  have hmiddleSource : middle (entrySlot 74) =
      CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
        (contributions entries) := by
    rw [hmiddle, install_slot entrySlot entrySlot_injective bank multiplyExit 74, hterm]
    rfl
  -- the fold, on its own bank
  obtain ⟨receipt, foldOut, hrun, hsteps, htapes, _hheads, hstore, _hvalue⟩ :=
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
  -- the composed body
  have hcount : (contributions entries).length = entries.length := contributions_length entries
  rw [hcount] at hfoldDock
  refine ⟨dockH foldSlot (fun _ => 0) receipt.final.heads,
    install foldSlot middle receipt.final.tapes, hmultiplyDock.seq hfoldDock, ?_, ?_⟩
  · have hproject : (fun i : Fin 94 =>
        install foldSlot middle receipt.final.tapes (foldSlot (i.castAdd 1))) = foldOut := by
      funext i
      rw [install_slot foldSlot foldSlot_injective middle receipt.final.tapes (i.castAdd 1)]
      exact htapes i
    rw [hproject]
    exact hstore
  · have hcast : foldSource = Fin.castAdd 1 (88 : Fin 94) := rfl
    have hproj : install foldSlot middle receipt.final.tapes (foldSlot foldSource)
        = receipt.final.tapes foldSource :=
      install_slot foldSlot foldSlot_injective middle receipt.final.tapes foldSource
    rw [← foldSlot_source, hproj, hcast, htapes (88 : Fin 94)]
    exact hstore.source

/-! ## §5 The gate front -/

theorem worker_dock {Atom : Type} {loaderStates : ℕ}
    (onset entryWidth : ℕ) (loader : Machine 218 loaderStates)
    (loaderFuel : ℕ → ℕ) (len : ℕ) (x : BitInput len) (bits : List Bool)
    (honset : onset ≤ len)
    (supplier : List Atom → ℚ) (polynomial : CircuitPolynomial Atom 4)
    (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hloader : Step loader (loaderFuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (Composition.machine loader dockBody))
          dockTapes_two result).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) bank) :
    ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (worker onset inputTape flag result (Composition.machine loader dockBody))
        (workerBudget onset
          (fun n => loaderFuel n + 1 + dockBudget entryWidth entries.length) len)
        (fun _ => 0)
        ((UAcceptanceCarrier.verifier
          (worker onset inputTape flag result (Composition.machine loader dockBody))
          dockTapes_two result).inputTapes (List.ofFn x) bits) heads exit ∧
      CompetitorSumFold.Store (joinScalarWidth entryWidth entries.length)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
        (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
          (contributions entries))
        (fun i : Fin 94 => exit (foldSlot (i.castAdd 1))) ∧
      (((CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions entries)).value : ℚ) : ℝ) =
        polynomial.estimatedMean supplier := by
  obtain ⟨heads, exit, hstep, hstore, _hsource⟩ :=
    dock_step entryWidth entries bank hentries hready
  refine ⟨heads, exit, ?_, hstore, ?_⟩
  · exact worker_step onset inputTape flag result (Composition.machine loader dockBody)
      dockTapes_two inputTape_val
      (fun n => loaderFuel n + 1 + dockBudget entryWidth entries.length) len x bits honset
      heads exit (hloader.seq hstep)
  · refine folded_value_eq_estimatedMean supplier
      (CompetitorRationalDecision.width entryWidth) polynomial entries hcalls ?_
    intro estimate hestimate
    rcases List.mem_map.mp hestimate with ⟨entry, hentry, rfl⟩
    exact CloseoutRowsEstimatorCoefficients.Stream.Entry.valid_estimate entryWidth entry
      (hentries entry hentry)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
