import Proof.CaseAnalysis.FinalWorkerEmitBody
import Proof.CaseAnalysis.FinalWorkerDockSeam

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The dock without its loader -/

/-- The dock without its loader. -/
noncomputable def dockedBody {emitStates : ℕ} (emitLoader : Machine 218 emitStates) :=
  Composition.machine dockBody
    (Composition.machine emitLoader
      (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine))

/-- The docked body's fuel: `fullBodyFuel` without the loader's summand. -/
def dockedFuel (emitFuel : ℕ → ℕ) (entryWidth callCount : ℕ) : ℕ → ℕ :=
  fun n => dockBudget entryWidth callCount + 1 +
    (emitFuel n + 1 + CompetitorCountRecordAppend.budget (joinScalarWidth entryWidth callCount))

/-- **`body_runs_of_loader` minus the loader: from any ready bank at heads 0.**
The proof is `(hdock).seq (hemitStep.seq hanswer)` exactly as in
`body_runs_of_loader`, without the leading `hloader.seq`. -/
theorem docked_run (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool) (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank) (n : ℕ) :
    ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (dockedBody emitLoader)
        (dockedFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
          entryWidth entries.length n)
        (fun _ => 0) bank heads exit ∧
      exit port = CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1 := by
  obtain ⟨dockHeads, dockExit, hdock, hstore, hzero, hanswerPorts⟩ :=
    dock_exit entryWidth entries bank hentries hready
  have hvalid : CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (joinScalarWidth entryWidth entries.length) := by
    rw [joinScalarWidth_eq entryWidth entries]
    exact answer_valid (CompetitorRationalDecision.width entryWidth)
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
  exact ⟨answerHeads, answerExit, hdock.seq (hemitStep.seq hanswer), hencoded⟩

/-! ## §2 The layout on `218 + e` tapes -/

/-- Both heads profiles at zero, joined, are the zero profile on `218 + e` tapes. -/
theorem addCases_zero (e : ℕ) :
    (Fin.addCases (fun _ : Fin 218 => (0 : ℕ)) (fun _ : Fin e => (0 : ℕ))) =
      (fun _ : Fin (218 + e) => (0 : ℕ)) := by
  funext i
  refine Fin.addCases (m := 218) (n := e) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

/-- **The verifier's input tapes do not depend on the machine.**  On `218 + e`
tapes they are the 218-tape input tapes with every extra tape blank. -/
theorem inputTapes_addCases {e s s' : ℕ} (p : Machine (218 + e) s) (p' : Machine 218 s')
    (ht : 2 ≤ 218 + e) (resultSlot : Fin (218 + e)) (resultSlot' : Fin 218)
    (input witness : List Bool) :
    (UAcceptanceCarrier.verifier p ht resultSlot).inputTapes input witness =
      Fin.addCases
        ((UAcceptanceCarrier.verifier p' dockTapes_two resultSlot').inputTapes input witness)
        (fun _ : Fin e => []) := by
  funext i
  rw [UAcceptanceCarrier.inputTapes_eq, UAcceptanceCarrier.inputTapes_eq]
  refine Fin.addCases (m := 218) (n := e) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    rfl
  · rw [Fin.addCases_right]
    have h0 : (Fin.natAdd 218 j).val ≠ 0 := by rw [Fin.val_natAdd]; omega
    have h1 : (Fin.natAdd 218 j).val ≠ 1 := by rw [Fin.val_natAdd]; omega
    show (if (Fin.natAdd 218 j).val = 0 then frame input
      else if (Fin.natAdd 218 j).val = 1 then frame witness else []) = []
    rw [if_neg h0, if_neg h1]

/-- **The gate's exit commutes with the embedding.** -/
theorem exitTapes_addCases {e : ℕ} (flagSlot : Fin 218) (T : Fin 218 → List Bool)
    (h : ℕ) (b : Bool) :
    exitTapes (Fin.castAdd e flagSlot) (Fin.addCases T (fun _ : Fin e => [])) h b =
      Fin.addCases (exitTapes flagSlot T h b) (fun _ : Fin e => []) := by
  funext i
  refine Fin.addCases (m := 218) (n := e) (fun j => ?_) (fun j => ?_) i
  · simp only [exitTapes, Fin.addCases_left]
    by_cases hj : j = flagSlot
    · subst hj
      rw [if_pos rfl, if_pos rfl]
    · have hj' : Fin.castAdd e j ≠ Fin.castAdd e flagSlot := by
        intro hc
        apply hj
        exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val hc)
      rw [if_neg hj', if_neg hj]
  · simp only [exitTapes, Fin.addCases_left, Fin.addCases_right]
    have hne : Fin.natAdd 218 j ≠ Fin.castAdd e flagSlot := by
      intro hc
      have hv := congrArg Fin.val hc
      rw [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := flagSlot.isLt
      omega
    rw [if_neg hne]

/-- **The stage's input, as the embedding of the 218-tape gate exit.**  This is
the exact shape the supplier stage receives: the gate's exit on the dock's own
218 tapes, joined with `e` blank extra tapes. -/
theorem stageInput_addCases {e s s' : ℕ} (p : Machine (218 + e) s) (p' : Machine 218 s')
    (ht : 2 ≤ 218 + e) (input witness : List Bool) :
    exitTapes (Fin.castAdd e flag)
        ((UAcceptanceCarrier.verifier p ht (Fin.castAdd e result)).inputTapes input witness)
        0 true =
      Fin.addCases
        (exitTapes flag
          ((UAcceptanceCarrier.verifier p' dockTapes_two result).inputTapes input witness)
          0 true)
        (fun _ : Fin e => []) := by
  rw [inputTapes_addCases p p' ht (Fin.castAdd e result) result input witness,
    exitTapes_addCases]

/-! ## §3 The stage seam -/

/-- The stage seam: a supplier stage on `218+e` tapes followed by the embedded dock. -/
noncomputable def stagedBody {e st emitStates : ℕ} (stage : Machine (218+e) st)
    (emitLoader : Machine 218 emitStates) :=
  Composition.machine stage (TapeEmbedding.machine e (dockedBody emitLoader))

/-- The seam's fuel: the stage's, one paid bridge step, the docked body's. -/
def stagedFuel (stageFuel emitFuel : ℕ → ℕ) (entryWidth callCount : ℕ) : ℕ → ℕ :=
  fun n => stageFuel n + 1 + dockedFuel emitFuel entryWidth callCount n

/-- **`EstimatorBody` from a supplier stage.**  The stage leaves the ready bank
on the first 218 tapes, with every head at zero and arbitrary scratch on the
extra tapes; the embedded dock then runs untouched by the extra tapes
(`Step.embed`), and its port `215` -- now tape `Fin.castAdd e port` -- carries
the record word of the fold.  The emit loader is the built one
(`CloseoutFinalC10WorkerEmitLoader.emitLoader`), as in `body_runs_of_loader`. -/
noncomputable def estimatorBody_of_stage {Atom : Type} {e st : ℕ}
    (stage : Machine (218+e) st) (stageFuel emitFuel : ℕ → ℕ)
    (onset entryWidth : ℕ) (len : ℕ) (x : BitInput len) (bits : List Bool)
    (supplier : List Atom → ℚ) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank)
    (hemit : emitFuel =
      fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
        (joinScalarWidth entryWidth entries.length))
    (hstage : Step stage (stageFuel len) (fun _ => 0)
      (exitTapes (Fin.castAdd e flag)
        ((UAcceptanceCarrier.verifier
          (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
            (stagedBody stage emitLoader))
          (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) (Fin.addCases bank scratch)) :
    EstimatorBody (stagedBody stage emitLoader) onset (Fin.castAdd e inputTape)
      (Fin.castAdd e flag) (Fin.castAdd e result) (Fin.castAdd e port) (by omega)
      (stagedFuel stageFuel emitFuel entryWidth entries.length)
      (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
      (CompetitorRationalDecision.width entryWidth) supplier polynomial len x bits := by
  subst hemit
  have hdocked := docked_run entryWidth entries hentries bank hready hentry len
  have hembed :
      Step (TapeEmbedding.machine e (dockedBody emitLoader))
        (dockedFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
          entryWidth entries.length len)
        (fun _ => 0) (Fin.addCases bank scratch)
        (Fin.addCases hdocked.choose (fun _ : Fin e => 0))
        (Fin.addCases hdocked.choose_spec.choose scratch) :=
    (hdocked.choose_spec.choose_spec.1.embed (fun _ : Fin e => 0) scratch).congr_in
      (addCases_zero e) rfl
  refine estimatorBody_ofFoldWidth entries (Fin.addCases hdocked.choose (fun _ : Fin e => 0))
    (Fin.addCases hdocked.choose_spec.choose scratch) hcalls
    (contributions_valid entryWidth entries hentries) ?_ ?_
  · exact hstage.seq hembed
  · rw [Fin.addCases_left]
    exact hdocked.choose_spec.choose_spec.2

noncomputable def realizes_of_stage {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm} {e st : ℕ}
    (phase : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput arity → Bool)
    (proofValue :
      BitInput arity → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (supplier : List Atom → ℚ) (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth) (hdenominatorPositive : 0 < denominator)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤
        failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (stage : Machine (218+e) st) (stageFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (hready : DockReady entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom) bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length) bank)
    (hemit : emitFuel =
      fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length))
    (hstage : Step stage (stageFuel len) (fun _ => 0)
      (exitTapes (Fin.castAdd e flag)
        ((UAcceptanceCarrier.verifier
          (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
            (stagedBody stage emitLoader))
          (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) (Fin.addCases bank scratch)) :
    Realizes phase constants pcpp proofValue evaluate
      (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
        (stagedBody stage emitLoader))
      (workerBudget onset
        (stagedFuel stageFuel emitFuel entryWidth
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
        len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier
        (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
          (stagedBody stage emitLoader))
        (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits)
      (Fin.castAdd e port)
      (foldWidth (CompetitorRationalDecision.width entryWidth)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom)) :=
  worker_realizes phase constants pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic supplier failure hfailure hpoint mass hmass hbudget
    onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
    (Fin.castAdd e port) (stagedBody stage emitLoader) (by omega) rfl
    (stagedFuel stageFuel emitFuel entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
    (foldWidth (CompetitorRationalDecision.width entryWidth)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
    (CompetitorRationalDecision.width entryWidth) len x bits honset
    (estimatorBody_of_stage stage stageFuel emitFuel onset entryWidth len x bits supplier
      (phasePolynomial phase pcpp coordinate systematicAtom)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom)
      (phase_calls phase pcpp coordinate systematicAtom supplier answer denominator
        hsupplier)
      (phase_records_valid phase pcpp coordinate systematicAtom answer denominator
        entryWidth hcount hdenominator hdenominatorPositive hcoefficients)
      bank scratch hready hentry hemit hstage)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
