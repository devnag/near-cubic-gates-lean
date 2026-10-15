import Proof.CaseAnalysis.FinalStageContracts

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform

open LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation SourceInterfaces SupplierPipeline
open CompetitorRationalGap CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10Exactness RepairOrdinary.CloseoutFinalC10Realizes
open RepairOrdinary.CloseoutFinalC10WorkerChain RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerDockSeam RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10StageSeam RepairOrdinary.CloseoutFinalC10SupplierCalls
open RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open C10Verdict C10LengthGate C10TailCompose C10BodyWidths C10TailComposeVerdict

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData sources k p) (hs : StageBlock sources k p S)

def tailStates : ℕ := (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose

def tailMachine : LocalBitMultitape.Machine C10TailVerdict.tailBank (tailStates sources) :=
  (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose_spec.choose

theorem tail_spec : UniformTail' (tailMachine sources) C10TailVerdictUniform.tbud (constantsOf sources) := by
  intro bP bM bC eP eM eC hvP hvM hvC hwidth H A hpark
  obtain ⟨H', A', hrun, hiff, hframe, _hhead⟩ :=
    (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose_spec.choose_spec
      bP bM bC eP eM eC hvP hvM hvC hwidth H A hpark
  exact ⟨H', A', hrun, hiff, hframe⟩

/-- The same selected tail also exposes its physical result head. -/
theorem tail_spec_head :
    ∀ (bP bM bC : ℕ) (eP eM eC : CompetitorValidity.Estimate),
      eP.Valid bP → eM.Valid bM → eC.Valid bC →
      C10TailVerdictUniform.TailWidths' (constantsOf sources) bP bM bC →
      ∀ (H : Fin C10TailVerdict.tailBank → ℕ) (A : Fin C10TailVerdict.tailBank → List Bool),
        C10TailVerdictUniform.ParkedThree' bP bM bC eP eM eC H A →
        ∃ H' A', Step (tailMachine sources) (C10TailVerdictUniform.tbud (max bP (max bM bC))) H A H' A' ∧
          (readTapeBit (A' C10TailVerdict.tailFlag) 0 = true ↔
            (CompetitorThresholdDecision.estimate eP.positive eP.negative eP.denominator ≤ 2*zeta (constantsOf sources) ∧
             CompetitorThresholdDecision.estimate eM.positive eM.negative eM.denominator ≤ 1+zeta (constantsOf sources) ∧
             midpoint (constantsOf sources) ≤ CompetitorThresholdDecision.estimate eC.positive eC.negative eC.denominator)) ∧
          (∀ i, C10TailSlotsUniform.PublicPrefix i → A' i = A i) ∧ H' C10TailVerdict.tailFlag = 0 :=
  (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose_spec.choose_spec

def workerOf := C10ComposeWidths.composedWorker' S.e hs.he (Soundness.cutoff (constantsOf sources))
  (body sources k p S) (tailMachine sources)

def phaseBank {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  (hs.hstage n x bits hc ph).choose

def phaseScratch {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  (hs.hstage n x bits hc ph).choose_spec.choose

theorem phaseReady {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    StageReady sources k p S hs.he x bits ph
      (phaseBank sources k p S hs x bits hc ph) (phaseScratch sources k p S hs x bits hc ph) :=
  (hs.hstage n x bits hc ph).choose_spec.choose_spec

def foldedOf {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  CompetitorSumFold.folded CompetitorSumWidth.zero (contributions (records sources k p S x bits ph))

def rawRealizes {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  realizes_of_stage ph (constantsOf sources) (pcppOf sources k p x bits)
    C10TotalDecode.evaluate (proofOf sources k p x bits) (S.coordinate n x bits)
    (hs.hcoordinate n x bits hc) C10TotalDecode.Atom.systematic
    (C10TotalDecode.hsystematic_rfl (pcppOf sources k p x bits))
    (S.supplier n x bits) (S.answer n x bits) (S.denominator n) (S.entryWidth n)
    (hs.hsupplier n x bits hc) (hs.hcount n x bits hc) (hs.hdenominator n hc) (hs.hdenominatorPositive n hc)
    (hs.hcoefficients n x bits hc ph) (S.failure n x bits ph) (hs.hfailure n x bits hc ph)
    (hs.hpoint n x bits hc ph) (S.mass n x bits ph) (hs.hmass n x bits hc ph) (hs.haccuracy n x bits hc ph)
    (Soundness.cutoff (constantsOf sources)) (S.stage ph) (S.stageFuel ph)
    (emissionFuel sources k p S x bits ph) n x bits hc
    (phaseBank sources k p S hs x bits hc ph) (phaseScratch sources k p S hs x bits hc ph)
    (phaseReady sources k p S hs x bits hc ph).hready (phaseReady sources k p S hs x bits hc ph).hentry
    (phaseReady sources k p S hs x bits hc ph).hemit (phaseReady sources k p S hs x bits hc ph).hstage

theorem rawRealizes_result {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    (rawRealizes sources k p S hs x bits hc ph).result = foldedOf sources k p S x bits ph := rfl

theorem blocks_run {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    BlockRunsWidths S.e hs.he (body sources k p S ph) (phaseFuel sources k p S x bits ph)
      (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord (widthOf sources k p S x bits ph)
        (foldedOf sources k p S x bits ph) 1 1) (widthOf sources k p S x bits ph) :=
  C10StageWidths.blockRuns_widths_of_stage hs.he (S.stage ph) (S.stageFuel ph)
    (emissionFuel sources k p S x bits ph) (Soundness.cutoff (constantsOf sources)) (S.entryWidth n)
    n x bits (records sources k p S x bits ph)
    (phase_records_valid ph (pcppOf sources k p x bits) (S.coordinate n x bits) C10TotalDecode.Atom.systematic
      (S.answer n x bits) (S.denominator n) (S.entryWidth n) (hs.hcount n x bits hc)
      (hs.hdenominator n hc) (hs.hdenominatorPositive n hc) (hs.hcoefficients n x bits hc ph))
    (phaseBank sources k p S hs x bits hc ph) (phaseScratch sources k p S hs x bits hc ph)
    (phaseReady sources k p S hs x bits hc ph).hready (phaseReady sources k p S hs x bits hc ph).hentry
    (phaseReady sources k p S hs x bits hc ph).h0 (phaseReady sources k p S hs x bits hc ph).h1
    (phaseReady sources k p S hs x bits hc ph).hemit (phaseReady sources k p S hs x bits hc ph).hstage
    (phaseReady sources k p S hs x bits hc ph).hwidth

include hs in
theorem threshold_le_width {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ widthOf sources k p S x bits ph := by
  apply (hs.hthreshold n).trans
  unfold widthOf
  rw [foldWidth_eq_joinScalarWidth]
  unfold joinScalarWidth CompetitorSumWidth.width CompetitorRationalDecision.width
  nlinarith [Nat.zero_le ((records sources k p S x bits ph).length * (2*S.entryWidth n+3))]

theorem above_run {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) :
    ∃ A, Step (workerOf sources k p S hs) (S.budget n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e)).inputTapes
        (List.ofFn x) bits) (fun _ => 0) A ∧
      (readTapeBit (A (gResult S.e)) 0 = true ↔
        ((((foldedOf sources k p S x bits .penalty).value : ℚ) : ℝ) ≤ bound (constantsOf sources) .penalty ∧
         (((foldedOf sources k p S x bits .moment).value : ℚ) : ℝ) ≤ bound (constantsOf sources) .moment ∧
         bound (constantsOf sources) .clause ≤ (((foldedOf sources k p S x bits .clause).value : ℚ) : ℝ))) ∧
      (∀ ph, A (scr S.e ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (widthOf sources k p S x bits ph) (foldedOf sources k p S x bits ph) 1 1) := by
  have hv (ph : Phase) : (foldedOf sources k p S x bits ph).Valid (widthOf sources k p S x bits ph) :=
    (rawRealizes sources k p S hs x bits hc ph).hvalid
  obtain ⟨A, hrun, hbit, hrec⟩ := C10ComposeWidths.verdict_run_uniform' S.e hs.he
    (body sources k p S) (phaseFuel sources k p S x bits) (widthOf sources k p S x bits)
    (tailMachine sources) C10TailVerdictUniform.tbud (constantsOf sources) (tail_spec sources)
    (foldedOf sources k p S x bits) hv
    (C10TailVerdictUniform.tailWidths'_of (constantsOf sources)
      (threshold_le_width sources k p S hs x bits .penalty)
      (threshold_le_width sources k p S hs x bits .moment)
      (threshold_le_width sources k p S hs x bits .clause))
    (Soundness.cutoff (constantsOf sources)) n x bits hc (blocks_run sources k p S hs x bits hc)
  refine ⟨A, hrun.enlarge (hs.hfuel n x bits), ?_, hrec⟩
  exact hbit.trans (and_congr (bound_penalty _ _) (and_congr (bound_moment _ _) (bound_clause _ _)))

theorem below_run {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : n < Soundness.cutoff (constantsOf sources)) :
    ∃ H A, Step (workerOf sources k p S hs) (S.budget n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e)).inputTapes
        (List.ofFn x) bits) H A ∧ readTapeBit (A (gResult S.e)) (H (gResult S.e)) = false := by
  obtain ⟨H, A, hrun, hbit⟩ := gated_below S.e (Soundness.cutoff (constantsOf sources))
    (C10ComposeWidths.innerOf' S.e hs.he (body sources k p S) (tailMachine sources)) n x bits hc
  have hle : 2*n+3 ≤ actualFuel sources k p S x bits := by
    unfold actualFuel workerBudget
    omega
  exact ⟨H, A, hrun.enlarge (hle.trans (hs.hfuel n x bits)), hbit⟩

/-- The paper's verdict, at the same fixed machine and budget for every witness. -/
def verdict_of_stage (n : ℕ) (x : BitInput n) (bits : List Bool) :
    Verdict (constantsOf sources) (pcppOf sources k p x bits) (proofOf sources k p x bits)
      (C10TotalDecode.evaluate (pcpp := pcppOf sources k p x bits)) (workerOf sources k p S hs) (bigTwo S.e) S.budget n x bits
      (gResult S.e) (C10TailCompose.scr S.e) (widthOf sources k p S x bits) := by
  classical
  have hgate : LengthGate (constantsOf sources) (workerOf sources k p S hs) (bigTwo S.e)
      (gResult S.e) S.budget :=
    gate_of_compose S.e (constantsOf sources)
      (C10ComposeWidths.innerOf' S.e hs.he (body sources k p S) (tailMachine sources)) S.budget
  by_cases hc : Soundness.cutoff (constantsOf sources) ≤ n
  · let hrun := above_run sources k p S hs x bits hc
    let A := hrun.choose
    have hstep := hrun.choose_spec.1
    have hbit := hrun.choose_spec.2.1
    have hrec := hrun.choose_spec.2.2
    refine {
      gate := hgate
      heads := fun _ => 0
      exit := A
      run := hstep
      realizes := fun _ ph => transport (rawRealizes sources k p S hs x bits hc ph)
        (fun _ => 0) A hstep (hrec ph)
      hshared := fun _ _ => rfl
      estimate := fun ph => (((foldedOf sources k p S x bits ph).value : ℚ) : ℝ)
      hestimate := fun _ _ => rfl
      accepts_iff := ?_ }
    exact hbit.trans ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · let hrun := below_run sources k p S hs x bits (by omega)
    let H := hrun.choose
    let A := hrun.choose_spec.choose
    have hstep := hrun.choose_spec.choose_spec.1
    have hbit := hrun.choose_spec.choose_spec.2
    refine {
      gate := hgate
      heads := H
      exit := A
      run := hstep
      realizes := fun h => (hc h).elim
      hshared := fun h => (hc h).elim
      estimate := fun _ => 0
      hestimate := fun h => (hc h).elim
      accepts_iff := ?_ }
    constructor
    · intro h
      have habs : (false : Bool) = true := hbit.symm.trans h
      cases habs
    · intro h
      exact (hc h.1).elim

end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
