import Proof.CaseAnalysis.FinalStageWidths
import Proof.CaseAnalysis.FinalSupplierAccuracy

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionRecords

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 An arbitrary per-record stream -/

/-- `Forall₂ (Calls supplier)` for a record stream produced pointwise, with no
relation whatever between one record and the next. -/
theorem forall2_calls_map {Atom : Type} (supplier : List Atom → ℚ)
    (record : CircuitMonomial Atom 4 → Entry)
    (monomials : List (CircuitMonomial Atom 4))
    (hrecord : ∀ monomial ∈ monomials, Calls supplier monomial (record monomial)) :
    List.Forall₂ (Calls supplier) monomials (monomials.map record) := by
  induction monomials with
  | nil => exact List.Forall₂.nil
  | cons monomial rest inductionHypothesis =>
      exact List.Forall₂.cons (hrecord monomial (List.mem_cons_self ..))
        (inductionHypothesis fun entry hentry =>
          hrecord entry (List.mem_cons_of_mem monomial hentry))

/-- Validity of a pointwise-produced stream. -/
theorem valid_of_map {Atom : Type} (entryWidth : ℕ)
    (record : CircuitMonomial Atom 4 → Entry)
    (monomials : List (CircuitMonomial Atom 4))
    (hrecord : ∀ monomial ∈ monomials, Entry.Valid entryWidth (record monomial)) :
    ∀ entry ∈ monomials.map record, Entry.Valid entryWidth entry := by
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨monomial, hmonomial, rfl⟩
  exact hrecord monomial hmonomial

/-- **The phase's record stream, at an arbitrary per-record denominator.**  Same
shape as `phaseRecords` (`Proof/CaseAnalysis/FinalWorkerDockSeam.lean`) -- the
concatenation over PCPP clause addresses of one record per monomial -- except
that the record is an arbitrary function of the address AND the monomial, so each
record carries its own `denominator` field. -/
noncomputable def phaseRecords' {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) : List Entry :=
  (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
    (fun address =>
      (siteCalls phase pcpp coordinate systematicAtom address).monomials.map (record address))

/-- **`EstimatorBody.hcalls` at arbitrary per-record denominators.** -/
theorem phaseRecords'_calls {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (supplier : List Atom → ℚ)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (hrecord : ∀ (address : Fin (2 ^ pcpp.clauseBits)) monomial,
      monomial ∈ (siteCalls phase pcpp coordinate systematicAtom address).monomials →
        Calls supplier monomial (record address monomial)) :
    List.Forall₂ (Calls supplier)
      (phasePolynomial phase pcpp coordinate systematicAtom).monomials
      (phaseRecords' phase pcpp coordinate systematicAtom record) :=
  calls_of_clauseAddresses supplier phase pcpp coordinate systematicAtom
    (fun address =>
      (siteCalls phase pcpp coordinate systematicAtom address).monomials.map (record address))
    (fun address => forall2_calls_map supplier (record address) _ (hrecord address))

/-- **`EstimatorBody.hentries` at arbitrary per-record denominators.**  The ONLY
uniform quantity retained is the bank's bit width. -/
theorem phaseRecords'_valid {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (entryWidth : ℕ)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (hrecord : ∀ (address : Fin (2 ^ pcpp.clauseBits)) monomial,
      monomial ∈ (siteCalls phase pcpp coordinate systematicAtom address).monomials →
        Entry.Valid entryWidth (record address monomial)) :
    ∀ entry ∈ phaseRecords' phase pcpp coordinate systematicAtom record,
      Entry.Valid entryWidth entry := by
  intro entry hentry
  rcases List.mem_flatMap.mp hentry with ⟨address, _, hentry'⟩
  exact valid_of_map entryWidth (record address) _ (hrecord address) entry hentry'

/-! ## §2 The exact-fraction record, and that its denominators may genuinely differ -/

/-- **A.13.9's record shape.**  Numerator and denominator are arbitrary functions
of the address and the monomial; the only constraint is the one `Calls` names. -/
def exactFractionRecord {Atom : Type} (clauseAddresses : ℕ)
    (num den : Fin clauseAddresses → CircuitMonomial Atom 4 → ℕ)
    (address : Fin clauseAddresses) (monomial : CircuitMonomial Atom 4) : Entry :=
  ⟨coefficientEstimate monomial.coefficient, num address monomial, den address monomial⟩

/-- The exact-fraction record `Calls` its supplier.  `hratio` is the whole
premise: the record's own fraction is the supplier's answer.  Nothing ties
`den address monomial` to `den address' monomial'`. -/
theorem exactFraction_record_calls {Atom : Type} {clauseAddresses : ℕ}
    (supplier : List Atom → ℚ)
    (num den : Fin clauseAddresses → CircuitMonomial Atom 4 → ℕ)
    (hratio : ∀ (address : Fin clauseAddresses) (monomial : CircuitMonomial Atom 4),
      ((num address monomial : ℚ) / (den address monomial : ℚ)) = supplier monomial.factors)
    (address : Fin clauseAddresses) (monomial : CircuitMonomial Atom 4) :
    Calls supplier monomial (exactFractionRecord clauseAddresses num den address monomial) where
  coefficient := coefficientEstimate_value monomial.coefficient
  answer := hratio address monomial

/-- **The exact-fraction stream fits the bank.**  The coefficient premise is the
EXISTING `CoefficientsFit` that `realizes_of_stage` already takes; the numerator
and denominator premises are the existing `hcount`/`hdenominator`/
`hdenominatorPositive`, now quantified per call.  No new premise class. -/
theorem exactFraction_records_valid {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (entryWidth : ℕ)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (hnum : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      num address monomial < 2 ^ entryWidth)
    (hden : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      den address monomial < 2 ^ entryWidth)
    (hdenPos : ∀ address monomial, 0 < den address monomial)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address)) :
    ∀ entry ∈ phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den),
      Entry.Valid entryWidth entry :=
  phaseRecords'_valid phase pcpp coordinate systematicAtom entryWidth
    (exactFractionRecord (2 ^ pcpp.clauseBits) num den)
    (fun address monomial hmonomial =>
      { positive := (hcoefficients address monomial hmonomial).1
        negative := (hcoefficients address monomial hmonomial).2.1
        coefficientDenominator := (hcoefficients address monomial hmonomial).2.2
        coefficientDenominatorPositive := monomial.coefficient.pos
        count := hnum address monomial hmonomial
        denominator := hden address monomial hmonomial
        denominatorPositive := hdenPos address monomial })

/-- **The production rows already produce the per-call pair, with no rescaling.**
`rowSupplier_eq_ratio` (`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`) is
literally the `hratio` premise above at `num := rowAnswer`, `den := rowDenominator`
-- A.13.9's own numerator over A.13.9's own `|\mathcal E| 2^q`.  Positivity is the
row family's own `rowCountPositive`.  No floor, no common scale, no
`seedExponent <= scale`. -/
theorem rowFraction_answers_its_supplier {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ) :
    (∀ factors : List (Circuit arity),
        ((rowAnswer rows arity factors : ℚ) / (rowDenominator rows arity factors : ℚ)) =
          rowSupplier rows arity factors) ∧
      (∀ factors : List (Circuit arity), 0 < rowDenominator rows arity factors) :=
  ⟨rowSupplier_eq_ratio rows arity,
    fun factors => Nat.mul_pos (rows.rowCountPositive ⟨arity, factors⟩) (Nat.two_pow_pos arity)⟩

/-! ## §3 The three consumer applications, at the actual list type and width formula -/

/-- **Consumers 1 and 2: `estimatorBody_of_stage` then `worker_realizes`.**

Every record carries its own denominator.  The premises that survive are:

* the PHYSICAL RECORD PRODUCER -- `bank`, `scratch`, `hready : DockReady`,
  `hentry : EmitEntry`, `hemit`, `hstage : Step stage ...`;
* the SAMPLER'S ACCURACY -- `failure`, `hfailure`, `hpoint`, `mass`, `hmass`,
  `hbudget`;
* the record's own bit width and positivity -- `hnum`, `hden`, `hdenPos`,
  `hcoefficients`, which is `Entry.Valid`, i.e. the SAME premise class the common
  denominator route already carried, now quantified per call;
* the semantic wiring of the phase -- `hcoordinate`, `hsystematic`, `honset`.

There is no shared denominator, no common scale, no divisibility side condition
and no rounding bound anywhere in this signature. -/
noncomputable def exactFraction_realizes {Atom : Type} {arity : ℕ}
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
    (supplier : List Atom → ℚ) (entryWidth : ℕ)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (hratio : ∀ (address : Fin (2 ^ pcpp.clauseBits)) (monomial : CircuitMonomial Atom 4),
      ((num address monomial : ℚ) / (den address monomial : ℚ)) = supplier monomial.factors)
    (hnum : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      num address monomial < 2 ^ entryWidth)
    (hden : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      den address monomial < 2 ^ entryWidth)
    (hdenPos : ∀ address monomial, 0 < den address monomial)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (stage : Machine (218 + e) st) (stageFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (hready : DockReady entryWidth
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)) bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length) bank)
    (hemit : emitFuel =
      fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length))
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
          (phaseRecords' phase pcpp coordinate systematicAtom
            (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length)
        len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier
        (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
          (stagedBody stage emitLoader))
        (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits)
      (Fin.castAdd e port)
      (foldWidth (CompetitorRationalDecision.width entryWidth)
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den))) :=
  worker_realizes phase constants pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic supplier failure hfailure hpoint mass hmass hbudget
    onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
    (Fin.castAdd e port) (stagedBody stage emitLoader) (by omega) rfl
    (stagedFuel stageFuel emitFuel entryWidth
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length)
    (foldWidth (CompetitorRationalDecision.width entryWidth)
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)))
    (CompetitorRationalDecision.width entryWidth) len x bits honset
    (estimatorBody_of_stage stage stageFuel emitFuel onset entryWidth len x bits supplier
      (phasePolynomial phase pcpp coordinate systematicAtom)
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den))
      (phaseRecords'_calls phase pcpp coordinate systematicAtom supplier
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)
        (fun address monomial _ =>
          exactFraction_record_calls supplier num den hratio address monomial))
      (exactFraction_records_valid phase pcpp coordinate systematicAtom entryWidth num den
        hnum hden hdenPos hcoefficients)
      bank scratch hready hentry hemit hstage)

/-- **Consumer 3: `blockRuns_widths_of_stage` at the same per-record list and the
same width formula** `foldWidth (CompetitorRationalDecision.width entryWidth)`.
The two retained width words on tapes `274`/`275` are a function of that width and
of nothing else, so the per-record denominators do not reach them. -/
theorem exactFraction_widths {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {e st : ℕ} (he : 58 ≤ e)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth : ℕ)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (hnum : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      num address monomial < 2 ^ entryWidth)
    (hden : ∀ address, ∀ monomial ∈
        (siteCalls phase pcpp coordinate systematicAtom address).monomials,
      den address monomial < 2 ^ entryWidth)
    (hdenPos : ∀ address monomial, 0 < den address monomial)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (onset : ℕ) (stage : Machine (218 + e) st) (stageFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (hready : DockReady entryWidth
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)) bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth
      (phaseRecords' phase pcpp coordinate systematicAtom
        (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length) bank)
    (h0 : bank 0 = frame (List.ofFn x)) (h1 : bank 1 = frame bits)
    (hemit : emitFuel =
      fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length))
    (hstage : Step stage (stageFuel len) (fun _ => 0)
      (exitTapes (Fin.castAdd e flag)
        ((UAcceptanceCarrier.verifier
          (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
            (stagedBody stage emitLoader))
          (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) (Fin.addCases bank scratch))
    (hwidth : ∀ j,
      Fin.addCases bank scratch
          (NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths.retained e he j) =
        NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths.widthWord
          (foldWidth (CompetitorRationalDecision.width entryWidth)
            (phaseRecords' phase pcpp coordinate systematicAtom
              (exactFractionRecord (2 ^ pcpp.clauseBits) num den))) j) :
    NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths.BlockRunsWidths e he
      (stagedBody stage emitLoader)
      (stagedFuel stageFuel emitFuel entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length len)
      (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth)
          (phaseRecords' phase pcpp coordinate systematicAtom
            (exactFractionRecord (2 ^ pcpp.clauseBits) num den)))
        (CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions
            (phaseRecords' phase pcpp coordinate systematicAtom
              (exactFractionRecord (2 ^ pcpp.clauseBits) num den)))) 1 1)
      (foldWidth (CompetitorRationalDecision.width entryWidth)
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den))) :=
  NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths.blockRuns_widths_of_stage he stage
    stageFuel emitFuel onset entryWidth len x bits
    (phaseRecords' phase pcpp coordinate systematicAtom
      (exactFractionRecord (2 ^ pcpp.clauseBits) num den))
    (exactFraction_records_valid phase pcpp coordinate systematicAtom entryWidth num den
      hnum hden hdenPos hcoefficients)
    bank scratch hready hentry h0 h1 hemit hstage hwidth

theorem denominators_may_differ :
    ∃ (num den : List ℕ → ℕ) (supplier : List ℕ → ℚ),
      (∀ factors : List ℕ, ((num factors : ℚ) / (den factors : ℚ)) = supplier factors) ∧
      (∀ factors : List ℕ, 0 < den factors) ∧
      den [] ≠ den [0] :=
  ⟨fun factors => factors.length, fun factors => factors.length + 1,
    fun factors => ((factors.length : ℚ) / ((factors.length + 1 : ℕ) : ℚ)),
    fun _ => rfl, fun _ => Nat.succ_pos _, by decide⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionRecords
