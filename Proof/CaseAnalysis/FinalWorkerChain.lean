import Proof.CaseAnalysis.FinalRealizes
import Proof.CaseAnalysis.FinalLengthGate
import Proof.CaseAnalysis.RowsEstimatorCoefficientsLoop
import Proof.Hierarchy.CompetitorSumLoop
import Proof.CaseAnalysis.RowsOriginalClauseLoop

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 One record is one AND-four supplier call -/

/-- **One physical record = one AND-four supplier call for one monomial.**
The record carries the monomial's rational coefficient in its `coefficient`
field and the supplier's answer as the `count / denominator` pair: exactly
`Entry.estimate_value`'s two factors.  Paper C.10.1, "expanding it into
AND-four supplier calls". -/
structure Calls {Atom : Type} (supplier : List Atom → ℚ)
    (monomial : CircuitMonomial Atom 4) (entry : Entry) : Prop where
  /-- The record's rational coefficient is the monomial's coefficient. -/
  coefficient : entry.coefficient.value = monomial.coefficient
  /-- The record's `count / denominator` is the supplier's answer to the
  monomial's factor list. -/
  answer : ((entry.count : ℚ) / (entry.denominator : ℚ)) = supplier monomial.factors

/-- **Every call stays inside the four-factor ABI.**  The paper's "degree at
most four in the guessed sums"; here it is a property of the type, so no
request can leave the ABI. -/
theorem Calls.factors_length_le_four {Atom : Type} {supplier : List Atom → ℚ}
    {monomial : CircuitMonomial Atom 4} {entry : Entry}
    (_hcalls : Calls supplier monomial entry) : monomial.factors.length ≤ 4 :=
  monomial.degree_le

/-! ## §2 The record stream's exact value -/

/-- The per-record contribution values, read off the calls. -/
theorem entries_map_estimate_value {Atom : Type} (supplier : List Atom → ℚ)
    (monomials : List (CircuitMonomial Atom 4)) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) monomials entries) :
    entries.map (fun entry => entry.estimate.value) =
      monomials.map (fun monomial => monomial.coefficient * supplier monomial.factors) := by
  induction hcalls with
  | nil => rfl
  | @cons monomial entry monomials entries hcall _ inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis]
      congr 1
      rw [Entry.estimate_value, hcall.coefficient, hcall.answer]

theorem folded_value_eq_estimatedMean {Atom : Type} (supplier : List Atom → ℚ)
    (width : ℕ) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate width) :
    (((CompetitorSumFold.folded CompetitorSumWidth.zero
        (contributions entries)).value : ℚ) : ℝ) =
      polynomial.estimatedMean supplier := by
  have hfold := CompetitorSumFold.folded_value
    (CompetitorSumWidth.width (contributions entries).length width)
    CompetitorSumWidth.zero (contributions entries)
    (CompetitorSumWidth.uniform_trace width (contributions entries) hvalid)
  have hzero : CompetitorSumWidth.zero.value = 0 := by
    norm_num [CompetitorSumWidth.zero, CompetitorValidity.Estimate.value]
  have hmap : (contributions entries).map CompetitorValidity.Estimate.value =
      polynomial.monomials.map
        (fun monomial => monomial.coefficient * supplier monomial.factors) := by
    rw [contributions, List.map_map]
    exact entries_map_estimate_value supplier polynomial.monomials entries hcalls
  rw [hfold, hzero, zero_add, hmap, ratListSum_cast, List.map_map,
    CircuitPolynomial.estimatedMean]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro monomial _
  simp only [Function.comp_apply]
  push_cast
  ring

/-! ## §3 The clause-address decomposition -/

/-- Appending two call lists. -/
theorem forall2_append {Beta Gamma : Type} (Relation : Beta → Gamma → Prop)
    {left right image preimage : List _}
    (hleft : List.Forall₂ Relation left image)
    (hright : List.Forall₂ Relation right preimage) :
    List.Forall₂ Relation (left ++ right) (image ++ preimage) := by
  induction hleft with
  | nil => simpa using hright
  | cons hhead _ inductionHypothesis => exact List.Forall₂.cons hhead inductionHypothesis

/-- Concatenating call lists along an index list. -/
theorem forall2_flatMap {Alpha Beta Gamma : Type} (Relation : Beta → Gamma → Prop)
    (indices : List Alpha) (left : Alpha → List Beta) (right : Alpha → List Gamma)
    (hstep : ∀ index, List.Forall₂ Relation (left index) (right index)) :
    List.Forall₂ Relation (indices.flatMap left) (indices.flatMap right) := by
  induction indices with
  | nil => exact List.Forall₂.nil
  | cons index indices inductionHypothesis =>
      simp only [List.flatMap_cons]
      exact forall2_append Relation (hstep index) inductionHypothesis

/-- Scaling a list-indexed polynomial sum distributes over the index list. -/
theorem scaled_sum_monomials {Atom : Type} {degree : ℕ} {Index : Type} (scalar : ℚ)
    (indices : List Index) (polynomial : Index → CircuitPolynomial Atom degree) :
    (CircuitPolynomial.scale scalar
        (polynomialSumList (indices.map polynomial))).monomials =
      indices.flatMap
        (fun index => (CircuitPolynomial.scale scalar (polynomial index)).monomials) := by
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      have hstep : (CircuitPolynomial.scale scalar
            (polynomialSumList ((index :: indices).map polynomial))).monomials =
          (polynomial index).monomials.map (CircuitMonomial.scale scalar) ++
            (CircuitPolynomial.scale scalar
              (polynomialSumList (indices.map polynomial))).monomials := by
        simp [CircuitPolynomial.scale, polynomialSumList]
      rw [hstep, inductionHypothesis]
      rfl

/-- **The site list is the PCPP clause address, and nothing else.**  The phase
polynomial's monomial list is literally the concatenation, over clause
addresses, of the monomial lists of the scaled site polynomials.  `BitInput n`
is never enumerated. -/
theorem phasePolynomial_monomials {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    (phasePolynomial phase pcpp coordinate systematicAtom).monomials =
      (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
        (fun address => (CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
          (sitePolynomial phase pcpp coordinate systematicAtom address)).monomials) := by
  rw [phasePolynomial, polynomialFinsetSum]
  exact scaled_sum_monomials _ _ _

/-- **The clause-address loop's call stream.**  If at each PCPP clause address
the machine emits one call per monomial of that address's scaled site
polynomial, then the concatenation over addresses is exactly the phase's call
stream.  This is what the physical repeat driver of §4 accumulates. -/
theorem calls_of_clauseAddresses {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} (supplier : List Atom → ℚ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (records : Fin (2 ^ pcpp.clauseBits) → List Entry)
    (hsite : ∀ address, List.Forall₂ (Calls supplier)
      (CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
        (sitePolynomial phase pcpp coordinate systematicAtom address)).monomials
      (records address)) :
    List.Forall₂ (Calls supplier)
      (phasePolynomial phase pcpp coordinate systematicAtom).monomials
      ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap records) := by
  rw [phasePolynomial_monomials]
  exact forall2_flatMap _ _ _ _ hsite

/-! ## §4 The physical clause-address driver -/

/-- **The loop ranges over PCPP clause addresses.**  `CloseoutRowsOriginalClauseLoop.run`
at `N := 2 ^ pcpp.clauseBits`: the unary driver word has one cell per clause
address, and the body is requested exactly at the addresses below it. -/
theorem clauseAddress_loop {tapes states arity : ℕ} {circuit : BooleanCircuit arity}
    (body : Machine tapes states) (pcpp : PointwisePCPP circuit) (cost : ℕ)
    (heads : ℕ → Fin tapes → ℕ) (tape : ℕ → Fin tapes → List Bool)
    (site : ∀ address < 2 ^ pcpp.clauseBits,
      Step body cost (heads address) (tape address)
        (heads (address + 1)) (tape (address + 1))) :
    Step (RepeatMachine.machine body (fun _ _ => true))
      (2 ^ pcpp.clauseBits * (cost + 3) + 3)
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (tape 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits)))
      (Fin.addCases (heads (2 ^ pcpp.clauseBits)) (fun _ : Fin 1 => 1))
      (Fin.addCases (tape (2 ^ pcpp.clauseBits))
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits))) :=
  CloseoutRowsOriginalClauseLoop.run body (2 ^ pcpp.clauseBits) cost heads tape site

/-! ## §5 The gated worker -/

/-- **The worker.**  P4's length gate is its front: the gate counts the frozen
onset out of the framed input in `4*C+3` steps, rejects below the cutoff, and
otherwise hands the estimator body the verifier's own tapes with every head at
zero and the single scratch slot `flag` carrying `[true]`. -/
def worker {tapes bodyStates : ℕ} (onset : ℕ) (input flag result : Fin tapes)
    (body : Machine tapes bodyStates) :
    Machine tapes ((4 * onset + 2) + (2 + bodyStates)) :=
  gated onset input flag result body

/-- **The budget is a function of the input length alone.**  The gate costs
`4*C+3` and the body is charged `fuel len`; neither term mentions the witness
string, which is what `Weak.StepAtInputs` requires of a `budget : ℕ → ℕ`. -/
def workerBudget (onset : ℕ) (fuel : ℕ → ℕ) (len : ℕ) : ℕ :=
  (4 * onset + 1) + 1 + (fuel len + 1)

/-- **The docked front.**  A body receipt at the gate's exit becomes a worker
receipt at the verifier's input tapes, at a budget that depends only on `len`.
`bits` is universally quantified at a fixed budget: no stage's runtime may
depend on the witness length. -/
theorem worker_step {tapes bodyStates : ℕ} (onset : ℕ)
    (input flag result : Fin tapes) (body : Machine tapes bodyStates)
    (htapes : 2 ≤ tapes) (hzero : input.val = 0) (fuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (heads : Fin tapes → ℕ) (exit : Fin tapes → List Bool)
    (hbody : Step body (fuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
          result).inputTapes (List.ofFn x) bits) 0 true) heads exit) :
    Step (worker onset input flag result body) (workerBudget onset fuel len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
        result).inputTapes (List.ofFn x) bits) heads exit :=
  gated_verifier_pass onset input flag result body htapes hzero len x bits honset
    (fuel len) heads exit hbody

/-! ## §6 The junction, and the phase realization -/

structure EstimatorBody {Atom : Type} {tapes bodyStates : ℕ}
    (body : Machine tapes bodyStates) (onset : ℕ)
    (input flag result port : Fin tapes) (htapes : 2 ≤ tapes) (fuel : ℕ → ℕ)
    (width recordWidth : ℕ) (supplier : List Atom → ℚ)
    (polynomial : CircuitPolynomial Atom 4)
    (len : ℕ) (x : BitInput len) (bits : List Bool) where
  /-- One record per monomial: the machine's AND-four supplier calls. -/
  entries : List Entry
  heads : Fin tapes → ℕ
  exit : Fin tapes → List Bool
  /-- **The call stream is the paper's expansion.** -/
  hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries
  /-- Every contribution fits the fold's scalar width. -/
  hentries : ∀ estimate ∈ contributions entries,
    CompetitorValidity.Estimate.Valid estimate recordWidth
  /-- The fold itself fits the output width. -/
  hfolded : CompetitorValidity.Estimate.Valid
    (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) width
  /-- The physical receipt, at the gate's exit, at an `n`-determined budget. -/
  run : Step body (fuel len) (fun _ => 0)
    (exitTapes flag
      ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
        result).inputTapes (List.ofFn x) bits) 0 true) heads exit
  /-- The output port carries the encoder's own record word for the fold. -/
  hencoded : exit port =
    CloseoutRowsEstimatorCoefficients.Stream.recordWord width
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1

/-- **The clause-address constructor.**  A body that emits, at each PCPP clause
address, the calls of that address's scaled site polynomial, has the phase's
whole call stream in the concatenation over addresses -- which is the stream
the repeat driver of §4 accumulates. -/
noncomputable def EstimatorBody.ofClauseAddresses {Atom : Type} {tapes bodyStates arity : ℕ}
    {circuit : BooleanCircuit arity}
    {body : Machine tapes bodyStates} {onset : ℕ}
    {input flag result port : Fin tapes} {htapes : 2 ≤ tapes} {fuel : ℕ → ℕ}
    {width recordWidth : ℕ} {supplier : List Atom → ℚ}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    {len : ℕ} {x : BitInput len} {bits : List Bool}
    (records : Fin (2 ^ pcpp.clauseBits) → List Entry)
    (hsite : ∀ address, List.Forall₂ (Calls supplier)
      (CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
        (sitePolynomial phase pcpp coordinate systematicAtom address)).monomials
      (records address))
    (heads : Fin tapes → ℕ) (exit : Fin tapes → List Bool)
    (hentries : ∀ estimate ∈ contributions
        ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap records),
      CompetitorValidity.Estimate.Valid estimate recordWidth)
    (hfolded : CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero
        (contributions
          ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap records))) width)
    (run : Step body (fuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
          result).inputTapes (List.ofFn x) bits) 0 true) heads exit)
    (hencoded : exit port =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width
        (CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions
            ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap records))) 1 1) :
    EstimatorBody body onset input flag result port htapes fuel width recordWidth
      supplier (phasePolynomial phase pcpp coordinate systematicAtom) len x bits where
  entries := (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap records
  heads := heads
  exit := exit
  hcalls := calls_of_clauseAddresses supplier phase pcpp coordinate systematicAtom
    records hsite
  hentries := hentries
  hfolded := hfolded
  run := run
  hencoded := hencoded

noncomputable def worker_realizes {tapes bodyStates : ℕ} {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
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
    (supplier : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤
        failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (input flag result port : Fin tapes)
    (body : Machine tapes bodyStates) (htapes : 2 ≤ tapes) (hzero : input.val = 0)
    (fuel : ℕ → ℕ) (width recordWidth : ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (estimator : EstimatorBody body onset input flag result port htapes fuel width
      recordWidth supplier (phasePolynomial phase pcpp coordinate systematicAtom)
      len x bits) :
    Realizes phase constants pcpp proofValue evaluate
      (worker onset input flag result body) (workerBudget onset fuel len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
        result).inputTapes (List.ofFn x) bits)
      port width :=
  realizes_of_phasePolynomial phase constants pcpp evaluate proofValue coordinate
    hcoordinate systematicAtom hsystematic supplier failure hfailure hpoint mass
    hmass hbudget (worker onset input flag result body) (workerBudget onset fuel len)
    (fun _ => 0)
    ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
      result).inputTapes (List.ofFn x) bits)
    port width estimator.heads estimator.exit
    (worker_step onset input flag result body htapes hzero fuel len x bits honset
      estimator.heads estimator.exit estimator.run)
    (CompetitorSumFold.folded CompetitorSumWidth.zero
      (contributions estimator.entries))
    estimator.hfolded estimator.hencoded
    (folded_value_eq_estimatedMean supplier recordWidth
      (phasePolynomial phase pcpp coordinate systematicAtom) estimator.entries
      estimator.hcalls estimator.hentries)

/-- **The accuracy the worker inherits.**  P2's `accurate_of_realizes` applied
to `worker_realizes`: the exit port carries an `Estimate` within
`eps_est := min{zeta, (c_p - s_p)/20}` of the paper's grouped phase mean.
Paper C.10.2. -/
theorem worker_accurate {tapes bodyStates : ℕ} {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
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
    (supplier : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤
        failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (input flag result port : Fin tapes)
    (body : Machine tapes bodyStates) (htapes : 2 ≤ tapes) (hzero : input.val = 0)
    (fuel : ℕ → ℕ) (width recordWidth : ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (estimator : EstimatorBody body onset input flag result port htapes fuel width
      recordWidth supplier (phasePolynomial phase pcpp coordinate systematicAtom)
      len x bits) :
    |(((CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions estimator.entries)).value : ℚ) : ℝ) -
        CloseoutRowsOriginalSchedule.mean phase pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) :=
  accurate_of_realizes
    (worker_realizes phase constants pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic supplier failure hfailure hpoint mass hmass hbudget
      onset input flag result port body htapes hzero fuel width recordWidth len x bits
      honset estimator)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
