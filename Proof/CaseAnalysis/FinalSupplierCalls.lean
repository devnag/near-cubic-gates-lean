import Proof.CaseAnalysis.FinalWorkerWidth
import Proof.Hierarchy.CompetitorMonomialProducts

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The coefficient slot: one rational, exactly -/

def coefficientEstimate (coefficient : ℚ) : CompetitorValidity.Estimate :=
  ⟨CompetitorMonomialProducts.positive coefficient,
    CompetitorMonomialProducts.negative coefficient, coefficient.den⟩

/-- The coefficient slot decodes to the coefficient. -/
theorem coefficientEstimate_value (coefficient : ℚ) :
    (coefficientEstimate coefficient).value = coefficient := by
  simp only [coefficientEstimate, CompetitorValidity.Estimate.value]
  rw [CompetitorMonomialProducts.sign_parts, Rat.num_div_den]

/-! ## §2 The supplier's answer channel -/

def countSupplier {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ) :
    List Atom → ℚ :=
  fun factors => ((answer factors : ℚ) / (denominator : ℚ))

/-- **One monomial, one call, one record.**  The record carries the monomial's
coefficient in its coefficient slot and the supplier's answer to the monomial's
at-most-four factor list in its count/denominator slot. -/
def callEntry {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ)
    (monomial : CircuitMonomial Atom 4) : Entry :=
  ⟨coefficientEstimate monomial.coefficient, answer monomial.factors, denominator⟩

/-- **`countSupplier` is answered by the emitted record.**  Both conjuncts of
`Calls` hold for the emitted entry, for the supplier that the answer channel
defines. -/
theorem callEntry_calls_countSupplier {Atom : Type} (answer : List Atom → ℕ)
    (denominator : ℕ) (monomial : CircuitMonomial Atom 4) :
    Calls (countSupplier answer denominator) monomial
      (callEntry answer denominator monomial) where
  coefficient := coefficientEstimate_value monomial.coefficient
  answer := rfl

theorem callEntry_calls {Atom : Type} (supplier : List Atom → ℚ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (monomial : CircuitMonomial Atom 4) :
    Calls supplier monomial (callEntry answer denominator monomial) where
  coefficient := coefficientEstimate_value monomial.coefficient
  answer := hsupplier monomial.factors

/-- **The call stays inside the four-factor ABI.**  Paper C.10: "degree at most
four in the guessed sums". -/
theorem callEntry_factors_length_le_four {Atom : Type} (supplier : List Atom → ℚ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (monomial : CircuitMonomial Atom 4) : monomial.factors.length ≤ 4 :=
  Calls.factors_length_le_four (callEntry_calls supplier answer denominator hsupplier monomial)

/-! ## §3 One record per monomial -/

/-- The call stream of one polynomial: one record per monomial, in order. -/
def callRecords {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ)
    (polynomial : CircuitPolynomial Atom 4) : List Entry :=
  polynomial.monomials.map (callEntry answer denominator)

/-- **One record per monomial, and each record is that monomial's call.** -/
theorem callRecords_calls {Atom : Type} (supplier : List Atom → ℚ)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (polynomial : CircuitPolynomial Atom 4) :
    List.Forall₂ (Calls supplier) polynomial.monomials
      (callRecords answer denominator polynomial) := by
  unfold callRecords
  induction polynomial.monomials with
  | nil => exact List.Forall₂.nil
  | cons monomial monomials inductionHypothesis =>
      exact List.Forall₂.cons
        (callEntry_calls supplier answer denominator hsupplier monomial)
        inductionHypothesis

/-- The stream is exactly as long as the monomial list: one call per monomial,
counted. -/
theorem callRecords_length {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ)
    (polynomial : CircuitPolynomial Atom 4) :
    (callRecords answer denominator polynomial).length = polynomial.monomials.length := by
  simp [callRecords]

/-! ## §4 The record width -/

/-- **One record fits the scalar bank.**  Every field of the emitted record is
bounded by the bank's own width: the coefficient's two sign parts and its
denominator, and the supplier's count and denominator.  No constant is chosen
here -- `entryWidth` is the bank width the fold of
`RepairCloseoutFinalC10WorkerFold` already runs at. -/
theorem callEntry_valid {Atom : Type} (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ) (monomial : CircuitMonomial Atom 4)
    (hpositive : CompetitorMonomialProducts.positive monomial.coefficient < 2 ^ entryWidth)
    (hnegative : CompetitorMonomialProducts.negative monomial.coefficient < 2 ^ entryWidth)
    (hcoefficientDenominator : monomial.coefficient.den < 2 ^ entryWidth)
    (hcount : answer monomial.factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth)
    (hdenominatorPositive : 0 < denominator) :
    Entry.Valid entryWidth (callEntry answer denominator monomial) where
  positive := hpositive
  negative := hnegative
  coefficientDenominator := hcoefficientDenominator
  coefficientDenominatorPositive := monomial.coefficient.pos
  count := hcount
  denominator := hdenominator
  denominatorPositive := hdenominatorPositive

/-- The bound on a polynomial's coefficients that the bank width has to carry. -/
def CoefficientsFit {Atom : Type} (entryWidth : ℕ)
    (polynomial : CircuitPolynomial Atom 4) : Prop :=
  ∀ monomial ∈ polynomial.monomials,
    CompetitorMonomialProducts.positive monomial.coefficient < 2 ^ entryWidth ∧
      CompetitorMonomialProducts.negative monomial.coefficient < 2 ^ entryWidth ∧
      monomial.coefficient.den < 2 ^ entryWidth

/-- Every emitted record fits the bank. -/
theorem callRecords_valid {Atom : Type} (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ) (polynomial : CircuitPolynomial Atom 4)
    (hcoefficients : CoefficientsFit entryWidth polynomial)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth)
    (hdenominatorPositive : 0 < denominator) :
    ∀ entry ∈ callRecords answer denominator polynomial, Entry.Valid entryWidth entry := by
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨monomial, hmonomial, rfl⟩
  obtain ⟨hpositive, hnegative, hcoefficientDenominator⟩ := hcoefficients monomial hmonomial
  exact callEntry_valid answer denominator entryWidth monomial hpositive hnegative
    hcoefficientDenominator (hcount monomial.factors) hdenominator hdenominatorPositive

/-- The per-record contributions are valid at the fold's own scalar width, which
is what `EstimatorBody.hentries` asks for. -/
theorem callRecords_contributions_valid {Atom : Type} (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ) (polynomial : CircuitPolynomial Atom 4)
    (hvalid : ∀ entry ∈ callRecords answer denominator polynomial,
      Entry.Valid entryWidth entry) :
    ∀ estimate ∈ contributions (callRecords answer denominator polynomial),
      CompetitorValidity.Estimate.Valid estimate
        (CompetitorRationalDecision.width entryWidth) := by
  intro estimate hestimate
  rcases List.mem_map.mp hestimate with ⟨entry, hentry, rfl⟩
  exact Entry.valid_estimate entryWidth entry (hvalid entry hentry)

/-! ## §5 The clause address -/

/-- **The calls of one PCPP clause address.**  P3a's site polynomial at that
address, carrying the phase's uniform `1/2^clauseBits`.  The site index is the
clause address and nothing else. -/
noncomputable def siteCalls {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
    (sitePolynomial phase pcpp coordinate systematicAtom address)

/-- The record stream emitted at one PCPP clause address. -/
noncomputable def siteRecords {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) : List Entry :=
  callRecords answer denominator (siteCalls phase pcpp coordinate systematicAtom address)

/-! ## §6 S1 -- the per-clause-address call production, with its receipt -/

theorem calls_run {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (supplier : List Atom → ℚ) (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth) (hdenominatorPositive : 0 < denominator)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (address : Fin (2 ^ pcpp.clauseBits)) :
    List.Forall₂ (Calls supplier)
        (siteCalls phase pcpp coordinate systematicAtom address).monomials
        (siteRecords answer denominator phase pcpp coordinate systematicAtom address) ∧
      (∀ entry ∈ siteRecords answer denominator phase pcpp coordinate systematicAtom address,
        Entry.Valid entryWidth entry) ∧
      (∀ monomial ∈ (siteCalls phase pcpp coordinate systematicAtom address).monomials,
        monomial.factors.length ≤ 4 ∧
          ∃ receipt,
            run CompetitorCountRecordAppend.machine
                (CompetitorCountRecordAppend.budget entryWidth)
                (CloseoutRowsEstimatorCoefficients.Append.input entryWidth
                  (coefficientEstimate monomial.coefficient) (answer monomial.factors)
                  denominator) = some receipt ∧
              receipt.steps ≤ CompetitorCountRecordAppend.budget entryWidth ∧
              receipt.final.tapes 28 =
                CloseoutRowsEstimatorCoefficients.Stream.entryWord entryWidth
                  (callEntry answer denominator monomial)) := by
  refine ⟨callRecords_calls supplier answer denominator hsupplier _,
    callRecords_valid answer denominator entryWidth _ (hcoefficients address) hcount
      hdenominator hdenominatorPositive, ?_⟩
  intro monomial _hmonomial
  obtain ⟨receipt, hrun, hsteps, hword, _hcoefficient, _hanswer, hfour⟩ :=
    call_record_run (supplier := supplier) (monomial := monomial)
      (entry := callEntry answer denominator monomial) entryWidth
      (callEntry_calls supplier answer denominator hsupplier monomial)
  exact ⟨hfour, receipt, hrun, hsteps, hword⟩

/-! ## §7 The phase's whole call stream -/

/-- **The phase's call stream is the concatenation over clause addresses.**
W1's `calls_of_clauseAddresses`, fed by S1's per-address production: the
monomials of the phase polynomial are matched, one for one, by the records the
clause-address loop emits.  This is `EstimatorBody.hcalls`. -/
theorem phase_calls {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (supplier : List Atom → ℚ) (answer : List Atom → ℕ) (denominator : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors) :
    List.Forall₂ (Calls supplier)
      (phasePolynomial phase pcpp coordinate systematicAtom).monomials
      ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
        (siteRecords answer denominator phase pcpp coordinate systematicAtom)) :=
  calls_of_clauseAddresses supplier phase pcpp coordinate systematicAtom
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)
    (fun address => callRecords_calls supplier answer denominator hsupplier
      (siteCalls phase pcpp coordinate systematicAtom address))

/-- Every record of the whole phase stream fits the bank. -/
theorem phase_records_valid {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (answer : List Atom → ℕ) (denominator entryWidth : ℕ)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth) (hdenominatorPositive : 0 < denominator)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address)) :
    ∀ entry ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
        (siteRecords answer denominator phase pcpp coordinate systematicAtom),
      Entry.Valid entryWidth entry := by
  intro entry hentry
  rcases List.mem_flatMap.mp hentry with ⟨address, _haddress, hentry'⟩
  exact callRecords_valid answer denominator entryWidth _ (hcoefficients address) hcount
    hdenominator hdenominatorPositive entry hentry'

/-- The whole phase stream's contributions are valid at the fold's scalar width:
`EstimatorBody.hentries`. -/
theorem phase_contributions_valid {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (answer : List Atom → ℕ) (denominator entryWidth : ℕ)
    (hvalid : ∀ entry ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
        (siteRecords answer denominator phase pcpp coordinate systematicAtom),
      Entry.Valid entryWidth entry) :
    ∀ estimate ∈ contributions
        ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
          (siteRecords answer denominator phase pcpp coordinate systematicAtom)),
      CompetitorValidity.Estimate.Valid estimate
        (CompetitorRationalDecision.width entryWidth) := by
  intro estimate hestimate
  rcases List.mem_map.mp hestimate with ⟨entry, hentry, rfl⟩
  exact Entry.valid_estimate entryWidth entry (hvalid entry hentry)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
