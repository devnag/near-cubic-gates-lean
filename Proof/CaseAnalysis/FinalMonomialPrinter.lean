import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10MonomialPrinter

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 One monomial, one printed word -/

/-- **The word one monomial's call record occupies on the stream tape.**  This
is the CAPP row's record: the monomial's coefficient in the coefficient slot and
the at-most-four-atom conjunction's answer in the count slot. -/
noncomputable def monomialWord (entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (monomial : CircuitMonomial Atom 4) : List Bool :=
  CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
    [callEntry answer denominator monomial]

/-- A one-record stream is that record's word. -/
theorem words_singleton (b : ℕ) (entry : Entry) :
    CloseoutRowsEstimatorCoefficients.Stream.words b [entry]
      = CloseoutRowsEstimatorCoefficients.Stream.entryWord b entry := by
  simp [CloseoutRowsEstimatorCoefficients.Stream.words]

/-- **The printed word IS the record appender's output word.**  Nothing is
re-encoded here: `Stream.entryWord` of `callEntry` is definitionally
`Stream.recordWord` at the monomial's own three operands. -/
theorem monomialWord_eq (entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (monomial : CircuitMonomial Atom 4) :
    monomialWord entryWidth answer denominator monomial
      = CloseoutRowsEstimatorCoefficients.Stream.recordWord entryWidth
          (coefficientEstimate monomial.coefficient) (answer monomial.factors)
          denominator := by
  unfold monomialWord
  rw [words_singleton]
  rfl

theorem monomial_run (entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (monomial : CircuitMonomial Atom 4) :
    ∃ receipt,
      run CompetitorCountRecordAppend.machine
          (CompetitorCountRecordAppend.budget entryWidth)
          (CloseoutRowsEstimatorCoefficients.Append.input entryWidth
            (coefficientEstimate monomial.coefficient) (answer monomial.factors)
            denominator) = some receipt ∧
        receipt.steps ≤ CompetitorCountRecordAppend.budget entryWidth ∧
        receipt.final.tapes 28 = monomialWord entryWidth answer denominator monomial ∧
        receipt.final.heads 28 =
          (monomialWord entryWidth answer denominator monomial).length := by
  obtain ⟨receipt, hrun, hsteps, hword, hheads, _, _⟩ :=
    CloseoutRowsEstimatorCoefficients.Append.record_run entryWidth
      (coefficientEstimate monomial.coefficient) (answer monomial.factors) denominator
  refine ⟨receipt, hrun, hsteps, ?_, ?_⟩
  · rw [hword, monomialWord_eq]
  · rw [hheads, Function.update_self, monomialWord_eq]

/-! ## §2 The site polynomial's printed words, one per monomial -/

/-- **One printed word per monomial of the site polynomial, in the monomial
list's own order.**  The list's LENGTH is the paper's term count and its
entries carry the paper's coefficient mass. -/
noncomputable def siteWords (entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) : List (List Bool) :=
  (siteCalls phase pcpp coordinate systematicAtom address).monomials.map
    (monomialWord entryWidth answer denominator)

/-- The term count: one word per monomial, counted. -/
theorem siteWords_length (entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) :
    (siteWords entryWidth answer denominator phase pcpp coordinate systematicAtom
        address).length
      = (siteCalls phase pcpp coordinate systematicAtom address).monomials.length := by
  simp [siteWords]

/-- An encoded record stream over a mapped list splits into the per-source
printed words. -/
theorem words_map {α : Type} (b : ℕ) (f : α → Entry) (xs : List α) :
    CloseoutRowsEstimatorCoefficients.Stream.words b (xs.map f)
      = (xs.map fun a =>
          CloseoutRowsEstimatorCoefficients.Stream.words b [f a]).flatten := by
  induction xs with
  | nil => rfl
  | cons a xs inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, ← inductionHypothesis,
        words_singleton]
      simp [CloseoutRowsEstimatorCoefficients.Stream.words]

/-- **The clause address's whole encoded stream is the concatenation of its
monomials' printed words.**  This is the identity the round-`k` emitter owes:
`siteRecords` (`Proof/CaseAnalysis/FinalSupplierCalls.lean`) is one record per
monomial, so its encoding is one printed word per monomial. -/
theorem siteWords_flatten (entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) :
    (siteWords entryWidth answer denominator phase pcpp coordinate systematicAtom
        address).flatten
      = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (siteRecords answer denominator phase pcpp coordinate systematicAtom address) := by
  unfold siteWords siteRecords callRecords monomialWord
  rw [words_map]

/-! ## §3 The loop bank's data tape -/

/-- Tape `81` of the clause-address loop bank is the accumulated stream.  Stated
by tape NUMBER, not by a whole-layout equality, so it survives every bank
width. -/
theorem loopBank_data (extra entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) (i : Fin (218 + (60 + extra)))
    (hi : i.val = 81) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k i
      = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k) := by
  unfold loopBank C10SupplierCall.bank C10SupplierCall.bankAt
  rw [hi]
  norm_num

/-! ## §4 MONO -- the round's append, monomial by monomial -/

theorem site_printed (extra entryWidth : ℕ) (answer : List Atom → ℕ)
    (denominator : ℕ) (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) (hk : k < 2 ^ pcpp.clauseBits)
    (i : Fin (218 + (60 + extra))) (hi : i.val = 81) :
    ∃ address : Fin (2 ^ pcpp.clauseBits),
      (∀ monomial ∈ (siteCalls phase pcpp coordinate systematicAtom address).monomials,
          ∃ receipt,
            run CompetitorCountRecordAppend.machine
                (CompetitorCountRecordAppend.budget entryWidth)
                (CloseoutRowsEstimatorCoefficients.Append.input entryWidth
                  (coefficientEstimate monomial.coefficient) (answer monomial.factors)
                  denominator) = some receipt ∧
              receipt.steps ≤ CompetitorCountRecordAppend.budget entryWidth ∧
              receipt.final.tapes 28 =
                monomialWord entryWidth answer denominator monomial ∧
              receipt.final.heads 28 =
                (monomialWord entryWidth answer denominator monomial).length) ∧
        (siteWords entryWidth answer denominator phase pcpp coordinate systematicAtom
            address).length
          = (siteCalls phase pcpp coordinate systematicAtom address).monomials.length ∧
        loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness scratch (k + 1) i
          = loopBank extra entryWidth answer denominator phase pcpp coordinate
              systematicAtom input witness scratch k i
            ++ (siteWords entryWidth answer denominator phase pcpp coordinate
                systematicAtom address).flatten := by
  obtain ⟨address, haddress⟩ :=
    addressRecords_site answer denominator phase pcpp coordinate systematicAtom k hk
  refine ⟨address, fun monomial _hmonomial =>
      monomial_run entryWidth answer denominator monomial,
    siteWords_length entryWidth answer denominator phase pcpp coordinate systematicAtom
      address, ?_⟩
  rw [loopBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch (k + 1) i hi,
    loopBank_data extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch k i hi,
    siteWords_flatten, ← haddress, prefixRecords_succ, words_append]

theorem coefficientEstimate_eq_raw (coefficient : ℚ) :
    coefficientEstimate coefficient
      = CloseoutRowsEstimatorCoefficients.Fraction.raw [coefficient] := by
  have hnum : CloseoutRowsEstimatorCoefficients.Fraction.numerator [coefficient]
      = coefficient.num.natAbs := by
    simp [CloseoutRowsEstimatorCoefficients.Fraction.numerator]
  have hden : CloseoutRowsEstimatorCoefficients.Fraction.denominator [coefficient]
      = coefficient.den := by
    simp [CloseoutRowsEstimatorCoefficients.Fraction.denominator]
  have hparity : CloseoutRowsEstimatorCoefficients.Fraction.parity [coefficient]
      = decide (coefficient.num < 0) := by
    simp [CloseoutRowsEstimatorCoefficients.Fraction.parity]
  unfold coefficientEstimate CloseoutRowsEstimatorCoefficients.Fraction.raw
  rw [hnum, hden, hparity, CloseoutRowsEstimatorCoefficients.Fraction.signed]
  by_cases hsign : coefficient.num < 0
  · have hpositive : CompetitorMonomialProducts.positive coefficient = 0 := by
      unfold CompetitorMonomialProducts.positive
      omega
    have hnegative :
        CompetitorMonomialProducts.negative coefficient = coefficient.num.natAbs := by
      unfold CompetitorMonomialProducts.negative
      omega
    rw [hpositive, hnegative, if_pos (decide_eq_true hsign)]
  · have hpositive :
        CompetitorMonomialProducts.positive coefficient = coefficient.num.natAbs := by
      unfold CompetitorMonomialProducts.positive
      omega
    have hnegative : CompetitorMonomialProducts.negative coefficient = 0 := by
      unfold CompetitorMonomialProducts.negative
      omega
    rw [hpositive, hnegative, if_neg (by simp [hsign])]

end NearCubicWires.RepairSource.CloseoutFinal.C10MonomialPrinter
