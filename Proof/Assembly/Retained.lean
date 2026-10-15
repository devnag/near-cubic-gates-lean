import Proof.Assembly.OrderedCalls
import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.RowsOriginalClauseLoop

/-!
The retained C10 consumer uses the selected phase fold, actual clause driver,
and source-fixed head-aware tail. Accuracy is required only for monomials in
the actual phase. Entry and clause transitions keep their physical tapes,
heads and budgets explicit. No whole-worker run or Runtime is inferred.
-/
namespace OrderedCallPhases.Retained
open NearCubicWires RepairOrdinary LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairRepresentation SourceInterfaces RepairSource.CompetitorRationalGap
open RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule CloseoutRowsEstimatorCoefficients.Stream
open CloseoutFinalC10Realizes CloseoutFinalC10WorkerFold
open RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The actual phase fold realizes its selected monomials, with local inputs. -/
noncomputable def local_realizes
    (L : Nat)
    (B : Nat)
    (arity : Nat)
    (hL : 301 ≤ L)
    (hFresh : L+1154<B)
    (Atom : Type)
    (circuit : NearCubicWires.BooleanCircuit arity)
    (source : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm)
    (constants : NearCubicWires.RepairSource.CompetitorRationalGap.Constants source)
    (pcpp : NearCubicWires.SourceInterfaces.PointwisePCPP circuit)
    (ph : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (evaluate : Atom → NearCubicWires.BitInput arity → Bool)
    (proofValue : NearCubicWires.BitInput arity → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → Real)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → NearCubicWires.ComponentwisePolynomial.CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (supplier : List Atom → Rat)
    (failure : Real)
    (mass : Real)
    (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Fin B → Nat)
    (A : Fin B → List Bool)
    (hcoordinate : NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.CoordinateExpands pcpp evaluate proofValue coordinate)
    (hsystematic : ∀ index input, evaluate (systematicAtom index) input = NearCubicWires.SourceInterfaces.parityOn (pcpp.systematicSupport index) input)
    (hfailure : 0 ≤ failure)
    (hpoint : ∀ monomial ∈ (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials, |((supplier monomial.factors : Rat) : Real) - NearCubicWires.SupplierPipeline.conjunctionProbability evaluate monomial.factors| ≤ failure)
    (hmass : (((NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat) : Real) ≤ mass)
    (hbudget : failure * mass ≤ ((NearCubicWires.RepairSource.CompetitorRationalGap.estimationTolerance constants (NearCubicWires.RepairSource.CompetitorRationalGap.zeta constants) : Rat) : Real))
    (hcalls : OrderedCallPhases.OrderedCalls supplier (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
    (hvalid : ∀ entry ∈ entries, NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid b entry)
    (hHw : ∀ i, H (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (hHf : ∀ i, H (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (hdriver : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
    (hcount : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 90) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word entries.length)
    (hstream : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 81) = NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.words b entries)
    (hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (hfresh : ∀ i : Fin 278, 219 ≤ i.val → A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (hrecord : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)=[])
    (hlog : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 218)=[])
    : NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph) (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) H A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215) (NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold.foldWidth (NearCubicWires.RepairOrdinary.CompetitorRationalDecision.width b) entries) :=
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary
  NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
  NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
  NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
  NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
  NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream in
by
  classical
  let receipt := CloseoutFinalC10RetainedPhaseFold.run L B hL hFresh ph b entries H A
      hvalid hHw hHf hdriver hcount hstream hblank hfresh hrecord hlog
  let out := receipt.choose
  have hrun := receipt.choose_spec.1
  have hencoded := receipt.choose_spec.2.1
  have hentries := CloseoutFinalC10WorkerDockBody.contributions_valid b entries hvalid
  refine {
    ι := Fin (phasePolynomial ph pcpp coordinate systematicAtom).monomials.length
    index := Finset.univ
    coefficient := fun i => (((phasePolynomial ph pcpp coordinate systematicAtom).monomials[i].coefficient : Rat) : Real)
    circuits := fun i => (phasePolynomial ph pcpp coordinate systematicAtom).monomials[i].factors
    estimate := fun i => ((supplier (phasePolynomial ph pcpp coordinate systematicAtom).monomials[i].factors : Rat) : Real)
    failure := failure
    mass := mass
    hfailure := hfailure
    hexpansion := mean_eq_sum_conjunctionProbability ph pcpp evaluate proofValue coordinate hcoordinate systematicAtom hsystematic
    hpoint := ?_
    hmass := ?_
    hbudget := hbudget
    heads := H
    exit := out
    run := hrun
    result := CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)
    hvalid := CloseoutFinalC10WorkerWidth.answer_valid _ entries hentries
    hencoded := hencoded
    hvaluesum := ?_
  }
  · intro i _hi
    exact hpoint _ (List.getElem_mem _)
  · rw [coefficientMass_eq_finsetSum]
    exact hmass
  · rw [OrderedCallPhases.folded_value_of_orderedCalls supplier (CompetitorRationalDecision.width b)
      (phasePolynomial ph pcpp coordinate systematicAtom) entries hcalls hentries,
      estimatedMean_eq_finsetSum]

end
end OrderedCallPhases.Retained
