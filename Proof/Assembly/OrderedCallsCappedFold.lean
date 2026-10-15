import Proof.Assembly.CappedCoordinate
import Proof.Assembly.Retained

/-! The retained physical fold at the actual capped coordinate. Accuracy is
required only for monomials of the selected phase. Its input stream, valid call
records, driver words, heads, and blank workspace stay explicit assumptions;
the canonical retained-fold theorem derives the fold execution. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true

namespace OrderedCallPhases.CappedFold
open NearCubicWires NearCubicWires.P1TopDown NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceInterfaces

noncomputable def capped_fold :
open NearCubicWires NearCubicWires.P1TopDown NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma)
 (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((NearCubicWires.RepairSource.SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool),
 let pcpp := pcppAt sources k clock x oracle
 let Atom := C10TotalDecode.Atom pcpp
 let constants := NearCubicWires.RepairSource.CloseoutFinal.constantsOf sources
 let coordinate := CappedCoordinates.coordinate sources k clock p den x oracle bits
 let systematicAtom := C10TotalDecode.Atom.systematic (pcpp := pcpp)
 let evaluate := C10TotalDecode.evaluate (pcpp := pcpp)
 let proofValue := P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits
 ∀ (ph : CloseoutRowsOriginalSchedule.Phase),
 let mass : Real := ((CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat)
∀ (L : Nat)
    (B : Nat)
    (hL : 301 ≤ L)
    (hFresh : L+1154<B)
    (supplier : List Atom → Rat)
    (failure : Real)
    (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Fin B → Nat)
    (A : Fin B → List Bool)
    (_hfailure : 0 ≤ failure)
    (_hpoint : ∀ monomial ∈ (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials, |((supplier monomial.factors : Rat) : Real) - NearCubicWires.SupplierPipeline.conjunctionProbability evaluate monomial.factors| ≤ failure)
    (_hbudget : failure * mass ≤ ((NearCubicWires.RepairSource.CompetitorRationalGap.estimationTolerance constants (NearCubicWires.RepairSource.CompetitorRationalGap.zeta constants) : Rat) : Real))
    (_hcalls : OrderedCallPhases.OrderedCalls supplier (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
    (_hvalid : ∀ entry ∈ entries, NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid b entry)
    (_hHw : ∀ i, H (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (_hHf : ∀ i, H (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (_hdriver : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
    (_hcount : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 90) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word entries.length)
    (_hstream : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 81) = NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.words b entries)
    (_hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hfresh : ∀ i : Fin 278, 219 ≤ i.val → A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hrecord : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)=[])
    (_hlog : A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 218)=[])
,
NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph) (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) H A (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215) (NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold.foldWidth (NearCubicWires.RepairOrdinary.CompetitorRationalDecision.width b) entries)
 := by
  intro sources gamma p k den clock n x oracle bits pcpp Atom constants coordinate systematicAtom
    evaluate proofValue ph mass L B hL hFresh supplier failure b entries H A
    hfailure hpoint hbudget hcalls hvalid hHw hHf hdriver hcount hstream hblank hfresh hrecord hlog
  exact OrderedCallPhases.Retained.local_realizes L B _ hL hFresh Atom _ _ constants pcpp
    ph evaluate proofValue coordinate systematicAtom supplier failure mass b entries H A
    (CappedCoordinates.coordinateExpands sources k clock p den x oracle bits)
    (by intros; rfl) hfailure hpoint le_rfl hbudget hcalls hvalid hHw hHf hdriver hcount
    hstream hblank hfresh hrecord hlog

end OrderedCallPhases.CappedFold
