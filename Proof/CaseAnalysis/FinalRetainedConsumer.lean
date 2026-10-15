import Proof.CaseAnalysis.FinalRetainedPhaseFold
import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.RowsOriginalClauseLoop

/-!
The retained C10 consumer uses the selected phase fold, actual clause driver,
and source-fixed head-aware tail. Accuracy is required only for monomials in
the actual phase. Entry and clause transitions keep their physical tapes,
heads and budgets explicit. No whole-worker run or Runtime is inferred.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedConsumer
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
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
    (hcalls : List.Forall₂ (NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain.Calls supplier) (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
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
  · rw [folded_value_eq_estimatedMean supplier (CompetitorRationalDecision.width b)
      (phasePolynomial ph pcpp coordinate systematicAtom) entries hcalls hentries,
      estimatedMean_eq_finsetSum]

/-- The original clause driver followed by the same retained fold. The entry
  and repeat transitions are actual source-linked Steps, not CallsReady. -/
def phase_realizes {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
    {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
    (evaluate : Atom → BitInput arity → Bool)
    (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B) (ph : Phase)
    (b : Nat) (entries : List Entry) {se sc : Nat}
    (entry : Machine (B+1) se) (clause : Machine B sc)
    (entryFuel N cost : Nat) (H : Nat → Fin B → Nat) (A : Nat → Fin B → List Bool)
    (hin : Fin (B+1) → Nat) (tin : Fin (B+1) → List Bool)
    (hentry : Step entry entryFuel hin tin
      (Fin.addCases (H 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (A 0) (fun _ : Fin 1 => CompareMachine.word N)))
    (hround : ∀ j<N, Step clause cost (H j) (A j) (H (j+1)) (A (j+1)))
    (R : Realizes ph constants pcpp proofValue evaluate
      (CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph)
      (CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) (H N) (A N)
      (CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)
      (foldWidth (CompetitorRationalDecision.width b) entries)) :
    Realizes ph constants pcpp proofValue evaluate
      (Composition.machine entry (Composition.machine (RepeatMachine.machine clause (fun _ _ => true))
        (RecoveryFocus.machine (Fin.castAdd 1)
          (CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph))))
      (entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length)) hin tin
      ((CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215).castAdd 1)
      (foldWidth (CompetitorRationalDecision.width b) entries) := by
  have hloop := CloseoutRowsOriginalClauseLoop.run clause N cost H A hround
  let slots : Fin B → Fin (B+1) := Fin.castAdd 1
  have inj : Function.Injective slots := by intro i j h; exact Fin.ext (congrArg (fun z : Fin (B+1) => z.val) h)
  let HN : Fin (B+1) → Nat := Fin.addCases (H N) (fun _ : Fin 1 => 1)
  let AN : Fin (B+1) → List Bool := Fin.addCases (A N) (fun _ : Fin 1 => CompareMachine.word N)
  have hfold := R.run.dock slots inj HN AN
    (by intro j; simp [HN,slots]) (by intro j; simp [AN,slots])
  exact C10TailComposeVerdict.transport R _ _ (hentry.seq (hloop.seq hfold))
    ((install_slot slots inj AN R.exit _).trans R.hencoded)

/-- Exactly the tail's required literal public words and private blank cells. -/
theorem parked (widths : Phase → Nat) (estimates : Phase → CompetitorValidity.Estimate)
    (A : Fin 475 → List Bool)
    (hrec : ∀ ph, A (C10TailVerdict.scratchT ph)=recordWord (widths ph) (estimates ph) 1 1)
    (hwidth : ∀ ph j, A (C10TailSlotsUniform.widthSlotT ph j)=C10BodyWidths.widthWord (widths ph) j)
    (hblank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val → A i=[]) :
    C10TailVerdictUniform.ParkedThree' (widths .penalty) (widths .moment) (widths .clause)
      (estimates .penalty) (estimates .moment) (estimates .clause) (fun _ => 0) A := by
  have hb (i : Fin 475) (hi : 221 ≤ i.val) : A i=[] := hblank i (Or.inr hi)
  have phase (ph : Phase) : C10TailFeedDockUniform.PhaseParked ph (widths ph) (estimates ph) (fun _ => 0) A := by
    refine ⟨?_, rfl, fun _ => rfl, ?_, fun _ => rfl, ?_, fun _ => rfl, ?_,
      fun _ => rfl, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
    · rw [C10TailVerdict.feedSlots_scratch]; exact hrec ph
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.cmp_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.normA_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.normB_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.word_ge j))
    · exact (congrArg A (C10TailSlotsUniform.feedSlots_width (C10TailUniformSlots.phaseIndex ph) ph 0)).trans (hwidth ph 0)
    · exact (congrArg A (C10TailSlotsUniform.feedSlots_width (C10TailUniformSlots.phaseIndex ph) ph 1)).trans (hwidth ph 1)
    · intro j
      exact (congrArg A (C10TailSlotsUniform.feedSlots_private (C10TailUniformSlots.phaseIndex ph) ph j)).trans
        (hblank _ (Or.inl (C10TailSlotsUniform.privateSlotT_range ph j)))
  exact ⟨phase .penalty,phase .moment,phase .clause,hb _ (by decide),rfl,hb _ (by decide),rfl⟩

/-- The actual fixed tail at the selected retained layout. It preserves all
  phase records and widths and exports the decision at its actual final head. -/
theorem tail_run (sources : RepairSource.EightSources)
    (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B)
    (widths : Phase → Nat) (estimates : Phase → CompetitorValidity.Estimate)
    (H : Fin B → Nat) (A : Fin B → List Bool)
    (hvalid : ∀ ph, (estimates ph).Valid (widths ph))
    (hthreshold : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ widths ph)
    (hhead : ∀ i,H (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i)=0)
    (hrec : ∀ ph, A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailVerdict.scratchT ph))=
      recordWord (widths ph) (estimates ph) 1 1)
    (hwidth : ∀ ph j, A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailSlotsUniform.widthSlotT ph j))=
      C10BodyWidths.widthWord (widths ph) j)
    (hblank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
      A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i)=[]) :
    let slots := CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
    ∃ H' A', Step (RecoveryFocus.machine slots (C10TailComposeUniform.tailMachine sources))
      (C10TailVerdictUniform.tbud (max (widths .penalty) (max (widths .moment) (widths .clause)))) H A H' A' ∧
      (readTapeBit (A' (slots C10TailVerdict.tailFlag)) (H' (slots C10TailVerdict.tailFlag))=true ↔
        (((estimates .penalty).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧
        (((estimates .moment).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧
        C10Verdict.bound (constantsOf sources) .clause ≤ (((estimates .clause).value : Rat) : Real)) ∧
      (∀ ph, A' (slots (C10TailVerdict.scratchT ph))=A (slots (C10TailVerdict.scratchT ph))) ∧
      (∀ ph j, A' (slots (C10TailSlotsUniform.widthSlotT ph j))=A (slots (C10TailSlotsUniform.widthSlotT ph j))) ∧
      (∀ i, (∀ j, slots j ≠ i) → A' i=A i) := by
  classical
  let slots := CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
  have inj : Function.Injective slots := by
    intro i j he
    have hv := congrArg Fin.val he
    apply Fin.ext
    dsimp only [slots,CloseoutFinalC10RetainedPhaseFold.tailSlots] at hv
    split_ifs at hv <;> omega
  have hp := parked widths estimates (A ∘ slots) hrec hwidth hblank
  have hw := C10TailVerdictUniform.tailWidths'_of (constantsOf sources)
    (hthreshold .penalty) (hthreshold .moment) (hthreshold .clause)
  obtain ⟨TH,TA,hs,htest,hframe,hflag⟩ := C10TailComposeUniform.tail_spec_head sources
    (widths .penalty) (widths .moment) (widths .clause)
    (estimates .penalty) (estimates .moment) (estimates .clause)
    (hvalid .penalty) (hvalid .moment) (hvalid .clause) hw (fun _ => 0) (A ∘ slots) hp
  refine ⟨dockH slots H TH, install slots A TA, hs.dock slots inj H A hhead (by intro i;rfl), ?_, ?_, ?_, ?_⟩
  · rw [dockH_slot slots inj, hflag, install_slot slots inj]
    exact htest.trans (and_congr (C10TailComposeVerdict.bound_penalty (constantsOf sources) _)
      (and_congr (C10TailComposeVerdict.bound_moment (constantsOf sources) _)
        (C10TailComposeVerdict.bound_clause (constantsOf sources) _)))
  · intro ph
    exact (install_slot slots inj A TA _).trans (hframe _ (C10TailSlotsUniform.scratch_public ph))
  · intro ph j
    exact (install_slot slots inj A TA _).trans (hframe _ (C10TailSlotsUniform.width_public ph j))
  · intro i hi
    exact install_other slots A TA i hi

/-- Transport the actual local phase estimates onto one admitted worker run.
  The worker Step, retained records and physical tail test stay explicit. -/
def verdict_of_local_phases {Atom : Type} {arity t sw : Nat}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
    (evaluate : Atom → BitInput arity → Bool)
    {states : Phase → Nat} (program : (ph : Phase) → Machine t (states ph))
    (budget : Phase → Nat) (hin : Phase → Fin t → Nat) (tin : Phase → Fin t → List Bool)
    (localPort : Phase → Fin t) (width : Phase → Nat)
    (R : ∀ ph, Realizes ph constants pcpp proofValue evaluate (program ph) (budget ph)
      (hin ph) (tin ph) (localPort ph) (width ph))
    (worker : Machine t sw) (ht : 2 ≤ t) (fuel : Nat → Nat)
    (n : Nat) (x : BitInput n) (bits : List Bool) (result : Fin t) (ports : Phase → Fin t)
    (gate : C10LengthGate.LengthGate constants worker ht result fuel)
    (hcut : CloseoutWitness.Soundness.cutoff constants ≤ n)
    (heads : Fin t → Nat) (exit : Fin t → List Bool)
    (hrun : Step worker (fuel n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) heads exit)
    (hrecord : ∀ ph, exit (ports ph)=recordWord (width ph) (R ph).result 1 1)
    (htest : readTapeBit (exit result) (heads result)=true ↔
      ((((R .penalty).result.value : Rat) : Real) ≤ C10Verdict.bound constants .penalty ∧
       (((R .moment).result.value : Rat) : Real) ≤ C10Verdict.bound constants .moment ∧
       C10Verdict.bound constants .clause ≤ (((R .clause).result.value : Rat) : Real))) :
    C10Verdict.Verdict constants pcpp proofValue evaluate worker ht fuel n x bits result ports width :=
  C10GuardedStageConsumer.verdict_of_admitted constants pcpp proofValue evaluate worker ht fuel
    n x bits result ports width gate hcut heads exit hrun
    (fun ph => C10TailComposeVerdict.transport (R ph) heads exit hrun (hrecord ph))
    (by simpa only [C10TailComposeVerdict.transport_result] using htest)

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedConsumer
