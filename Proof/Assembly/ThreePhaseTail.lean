import Proof.CaseAnalysis.FinalRetainedConsumer

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SelectedPhaseLayout
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalSchedule CloseoutFinalC10Realizes
open CloseoutRowsEstimatorCoefficients.Stream
noncomputable section

variable (sources : EightSources) (L B t : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B)
 (body : Fin B → Fin t)

def recordPort (ph : Phase) : Fin t :=
 body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailVerdict.scratchT ph))
def resultPort : Fin t :=
 body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh C10TailVerdict.tailFlag)
def tail := RecoveryFocus.machine body
 (RecoveryFocus.machine (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh)
  (C10TailComposeUniform.tailMachine sources))

def branchProgram (phase : Phase → Σ states, Machine t states) :=
 Composition.machine (phase .penalty).2
  (Composition.machine (phase .moment).2
   (Composition.machine (phase .clause).2 (tail sources L B t hL hFresh body)))

def branchFuel (fuel : Phase → Nat) (width : Phase → Nat) :=
 fuel .penalty+1+(fuel .moment+1+(fuel .clause+1+
 C10TailVerdictUniform.tbud (max (width .penalty) (max (width .moment) (width .clause)))))

/-- Three consecutive actual executions. Earlier records are retained on the
same bank, and the existing tail requires only its literal public words and
private blank cells. No whole-branch or tail Step is a premise. -/
structure ThreePhases {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
 (pcpp : PointwisePCPP circuit)
 (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
 (evaluate : Atom → BitInput arity → Bool)
 (phase : Phase → Σ states, Machine t states)
 (fuel width : Phase → Nat) (H : Fin t → Nat) (A : Fin t → List Bool) : Type 1 where
 penalty : Realizes .penalty (constantsOf sources) pcpp proofValue evaluate
   (phase .penalty).2 (fuel .penalty) H A (recordPort L B t hL hFresh body .penalty) (width .penalty)
 moment : Realizes .moment (constantsOf sources) pcpp proofValue evaluate
   (phase .moment).2 (fuel .moment) penalty.heads penalty.exit
   (recordPort L B t hL hFresh body .moment) (width .moment)
 clause : Realizes .clause (constantsOf sources) pcpp proofValue evaluate
   (phase .clause).2 (fuel .clause) moment.heads moment.exit
   (recordPort L B t hL hFresh body .clause) (width .clause)
 penalty_kept : clause.exit (recordPort L B t hL hFresh body .penalty)=
   recordWord (width .penalty) penalty.result 1 1
 moment_kept : clause.exit (recordPort L B t hL hFresh body .moment)=
   recordWord (width .moment) moment.result 1 1
 threshold : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ width ph
 head : ∀ i, clause.heads (body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i))=0
 words : ∀ ph j, clause.exit (body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
   (C10TailSlotsUniform.widthSlotT ph j)))=C10BodyWidths.widthWord (width ph) j
 blank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
   clause.exit (body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i))=[]

variable {sources L B t hL hFresh body}
variable {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
 {pcpp : PointwisePCPP circuit}
 {proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real}
 {evaluate : Atom → BitInput arity → Bool}
 {phase : Phase → Σ states, Machine t states} {fuel width : Phase → Nat}
 {H : Fin t → Nat} {A : Fin t → List Bool}

abbrev ThreePhases.estimate (R : ThreePhases sources L B t hL hFresh body pcpp proofValue evaluate phase fuel width H A)
 (ph : Phase) : CompetitorValidity.Estimate := match ph with
 | .penalty => R.penalty.result | .moment => R.moment.result | .clause => R.clause.result

theorem ThreePhases.run (hi : Function.Injective body)
 (R : ThreePhases sources L B t hL hFresh body pcpp proofValue evaluate phase fuel width H A) :
 ∃ HF AF, Step (branchProgram sources L B t hL hFresh body phase) (branchFuel fuel width) H A HF AF ∧
 (∀ ph, AF (recordPort L B t hL hFresh body ph)=recordWord (width ph) (R.estimate ph) 1 1) ∧
 (readTapeBit (AF (resultPort L B t hL hFresh body)) (HF (resultPort L B t hL hFresh body))=true ↔
    (((R.estimate .penalty).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧
    (((R.estimate .moment).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧
    C10Verdict.bound (constantsOf sources) .clause ≤ (((R.estimate .clause).value : Rat) : Real)) := by
 have hv : ∀ ph, (R.estimate ph).Valid (width ph) := by
   intro ph; cases ph
   · exact R.penalty.hvalid
   · exact R.moment.hvalid
   · exact R.clause.hvalid
 have hr : ∀ ph, (R.clause.exit ∘ body) (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
     (C10TailVerdict.scratchT ph))=recordWord (width ph) (R.estimate ph) 1 1 := by
   intro ph; cases ph
   · exact R.penalty_kept
   · exact R.moment_kept
   · exact R.clause.hencoded
 obtain ⟨TH,TA,hs,htest,hrecords,_hwidth,_hframe⟩ :=
   CloseoutFinalC10RetainedConsumer.tail_run sources L B hL hFresh width R.estimate
     (R.clause.heads ∘ body) (R.clause.exit ∘ body) hv R.threshold R.head hr R.words R.blank
 have hd := hs.dock body hi R.clause.heads R.clause.exit (fun _ => rfl) (fun _ => rfl)
 refine ⟨_,_, R.penalty.run.seq (R.moment.run.seq (R.clause.run.seq hd)), ?_, ?_⟩
 · intro ph
   exact (install_slot body hi _ TA _).trans ((hrecords ph).trans (hr ph))
 · simpa only [resultPort, install_slot body hi, dockH_slot body hi] using htest

/-- One physical run shared by all three semantic realizations and the test. -/
structure BranchWitness {Atom : Type} {arity t states : Nat}
 {circuit : BooleanCircuit arity} (sources : EightSources) (pcpp : PointwisePCPP circuit)
 (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
 (evaluate : Atom → BitInput arity → Bool) (machine : Machine t states) (cost : Nat)
 (H : Fin t → Nat) (A : Fin t → List Bool) (ports : Phase → Fin t) (width : Phase → Nat)
 (result : Fin t) : Type 1 where
 realizes : ∀ ph, Realizes ph (constantsOf sources) pcpp proofValue evaluate machine cost H A (ports ph) (width ph)
 physical : readTapeBit ((realizes .penalty).exit result) ((realizes .penalty).heads result)=true ↔
   ((((realizes .penalty).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧
    (((realizes .moment).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧
    C10Verdict.bound (constantsOf sources) .clause ≤ (((realizes .clause).result.value : Rat) : Real))

@[irreducible] def ThreePhases.finish (hi : Function.Injective body)
 (R : ThreePhases sources L B t hL hFresh body pcpp proofValue evaluate phase fuel width H A) :
 BranchWitness sources pcpp proofValue evaluate
   (branchProgram sources L B t hL hFresh body phase) (branchFuel fuel width) H A
   (recordPort L B t hL hFresh body) width (resultPort L B t hL hFresh body) := by
 let receipt := R.run hi
 let HF := receipt.choose
 let AF := receipt.choose_spec.choose
 have run := receipt.choose_spec.choose_spec.1
 have records := receipt.choose_spec.choose_spec.2.1
 have physical := receipt.choose_spec.choose_spec.2.2
 let RR : ∀ ph, Realizes ph (constantsOf sources) pcpp proofValue evaluate
     (branchProgram sources L B t hL hFresh body phase) (branchFuel fuel width) H A
     (recordPort L B t hL hFresh body ph) (width ph) := fun ph => match ph with
   | .penalty => C10TailComposeVerdict.transport R.penalty HF AF run (records .penalty)
   | .moment => C10TailComposeVerdict.transport R.moment HF AF run (records .moment)
   | .clause => C10TailComposeVerdict.transport R.clause HF AF run (records .clause)
 exact ⟨RR,physical⟩

end
end SelectedPhaseLayout
