import Proof.Assembly.ThreePhaseTail
import Proof.Assembly.BranchPhases
import Proof.Assembly.AfterEntry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SelectedPhaseLayout
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary P1TopDown
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open CloseoutRowsOriginalSchedule CloseoutFinalC10Realizes
open ControllerSelectedContinuation
open CappedEntryRun (readyBank)
namespace S
open SelectedBranchPhases
noncomputable section
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

def ports := recordPort (offset sources p k r) (bodyTapes sources p k r scratch)
 (tapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch)
 (body sources p k r scratch)
def flag := resultPort (offset sources p k r) (bodyTapes sources p k r scratch)
 (tapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch)
 (body sources p k r scratch)
def heads := WorkspaceSelectedEntryReady.finalHeads sources p k r (extra sources p k r scratch)
 (CappedEntryRun.space sources p k r scratch)
def bank := readyBank sources p den hden k r (extra sources p k r scratch)
 (CappedEntryRun.space sources p k r scratch) n x bits hp
def mode := readTapeBit (bank sources p den hden k r scratch n x bits hp
 (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
 (heads sources p k r scratch (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))

theorem flag_val : (flag sources p k r scratch).val=
 WorkspaceSelectedAdmission.originalTapes sources p k+2+217 := by
 have hP : 217 < WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
   unfold WorkspaceSelectedEntry.size; omega
 simp only [flag,resultPort,body,ControllerSelectedLayout.selectedBody,ControllerSelectedLayout.body,
   CloseoutFinalC10RetainedPhaseFold.tailSlots,C10TailVerdict.tailFlag,ControllerSelectedLayout.location]
 simp [hP]

structure SelectedPhases
 (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
 {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
 (pcpp : PointwisePCPP circuit)
 (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
 (evaluate : Atom → BitInput arity → Bool) (remainingFuel : Nat) (width : Phase → Nat) : Type 1 where
 cost : Phase → Nat
 runs : ThreePhases sources (offset sources p k r) (bodyTapes sources p k r scratch)
   (tapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch)
   (body sources p k r scratch) pcpp proofValue evaluate
   (phase sources p k r scratch site (mode sources p den hden k r scratch n x bits hp))
   cost width (heads sources p k r scratch) (bank sources p den hden k r scratch n x bits hp)
 fits : branchFuel cost width+2 ≤ remainingFuel

variable {sources p den hden k r scratch n x bits hp}
 {site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states}
 {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
 {pcpp : PointwisePCPP circuit}
 {proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real}
 {evaluate : Atom → BitInput arity → Bool} {remainingFuel : Nat} {width : Phase → Nat}

def SelectedPhases.afterEntry
 (R : SelectedPhases sources p den hden k r scratch n x bits hp site pcpp proofValue evaluate remainingFuel width)
 (ph : Phase) : CappedEntryRun.AfterEntry sources p den hden k r scratch n x bits hp site
 ph (constantsOf sources) pcpp proofValue evaluate remainingFuel (ports sources p k r scratch ph) (width ph) where
 cost := branchFuel R.cost width
 result := (R.runs.finish (body_injective sources p k r scratch)).realizes ph
 fits := R.fits

theorem SelectedPhases.physical
 (R : SelectedPhases sources p den hden k r scratch n x bits hp site pcpp proofValue evaluate remainingFuel width) :
 let RR := fun ph => (R.afterEntry ph).phaseInput.realizes
 readTapeBit ((RR .penalty).exit (flag sources p k r scratch))
   ((RR .penalty).heads (flag sources p k r scratch))=true ↔
 (((RR .penalty).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧
 (((RR .moment).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧
 C10Verdict.bound (constantsOf sources) .clause ≤ (((RR .clause).result.value : Rat) : Real) :=
 (R.runs.finish (body_injective sources p k r scratch)).physical

theorem flag_eq_result (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den remainingDegree r base scratch : Nat)
 (site : Bool → Phase → Σ states, Machine (bodyTapes sources p
   (ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree) r scratch) states)
 (remainingFuel : Nat → Nat) :
 let C := ControllerCappedRuntime.continuation sources p den remainingDegree r base scratch site remainingFuel
 flag sources p C.k r scratch = C.result := by
 intro C
 apply Fin.ext
 exact flag_val sources p C.k r scratch

end
end S
end SelectedPhaseLayout
