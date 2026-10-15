import Proof.Assembly.OrderedCallsPhaseInput
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option quotPrecheck false
namespace OrderedCallPhases.SelectedConstruction
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary P1TopDown
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open CloseoutRowsOriginalSchedule CloseoutRowsEstimatorCoefficients.Stream
open SelectedPhaseLayout (branchFuel)
open SelectedPhaseLayout.S (ports heads bank mode)
open SelectedBranchPhases (offset tapes offset_ge fresh_lt body)
open ControllerSelectedContinuation (bodyTapes)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat)
local notation "H0" => heads sources p k r scratch
local notation "A0" => bank sources p den hden k r scratch n x bits hp
local notation "M0" => mode sources p den hden k r scratch n x bits hp
local notation "clk" => PolynomialClock.ordinaryClock k
local notation "oracle" => C10TotalDecode.oracleOf sources k clk p.degree n bits
local notation "PI" => PhaseConstruction.Input sources p k den r scratch clk n x oracle bits site M0

/-- The same selected three-phase consumer, now exposing the physical site,
record, and entry premises consumed by the checked phase construction. -/
structure Inputs : Type 1 where
 cost : Phase → Nat
 penalty : PI .penalty H0 A0 (cost .penalty) (width .penalty)
 moment : PI .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment)
 clause : PI .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause)
 penalty_kept : clause.realize.exit (ports sources p k r scratch .penalty)=
   recordWord (width .penalty) penalty.realize.result 1 1
 moment_kept : clause.realize.exit (ports sources p k r scratch .moment)=
   recordWord (width .moment) moment.realize.result 1 1
 threshold : ∀ ph,C10ThresholdWidths.thresholdWidth (constantsOf sources)≤width ph
 head : ∀ i,clause.realize.heads (body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (offset sources p k r)
    (bodyTapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch) i))=0
 words : ∀ ph j,clause.realize.exit (body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (offset sources p k r)
    (bodyTapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch)
    (C10TailSlotsUniform.widthSlotT ph j)))=C10BodyWidths.widthWord (width ph) j
 blank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
   clause.realize.exit (body sources p k r scratch
    (CloseoutFinalC10RetainedPhaseFold.tailSlots (offset sources p k r)
     (bodyTapes sources p k r scratch) (offset_ge sources p k r) (fresh_lt sources p k r scratch) i))=[]
 fits : branchFuel cost width+2≤remainingFuel

variable {sources p den hden k r scratch n x bits hp site remainingFuel width}
@[irreducible] noncomputable def Inputs.selected
 (I : Inputs sources p den hden k r scratch n x bits hp site remainingFuel width) :
 SelectedPhaseLayout.S.SelectedPhases sources p den hden k r scratch n x bits hp site
   (pcppAt sources k clk x oracle)
   (P1Independent.CappedDecode.proofValueOf sources k clk p den x oracle bits)
   (C10TotalDecode.evaluate (pcpp := pcppAt sources k clk x oracle)) remainingFuel width where
 cost := I.cost
 runs := {
   penalty := I.penalty.realize
   moment := I.moment.realize
   clause := I.clause.realize
   penalty_kept := I.penalty_kept
   moment_kept := I.moment_kept
   threshold := I.threshold
   head := I.head
   words := I.words
   blank := I.blank }
 fits := I.fits

end
end OrderedCallPhases.SelectedConstruction
