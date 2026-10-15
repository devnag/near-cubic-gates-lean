import Proof.MachineModel.TopDownWorkspaceSelectedEntryRepeat
import Proof.CaseAnalysis.FinalRetainedConsumer

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1TopDown.ControllerSelectedLayout
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding

def location (t P i : Nat) : Nat :=
  if i=0 then 0 else if i=1 then 1 else if i=216 then t+1
  else if i<P then t+2+i else if i<P+t-2 then i-P+2
  else if i=P+t-2+51 then t+2 else i+4

theorem facts (t P extra : Nat) (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) :
    (∀ i, i < t+2+extra-4 → location t P i < t+2+extra) ∧
    (∀ i j, i < t+2+extra-4 → j < t+2+extra-4 →
      location t P i=location t P j → i=j) ∧
    (∀ i, i < t+2+extra-4 → location t P i ≠ t+2+P+51) ∧
    (∀ i, i<P → location t P i=
      (if i=0 then 0 else if i=1 then 1 else if i=216 then t+1 else t+2+i)) ∧
    (∀ j, j<t → location t P (if j<2 then j else P+j-2)=j) ∧
    (∀ i, P+t-2 ≤ i → i ≠ P+t-2+51 → location t P i=i+4) := by
  unfold location
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    split_ifs <;> omega
  · intro i j hi hj he
    split_ifs at he <;> omega
  · intro i hi he
    split_ifs at he <;> omega
  · intro i hi
    split_ifs <;> omega
  · intro j hj
    split_ifs <;> omega
  · intro i hi hne
    split_ifs <;> omega

def body {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) (i : Fin (t+2+extra-4)) : Fin (t+1+1+extra) :=
  ⟨location t P i.val, by have := (facts t P extra ht hP hspace).1 i.val i.isLt; omega⟩

theorem body_injective {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) : Function.Injective (body ht hP hspace) := by
  intro i j he
  exact Fin.ext ((facts t P extra ht hP hspace).2.1 i.val j.val i.isLt j.isLt
    (congrArg Fin.val he))

theorem body_ne_driver {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P)
    (hspace : P+1155 ≤ extra) (i : Fin (t+2+extra-4)) :
    (body ht hP hspace i).val ≠ t+2+P+51 :=
  (facts t P extra ht hP hspace).2.2.1 i.val i.isLt

noncomputable section
variable (sources : EightSources) {gamma : Real} (par : Parameters sources gamma)
  (k r extra : Nat)

def selectedBody (hspace : WorkspaceSelectedEntry.size sources k r par.clauseDegree+1155 ≤ extra) :=
  body (WorkspaceSelectedEntryReady.old_size sources par k)
    (show 302 ≤ WorkspaceSelectedEntry.size sources k r par.clauseDegree by
      dsimp [WorkspaceSelectedEntry.size]; omega) hspace

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

/-- Supply the two previously unmatched layout premises of the actual
entry-to-loop consumer. The callback Step and its actual intermediate bank
stay explicit; in particular no zero-head or blank-bank reset is inserted. -/
theorem after_ready
    (hspace : WorkspaceSelectedEntry.size sources k r par.clauseDegree+1155 ≤ extra)
    {sc : Nat}
    (clause : Machine (WorkspaceSelectedAdmission.originalTapes sources par k+2+extra-4) sc)
    (N cost entryFuel : Nat)
    (H : Nat → Fin (WorkspaceSelectedAdmission.originalTapes sources par k+2+extra-4) → Nat)
    (A : Nat → Fin (WorkspaceSelectedAdmission.originalTapes sources par k+2+extra-4) → List Bool)
    (tin middle : Fin (WorkspaceSelectedAdmission.originalTapes sources par k+1+1+extra) → List Bool)
    (hentry : Step (WorkspaceSelectedEntryReady.program sources par k r extra (by omega)).2 entryFuel
      (fun _=>0) tin (WorkspaceSelectedEntryReady.finalHeads sources par k r extra (by omega)) middle)
    (hhead : ∀ i, WorkspaceSelectedEntryReady.finalHeads sources par k r extra (by omega)
      (selectedBody sources par k r extra hspace i)=H 0 i)
    (htape : ∀ i, middle (selectedBody sources par k r extra hspace i)=A 0 i)
    (hword : middle (WorkspaceSelectedEntryReady.driver sources par k r extra (by omega))=UnaryTemplate.tape N)
    (hround : ∀ j, j<N → Step clause cost (H j) (A j) (H (j+1)) (A (j+1))) :
    let port := WorkspaceSelectedEntryRepeat.slots (selectedBody sources par k r extra hspace)
      (WorkspaceSelectedEntryReady.driver sources par k r extra (by omega))
    Step (Composition.machine (WorkspaceSelectedEntryReady.program sources par k r extra (by omega)).2
      (RecoveryFocus.machine port (RepeatMachine.machine clause (fun _ _=>true))))
      (entryFuel+1+(N*(cost+3)+3)) (fun _=>0) tin
      (dockH port (WorkspaceSelectedEntryReady.finalHeads sources par k r extra (by omega))
        (Fin.addCases (H N) (fun _ : Fin 1=>1)))
      (install port middle (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N))) := by
  have hi : Function.Injective (selectedBody sources par k r extra hspace) :=
    body_injective _ _ hspace
  have hd : ∀ i, selectedBody sources par k r extra hspace i ≠
      WorkspaceSelectedEntryReady.driver sources par k r extra (by omega) := by
    intro i he
    have hv := congrArg Fin.val he
    exact body_ne_driver _ _ hspace i (by
      simpa only [selectedBody,WorkspaceSelectedEntryReady.driver,Nat.add_assoc] using hv)
  exact WorkspaceSelectedEntryRepeat.after_ready sources par k r extra (by omega) clause
    (selectedBody sources par k r extra hspace) hi hd
    N cost entryFuel H A tin middle hentry hhead htape hword hround

/-- Transport an existing phase realization through the physically docked
source-count Repeat. This is the padded-driver counterpart of
RetainedConsumer.phase_realizes, with ambient tapes preserved throughout. -/
def phase_realizes {Atom : Type} {arity t B se sc sf : Nat}
    {circuit : BooleanCircuit arity} {source : RepairRepresentation.PointwisePCPPAlgorithm}
    {constants : CompetitorRationalGap.Constants source}
    {pcpp : SourceInterfaces.PointwisePCPP circuit}
    {proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real}
    {evaluate : Atom → BitInput arity → Bool} {ph : CloseoutRowsOriginalSchedule.Phase}
    (entry : Machine t se) (clause : Machine B sc) (fold : Machine B sf)
    (port : Fin B) (width entryFuel N cost foldFuel : Nat)
    (body : Fin B → Fin t) (driver : Fin t)
    (hi : Function.Injective body) (hd : ∀ i, body i ≠ driver)
    (H : Nat → Fin B → Nat) (A : Nat → Fin B → List Bool)
    (hin middleH : Fin t → Nat) (tin middle : Fin t → List Bool)
    (hentry : Step entry entryFuel hin tin middleH middle)
    (hhead : ∀ i, middleH (body i)=H 0 i) (htape : ∀ i, middle (body i)=A 0 i)
    (hdriver : middleH driver=1) (hword : middle driver=UnaryTemplate.tape N)
    (hround : ∀ j, j<N → Step clause cost (H j) (A j) (H (j+1)) (A (j+1)))
    (R : CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
      fold foldFuel (H N) (A N) port width) :
    CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
      (Composition.machine entry
        (Composition.machine
          (RecoveryFocus.machine (WorkspaceSelectedEntryRepeat.slots body driver)
            (RepeatMachine.machine clause (fun _ _=>true)))
          (RecoveryFocus.machine body fold)))
      (entryFuel+1+(N*(cost+3)+3+1+foldFuel)) hin tin (body port) width := by
  let slots := WorkspaceSelectedEntryRepeat.slots body driver
  have inj := WorkspaceSelectedEntryRepeat.slots_injective body driver hi hd
  let HN := dockH slots middleH (Fin.addCases (H N) (fun _ : Fin 1=>1))
  let AN := install slots middle (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N))
  have hloop := WorkspaceSelectedEntryRepeat.run_at clause body driver hi hd N cost H A
    middleH middle hhead htape hdriver hword hround
  have hfold := R.run.dock body hi HN AN
    (by
      intro i
      simpa only [slots, WorkspaceSelectedEntryRepeat.slots, Fin.addCases_left] using
        dockH_slot slots inj middleH (Fin.addCases (H N) (fun _ : Fin 1=>1)) (i.castAdd 1))
    (by
      intro i
      simpa only [slots, WorkspaceSelectedEntryRepeat.slots, Fin.addCases_left] using
        install_slot slots inj middle (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N)) (i.castAdd 1))
  exact C10TailComposeVerdict.transport R _ _ (hentry.seq (hloop.seq hfold))
    ((install_slot body hi AN R.exit port).trans R.hencoded)

end
end NearCubicWires.P1TopDown.ControllerSelectedLayout
