import Proof.CaseAnalysis.FinalLegalAdmission
import Proof.CaseAnalysis.FinalCacheAtAdmission

/-! Checked admission-sensitive upper application. Rejected descriptions need
an actual rejecting run, never phase records or a decoder-fallback identity.
The physical rejected branch remains a separate ordinary-machine obligation.
No worker continuation or overall runtime bound is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceGuardedEntry
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal
open CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open RepairSource.CloseoutFinal.C10GuardedStageConsumer
open RepairSource.CloseoutFinal.C10Fusion
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

/-- The literal Machine consumer with its existing legal-admission requirement
discharged. Both remaining physical branches refer to the same chosen worker. -/
def machine_from_admitted (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (W : WorkerData) (coldCutoff : Nat)
    (ht : 2 ≤ W.tapes)
    (hcut : Soundness.cutoff (constantsOf sources) ≤ W.onset)
    (rejected : ∀ n x bits,
      n < (C10LegalAdmission.admissionData sources p W coldCutoff).onset ∨
        C10LegalAdmission.passed sources p W coldCutoff n x bits = false →
      RejectedAt W.worker ht W.result W.fuel n x bits)
    (admitted : ∀ n x bits,
      (C10LegalAdmission.admissionData sources p W coldCutoff).onset ≤ n →
      C10LegalAdmission.passed sources p W coldCutoff n x bits = true →
      DecodedVerdictAt sources p W ht n x bits) :
    CloseoutFinal.Machine sources p.degree p.clauseDegree p.copies :=
  machine_of_guarded sources p (C10LegalAdmission.admissionData sources p W coldCutoff)
    { htapes := ht
      hcut := hcut.trans (C10LegalAdmission.onset_le sources p W coldCutoff)
      rejected := rejected
      admitted := admitted
      admits_legal := C10LegalAdmission.admits_legal sources p W coldCutoff }

/-- The still-open physical regions, with all guards and output types exposed.
No all-witness record producer occurs here. -/
structure Branches (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (W : WorkerData) (coldCutoff : Nat) : Type 1 where
  htapes : 2 ≤ W.tapes
  hcut : Soundness.cutoff (constantsOf sources) ≤ W.onset
  rejected : ∀ n x bits,
    n < (C10LegalAdmission.admissionData sources p W coldCutoff).onset ∨
      C10LegalAdmission.passed sources p W coldCutoff n x bits = false →
    RejectedAt W.worker htapes W.result W.fuel n x bits
  admitted : ∀ n x bits,
    (C10LegalAdmission.admissionData sources p W coldCutoff).onset ≤ n →
    C10LegalAdmission.passed sources p W coldCutoff n x bits = true →
    DecodedVerdictAt sources p W htapes n x bits

/-- Literal headline application. Worker data and cutoff are chosen first;
the two actual execution branches and Runtime at the same worker are hypotheses of this construction. -/
theorem theorem25_from_admitted
    (chooseWorker : (sources : EightSources) → ∀ gamma : Real, 0 < gamma → gamma < 1/2 →
      (p : Parameters sources gamma) → WorkerData)
    (coldCutoff : (sources : EightSources) → Nat)
    (branches : (sources : EightSources) → ∀ gamma : Real, ∀ hg : 0 < gamma,
      ∀ hh : gamma < 1/2, (p : Parameters sources gamma) →
      Branches sources p (chooseWorker sources gamma hg hh p) (coldCutoff sources))
    (runtime : (sources : EightSources) → ∀ gamma : Real, ∀ hg : 0 < gamma,
      ∀ hh : gamma < 1/2, (p : Parameters sources gamma) →
      Runtime sources (chooseWorker sources gamma hg hh p).k
        (chooseWorker sources gamma hg hh p).clock (chooseWorker sources gamma hg hh p).fuel) :
    Theorem25Target :=
  theorem25_of_leaves
    (fun sources gamma hg hh p =>
      machine_from_admitted sources p (chooseWorker sources gamma hg hh p) (coldCutoff sources)
        (branches sources gamma hg hh p).htapes (branches sources gamma hg hh p).hcut
        (branches sources gamma hg hh p).rejected (branches sources gamma hg hh p).admitted)
    runtime

/-- The selected physical flag gives the actual raw-word bound. -/
theorem admitted_length (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (W : WorkerData) (coldCutoff n : Nat)
    (x : BitInput n) (bits : List Bool)
    (h : C10LegalAdmission.passed sources p W coldCutoff n x bits = true) :
    16*bits.length ≤ n := by
  classical
  unfold C10LegalAdmission.passed BoundedFamily.passed at h
  simp only [Bool.and_eq_true] at h
  have hv := of_decide_eq_true h.1
  simpa only [List.length_ofFn] using hv.1

end
end NearCubicWires.P1TopDown.WorkspaceGuardedEntry
