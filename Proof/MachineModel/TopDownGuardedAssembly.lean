import Proof.MachineModel.TopDownWorkspaceGuardedWorker

/-! Coherent guarded endpoint cut. All finite-program choices remain data;
the three substantive regions are the actual admission receipt, admitted
Verdict, and Runtime of precisely the chosen gated worker. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.GuardedAssembly
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open WorkspaceGuardedWorker
noncomputable section

structure ProgramData where
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  coldCutoff : Nat
  baseOnset : Nat
  tapes : Nat
  admissionStates : Nat
  bodyStates : Nat
  admission : LocalBitMultitape.Machine tapes admissionStates
  continuation : LocalBitMultitape.Machine tapes bodyStates
  inputTape : Fin tapes
  lengthFlag : Fin tapes
  admissionFlag : Fin tapes
  result : Fin tapes
  preFuel : Nat → Nat
  bodyFuel : Nat → Nat

def workerData (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (D : ProgramData) : WorkerData :=
  data sources p D.k D.clock D.coldCutoff D.baseOnset D.admission D.continuation
    D.inputTape D.lengthFlag D.admissionFlag D.result D.preFuel D.bodyFuel

/-- No data binder is silently considered produced. This record is a
conditional construction target, not a proof of its own inhabitability. -/
structure Obligations (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (D : ProgramData) : Type 1 where
  htapes : 2≤D.tapes
  hinput : D.inputTape.val=0
  hflag : D.lengthFlag≠D.inputTape
  admission_run : ∀ n x bits, (workerData sources p D).onset≤n →
    ∃ H A, Step D.admission (D.preFuel n) (fun _=>0)
      (entry D.lengthFlag (List.ofFn x) bits) H A ∧
      readTapeBit (A D.admissionFlag) (H D.admissionFlag)=
        C10LegalAdmission.passed sources p (reference D.k D.clock) D.coldCutoff n x bits
  admitted : ∀ n x bits, (workerData sources p D).onset≤n →
    (workerData sources p D).passed n x bits=true →
    DecodedVerdictAt sources p (workerData sources p D) htapes n x bits
  runtime : Runtime sources D.k D.clock (workerData sources p D).fuel

def requirements (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (D : ProgramData) (O : Obligations sources p D) :
    Requirements sources p (workerData sources p D) where
  htapes := O.htapes
  hcut := (Nat.le_max_right D.baseOnset _).trans (Nat.le_max_left _ _)
  rejected := WorkspaceGuardedWorker.rejected sources p D.k D.clock D.coldCutoff D.baseOnset
    D.admission D.continuation D.inputTape D.lengthFlag D.admissionFlag D.result
    D.preFuel D.bodyFuel O.htapes O.hinput O.hflag O.admission_run
  admitted := O.admitted
  admits_legal := legal_admission sources p D.k D.clock D.coldCutoff D.baseOnset
    D.admission D.continuation D.inputTape D.lengthFlag D.admissionFlag D.result
    D.preFuel D.bodyFuel

/-- Actual compiled endpoint application. Legal admission and the rejection
composition are supplied; the displayed program choices and obligations are not. -/
theorem close
    (choose : (sources : EightSources) → ∀ gamma : Real, 0<gamma → gamma<1/2 →
      Parameters sources gamma → ProgramData)
    (construct : (sources : EightSources) → ∀ gamma : Real, ∀ hg : 0<gamma,
      ∀ hh : gamma<1/2, (p : Parameters sources gamma) →
      Obligations sources p (choose sources gamma hg hh p)) :
    EightSources → OrdinaryHeadlineTheorem25 := by
  exact theorem25_of_guarded
    (fun sources gamma hg hh p => workerData sources p (choose sources gamma hg hh p))
    (fun sources gamma hg hh p => requirements sources p (choose sources gamma hg hh p)
      (construct sources gamma hg hh p))
    (fun sources gamma hg hh p => (construct sources gamma hg hh p).runtime)

end
end NearCubicWires.P1TopDown.GuardedAssembly
