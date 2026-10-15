import Proof.MachineModel.TopDownWorkspaceSelectedEntryBudget
import Proof.MachineModel.ControllerCappedRuntime
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace CappedEntryRun
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure
open RepairSource.SelectedRecoveryIntegration
open WorkspaceSelectedEntryBudget
noncomputable section
theorem admitted_width (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (k n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits=true) :
    SelectedOracle.width (fixedProjection sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)≤n := by
  have passed:=(BoundedFamily.passed_exact (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) (WorkspaceSelectedAdmission.coldCutoff sources)
    p.clauseDegree p.degree p.copies den den (CompetitorRationalGap.zeta (constantsOf sources))
    (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x bits (Nat.le_max_right _ _)).mp hp
  have live:=ColdFamilyGuards.live (fixedProjection sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) (WorkspaceSelectedAdmission.coldCutoff sources)
    p.degree (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)
    (BoundedFields.oracle bits) passed.2.2.1
  simpa only [List.length_ofFn] using live.2.1

/-- This is the literal fuel of EntryReady.run at its actual request. -/
theorem actual_fuel_le (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (k r n : Nat) (x : BitInput n) (bits : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width (fixedProjection sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)))
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits=true)
    (ho : oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound p.degree
      (SelectedOracle.width (fixedProjection sources) k
        (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
        (padding sources k (PolynomialClock.ordinaryClock k))
        (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x))) :
    let rq:=ColdNative.request (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x (Nat.le_max_right _ _) oracle
    C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n+
      WorkspaceSelectedEntryCount.budget (CloseoutLanguage.selectedPCPP sources) rq
        (C10PartsSchedule.entryWidthSchedule sources k r n)+5≤envelope sources p k r n := by
  intro rq
  have h:=actual_count_bound (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) p.degree
    (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x (Nat.le_max_right _ _) oracle
    (admitted_width sources p den hden k n x bits hp) ho
  unfold WorkspaceSelectedEntryCount.budget envelope
  dsimp only [rq] at *
  omega

end
end CappedEntryRun
