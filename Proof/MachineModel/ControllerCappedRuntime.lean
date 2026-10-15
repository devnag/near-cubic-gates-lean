import Proof.MachineModel.ControllerCappedSelected
import Proof.MachineModel.TopDownSelectedRuntime
import Proof.MachineModel.ControllerSelectedContinuation

/-! Preserve the C.10 choice order and complete runtime obligation at the
capped physical parser. Reuse the existing additive ledger and same three-phase
continuation syntax. This supplies no estimate for the still-unbuilt supplier. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerCappedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open ControllerCappedSelected
noncomputable section

theorem degree_before_hierarchy (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (den : Nat) :
    ∃ degree,∀ (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))),
      ∃ coefficient,∀ n,preFuel sources p den k clock n≤coefficient*(n+1)^degree := by
  obtain ⟨degree,hdegree⟩:=AdmissionBudget.degree_before_hierarchy
    (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (WorkspaceSelectedAdmission.coldCutoff sources) p.clauseDegree p.degree p.copies
    (WorkspaceSelectedAdmission.capacity sources p).E (WorkspaceSelectedAdmission.capacity sources p).K
    den den (CompetitorRationalGap.zeta (constantsOf sources)) p.hD
  exact ⟨degree,fun k clock=>hdegree (CloseoutWitness.SelectedSource.hierarchy sources k clock) (padding sources k clock)⟩

def prepDegree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) : Nat :=
  Classical.choose (degree_before_hierarchy sources p den)

theorem actual_preprocessing {sources : EightSources} {gamma : Real}
    {p : Parameters sources gamma} (den : Nat) (hden : 0<den)
    (C : SelectedAssembly.ContinuationData sources p) :
    ∃ coefficient,∀ n,(workerData sources p den hden (programData den C)).fuel n≤
      coefficient*(n+1)^prepDegree sources p den+C.fuel n := by
  obtain ⟨A,hA⟩:=Classical.choose_spec (degree_before_hierarchy sources p den) C.k C.clock
  let W:=workerData sources p den hden (programData den C)
  exact ⟨A+4*W.onset+5,fun n=>AdmissionBudget.guarded_fuel _ A W.onset n
    (preFuel sources p den C.k C.clock) C.fuel (hA n)⟩

/-- The caller owes the WHOLE continuation fuel, including input production,
all three phases and their physical decision. A bounded row is insufficient. -/
def of_body_bound {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (den : Nat) (hden : 0<den) (C : SelectedAssembly.ContinuationData sources p)
    (bodyDegree coefficient onset tableCoefficient tableDegree : Nat)
    (hk : max (prepDegree sources p den) bodyDegree≤C.k+1)
    (hbody : ∀ n,onset≤n → C.fuel n+2≤coefficient*(n+1)^bodyDegree+
      tableCoefficient*(2^(SelectedRuntime.width C n-
        (SelectedRuntime.sigma sources+tableDegree+2)*SelectedRuntime.logarithm C n)*
        (SelectedRuntime.width C n+1)^tableDegree)) :
    Runtime sources C.k C.clock (workerData sources p den hden (programData den C)).fuel := by
  let pre:=actual_preprocessing den hden C
  let A:=Classical.choose pre
  have hA:=Classical.choose_spec pre
  let sigma:=SelectedRuntime.sigma sources
  let q:=SelectedRuntime.width C
  let log:=SelectedRuntime.logarithm C
  let threshold:=max (C10LogFitFull.fullOnset sigma)
    (max (C10LogFitFull.fullOnset (sigma+tableDegree+2)) tableCoefficient)
  let cut:=max onset (2^threshold)
  have hwidth : ∀ n,cut≤n → threshold≤q n := by
    intro n hn
    exact C10LedgerAssembly.nativeWidth_ge sources C.k C.clock threshold n
      ((Nat.le_max_right _ _).trans hn)
  refine runtime_of_ledger sources C.k C.clock _ (A+coefficient)
    (max (prepDegree sources p den) bodyDegree) sigma sigma cut log
    hk le_rfl le_rfl ?_ ?_ ?_
  · intro n hn
    have hp:=hA n
    change (workerData sources p den hden (programData den C)).fuel n≤
      A*(n+1)^prepDegree sources p den+C.fuel n at hp
    have hb:=hbody n ((Nat.le_max_left _ _).trans hn)
    have ha:=SelectedRuntime.column_absorb (q n) tableCoefficient tableDegree sigma ((Nat.le_max_right _ _).trans (hwidth n hn))
    have hpre:=Nat.mul_le_mul_left A
      (Nat.pow_le_pow_right (by omega : 1≤n+1) (Nat.le_max_left (prepDegree sources p den) bodyDegree))
    have hpost:=Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_right (by omega : 1≤n+1) (Nat.le_max_right (prepDegree sources p den) bodyDegree))
    change (workerData sources p den hden (programData den C)).fuel n+2≤
      (A+coefficient)*(n+1)^max (prepDegree sources p den) bodyDegree+
        hotOf sigma q log n
    have ht : C.fuel n+2≤coefficient*(n+1)^bodyDegree+hotOf sigma q log n :=
      hb.trans (Nat.add_le_add_left ha _)
    calc _ ≤ A*(n+1)^prepDegree sources p den+
          (coefficient*(n+1)^bodyDegree+hotOf sigma q log n) := by omega
      _ ≤ (A+coefficient)*(n+1)^max (prepDegree sources p den) bodyDegree+
          hotOf sigma q log n := by nlinarith
  · exact fun n hn=>(Nat.le_succ _).trans
      (C10LogFitFull.hlog_of_onset _ _ ((Nat.le_max_left _ _).trans (hwidth n hn)))
  · exact fun n hn=>C10LogFitFull.hfit_full _ _ ((Nat.le_max_left _ _).trans (hwidth n hn))

/-- Supply Runtime to the exact capped endpoint, leaving only the actual
admitted Verdict as the other proof field. -/
def remaining {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (den : Nat) (hden : 0<den) (C : SelectedAssembly.ContinuationData sources p)
    (bodyDegree coefficient onset tableCoefficient tableDegree : Nat)
    (hk : max (prepDegree sources p den) bodyDegree≤C.k+1)
    (hbody : ∀ n,onset≤n → C.fuel n+2≤coefficient*(n+1)^bodyDegree+
      tableCoefficient*(2^(SelectedRuntime.width C n-
        (SelectedRuntime.sigma sources+tableDegree+2)*SelectedRuntime.logarithm C n)*
        (SelectedRuntime.width C n+1)^tableDegree))
    (hadmitted : ∀ n x bits,(workerData sources p den hden (programData den C)).onset≤n →
      (workerData sources p den hden (programData den C)).passed n x bits=true →
      P1Independent.CappedConsumer.DecodedVerdictAt sources p
        (workerData sources p den hden (programData den C))
        (by change 2≤WorkspaceSelectedAdmission.originalTapes sources p C.k+1+1+C.extra; omega) n x bits) :
    Remaining p den hden C :=
  ⟨hadmitted,of_body_bound den hden C bodyDegree coefficient onset tableCoefficient tableDegree hk hbody⟩

/-- Choose both admission and remaining source-length degrees before k. The
previously accepted complete continuation program is reused without alteration. -/
def hierarchyIndex (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree : Nat) :=
  max (prepDegree sources p den) (WorkspaceSelectedEntryRuntime.degree sources p remainingDegree)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

def continuation (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r base scratch : Nat)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      LocalBitMultitape.Machine (ControllerSelectedContinuation.bodyTapes sources p
        (hierarchyIndex sources p den remainingDegree) r scratch) states)
    (remainingFuel : Nat→Nat) : SelectedAssembly.ContinuationData sources p := by
  let k:=hierarchyIndex sources p den remainingDegree
  let X:=ControllerSelectedContinuation.extra sources p k r scratch
  let built:=ControllerSelectedContinuation.program sources p k r scratch site
  exact {
    k := k
    clock := PolynomialClock.ordinaryClock k
    base := base
    extra := X
    states := _
    machine := built.2
    result:=⟨WorkspaceSelectedAdmission.originalTapes sources p k+2+217,by
      have hP : 302≤WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
        unfold WorkspaceSelectedEntry.size; omega
      dsimp [X,ControllerSelectedContinuation.extra]; omega⟩
    fuel:=WorkspaceSelectedEntryRuntime.fuel sources p k r remainingFuel }

end
end NearCubicWires.P1TopDown.ControllerCappedRuntime
