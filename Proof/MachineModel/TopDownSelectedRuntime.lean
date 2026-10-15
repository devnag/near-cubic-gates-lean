import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.TopDownWorkspaceSelectedBudget
import Proof.CaseAnalysis.FinalLedgerAssembly

/-! Runtime of the actual selected guarded worker. Paper A.8:2249–2307
and C.10:4280–4330 keep polynomial-in-N admission separate from the single
residual table factor. The continuation's own fuel bound remains explicit.
Its polynomial degree must be fixed before choosing the hierarchy index. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
noncomputable section

def prepDegree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : Nat :=
  Classical.choose (WorkspaceSelectedBudget.guarded_degree_before_hierarchy sources p)

/-- `bodyDegree` is a supplier choice made before `k`, not a function of `k`. -/
def hierarchyIndex (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (bodyDegree : Nat) : Nat := max (prepDegree sources p) bodyDegree

theorem degrees_fit (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (bodyDegree : Nat) :
    max (prepDegree sources p) bodyDegree ≤ hierarchyIndex sources p bodyDegree+1 :=
  Nat.le_succ _

def sigma (sources : EightSources) : Nat := 6+(fixedProjection sources).degrees.proofLog

def width {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat :=
  (outer sources C.k C.clock).result.pcp.nativeWidth n

def logarithm {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat := Nat.log 2 (width C n)+1

/-- The polynomial coefficient may depend on the fixed hierarchy/clock and
finite gate onset; its degree is the earlier `prepDegree`. -/
theorem actual_preprocessing {sources : EightSources} {gamma : Real}
    {p : Parameters sources gamma} (C : SelectedAssembly.ContinuationData sources p) :
    ∃ coefficient,∀ n,
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel n ≤
        coefficient*(n+1)^prepDegree sources p+C.fuel n :=
  Classical.choose_spec (WorkspaceSelectedBudget.guarded_degree_before_hierarchy sources p)
    C.k C.clock C.base C.extra C.machine C.result C.fuel

/-- Highest existing Runtime producer applied at the literal selected worker.
The only execution bound supplied by the caller concerns `C.fuel` itself. -/
def of_body_bound {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (bodyDegree coefficient onset : Nat)
    (hk : max (prepDegree sources p) bodyDegree ≤ C.k+1)
    (hbody : ∀ n,onset≤n → C.fuel n+2 ≤ coefficient*(n+1)^bodyDegree+
      hotOf (sigma sources) (width C) (logarithm C) n) :
    Runtime sources C.k C.clock
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel := by
  let pre := actual_preprocessing C
  let A := Classical.choose pre
  have hA := Classical.choose_spec pre
  let cut := max onset (2^C10LogFitFull.fullOnset (sigma sources))
  have hwidth : ∀ n,cut≤n → C10LogFitFull.fullOnset (sigma sources)≤width C n := by
    intro n hn
    exact C10LedgerAssembly.nativeWidth_ge sources C.k C.clock _ n
      ((Nat.le_max_right _ _).trans hn)
  refine runtime_of_ledger sources C.k C.clock _ (A+coefficient)
    (max (prepDegree sources p) bodyDegree) (sigma sources) (sigma sources) cut
    (logarithm C) hk le_rfl le_rfl ?_ ?_ ?_
  · intro n hn
    have hpre := hA n
    change (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel n ≤
      A*(n+1)^prepDegree sources p+C.fuel n at hpre
    have hb := hbody n ((Nat.le_max_left _ _).trans hn)
    have hp := Nat.mul_le_mul_left A
      (Nat.pow_le_pow_right (by omega : 1≤n+1) (Nat.le_max_left (prepDegree sources p) bodyDegree))
    have hq := Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_right (by omega : 1≤n+1) (Nat.le_max_right (prepDegree sources p) bodyDegree))
    calc _ ≤ A*(n+1)^prepDegree sources p+(coefficient*(n+1)^bodyDegree+
          hotOf (sigma sources) (width C) (logarithm C) n) := by omega
      _ ≤ (A+coefficient)*(n+1)^max (prepDegree sources p) bodyDegree+
          hotOf (sigma sources) (width C) (logarithm C) n := by nlinarith
  · intro n hn
    exact (Nat.le_succ _).trans (C10LogFitFull.hlog_of_onset _ _ (hwidth n hn))
  · intro n hn
    exact C10LogFitFull.hfit_full _ _ (hwidth n hn)

/-- A fixed column coefficient enlarges only the finite onset. It does not
feed back into kappa; the supplier's q-exponent must be fixed before kappa. -/
theorem column_absorb (q tableCoefficient tableDegree sigma : Nat)
    (hq : max (C10LogFitFull.fullOnset (sigma+tableDegree+2)) tableCoefficient ≤ q) :
    tableCoefficient*(2^(q-(sigma+tableDegree+2)*(Nat.log 2 q+1))*
      (q+1)^tableDegree) ≤ 2^(q-sigma*(Nat.log 2 q+1)) := by
  have hw := (Nat.le_max_left _ _).trans hq
  have hc : tableCoefficient ≤ 2^(2*(Nat.log 2 q+1)) := by
    calc tableCoefficient ≤ q := (Nat.le_max_right _ _).trans hq
      _ ≤ 2^(Nat.log 2 q+1) := (Nat.le_succ _).trans (C10LogFitFull.hlog_of_onset _ _ hw)
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  exact C10SupplierFuel.hot_absorb
    (C10LogFitFull.hlog_of_onset _ _ hw) (C10LogFitFull.hfit_full _ _ hw) le_rfl hc

/-- Paper-shaped alternative: every row, printer-preprocessing, multiplicity,
and loop/clear/append cost must already occur in the actual body bound below.
In particular the `2^{o(q)}` printer cost is not called polynomial in N or q. -/
def of_paper_body_bound {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p)
    (bodyDegree coefficient onset tableCoefficient tableDegree : Nat)
    (hk : max (prepDegree sources p) bodyDegree≤C.k+1)
    (hbody : ∀ n,onset≤n → C.fuel n+2 ≤ coefficient*(n+1)^bodyDegree+
      tableCoefficient*(2^(width C n-(sigma sources+tableDegree+2)*logarithm C n)*
        (width C n+1)^tableDegree)) :
    Runtime sources C.k C.clock
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel := by
  apply of_body_bound C bodyDegree coefficient
    (max onset (2^max (C10LogFitFull.fullOnset (sigma sources+tableDegree+2)) tableCoefficient)) hk
  intro n hn
  have hb := hbody n ((Nat.le_max_left _ _).trans hn)
  have hw := C10LedgerAssembly.nativeWidth_ge sources C.k C.clock
    (max (C10LogFitFull.fullOnset (sigma sources+tableDegree+2)) tableCoefficient) n
    ((Nat.le_max_right _ _).trans hn)
  exact hb.trans (Nat.add_le_add_left
    (column_absorb (width C n) tableCoefficient tableDegree (sigma sources) hw) _)

/-- Actual hierarchy and clock selection after the two polynomial-N degrees.
The machine, result port and fuel remain the same explicit supplier choices. -/
def continuation (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (bodyDegree base extra : Nat) {states : Nat}
    (machine : LocalBitMultitape.Machine
      (WorkspaceSelectedAdmission.originalTapes sources p (hierarchyIndex sources p bodyDegree)+1+1+extra) states)
    (result : Fin (WorkspaceSelectedAdmission.originalTapes sources p
      (hierarchyIndex sources p bodyDegree)+1+1+extra)) (fuel : Nat → Nat) :
    SelectedAssembly.ContinuationData sources p where
  k := hierarchyIndex sources p bodyDegree
  clock := PolynomialClock.ordinaryClock (hierarchyIndex sources p bodyDegree)
  base := base
  extra := extra
  states := states
  machine := machine
  result := result
  fuel := fuel

def selected_runtime (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (bodyDegree base extra : Nat) {states : Nat}
    (machine : LocalBitMultitape.Machine
      (WorkspaceSelectedAdmission.originalTapes sources p (hierarchyIndex sources p bodyDegree)+1+1+extra) states)
    (result : Fin (WorkspaceSelectedAdmission.originalTapes sources p
      (hierarchyIndex sources p bodyDegree)+1+1+extra)) (fuel : Nat → Nat)
    (coefficient onset tableCoefficient tableDegree : Nat)
    (hbody : let C := continuation sources p bodyDegree base extra machine result fuel
      ∀ n,onset≤n → fuel n+2 ≤ coefficient*(n+1)^bodyDegree+
        tableCoefficient*(2^(width C n-(sigma sources+tableDegree+2)*logarithm C n)*
          (width C n+1)^tableDegree)) :
    let C := continuation sources p bodyDegree base extra machine result fuel
    Runtime sources C.k C.clock
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel :=
  of_paper_body_bound (continuation sources p bodyDegree base extra machine result fuel)
    bodyDegree coefficient onset tableCoefficient tableDegree (degrees_fit sources p bodyDegree) hbody

/-- Exact consumer application: admitted Verdict remains the other field;
there is no Runtime hypothesis in the construction inputs. -/
def remaining {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p)
    (admitted : ∀ n x bits,(GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).onset≤n →
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).passed n x bits=true →
      C10GuardedMachineConsumer.DecodedVerdictAt sources p
        (GuardedAssembly.workerData sources p (SelectedAssembly.programData C))
        (by change 2≤WorkspaceSelectedAdmission.originalTapes sources p C.k+1+1+C.extra; omega) n x bits)
    (bodyDegree coefficient onset tableCoefficient tableDegree : Nat)
    (hk : max (prepDegree sources p) bodyDegree≤C.k+1)
    (hbody : ∀ n,onset≤n → C.fuel n+2 ≤ coefficient*(n+1)^bodyDegree+
      tableCoefficient*(2^(width C n-(sigma sources+tableDegree+2)*logarithm C n)*
        (width C n+1)^tableDegree)) : SelectedAssembly.Remaining p C where
  admitted := admitted
  runtime := of_paper_body_bound C bodyDegree coefficient onset tableCoefficient tableDegree hk hbody

end
end NearCubicWires.P1TopDown.SelectedRuntime
