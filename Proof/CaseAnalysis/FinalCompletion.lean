import Proof.CaseAnalysis.FinalPipelineOfStage
import Proof.CaseAnalysis.FinalResidualLeaves
import Proof.CaseAnalysis.FinalSupplierFuel
import Proof.CaseAnalysis.FinalLogFitFull

namespace NearCubicWires.RepairSource.CloseoutFinal.C10Completion

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev StageChoice (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma) : Type 1 :=
  Σ' (k : ℕ) (S : StageData sources k p), StageBlock sources k p S

noncomputable def machineOf
    (stage : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      (p : Parameters sources gamma) → StageChoice sources p)
    (sources : EightSources) (gamma : ℝ) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : Machine sources p.degree p.clauseDegree p.copies :=
  C10PipelineOfStage.machine_of_stage sources p (stage sources gamma hg hh p).1
    (stage sources gamma hg hh p).2.1 (stage sources gamma hg hh p).2.2

noncomputable def runtimeOf (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (S : StageData sources k p)
    (emitFuel callCap tailBudget : ℕ → ℕ) (onset A a sigma kappa c : ℕ)
    (ha : a ≤ k + 1)
    (hsigma : 6 + (fixedProjection sources).degrees.proofLog ≤ sigma)
    (hslack : sigma + c + 2 ≤ kappa)
    (hgrow : ∀ N, onset ≤ N → C10LogFitFull.fullOnset kappa ≤
      (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
    (hstage : ∀ ph N, onset ≤ N → S.stageFuel ph N + 2 ≤
      2 ^ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N
            - kappa * (Nat.log 2
              ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N) + 1))
        * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1) ^ c)
    (hrest : ∀ N, onset ≤ N →
      dockedFuel emitFuel (S.entryWidth N) (callCap N) N + tailBudget N ≤ A * (N + 1) ^ a)
    (hbudget : S.budget =
      C10SupplierFuel.budgetOf onset S.stageFuel emitFuel S.entryWidth callCap tailBudget) :
    Runtime sources k (PolynomialClock.ordinaryClock k) S.budget := by
  rw [hbudget]
  exact C10SupplierFuel.runtime_of_supplierFuel sources k (PolynomialClock.ordinaryClock k)
    (fun N => Nat.log 2
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N) + 1)
    S.stageFuel emitFuel S.entryWidth callCap tailBudget onset A a sigma kappa c
    ha hsigma hslack
    (fun N hN => C10LogFitFull.hlog_of_onset kappa _ (hgrow N hN))
    (fun N hN => C10LogFitFull.hfit_full kappa _ (hgrow N hN))
    (fun N hN => C10LogFitFull.hlogTwo_of_onset kappa _ (hgrow N hN))
    hstage hrest

theorem theorem25_of_stageBlock
    (stage : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      (p : Parameters sources gamma) → StageChoice sources p)
    (ledger : (sources : EightSources) → ∀ (gamma : ℝ) (hg : 0 < gamma) (hh : gamma < 1/2)
      (p : Parameters sources gamma),
      Runtime sources (stage sources gamma hg hh p).1
        (PolynomialClock.ordinaryClock (stage sources gamma hg hh p).1)
        (stage sources gamma hg hh p).2.1.budget) :
    Theorem25Target :=
  theorem25_of_leaves (machineOf stage) ledger

end NearCubicWires.RepairSource.CloseoutFinal.C10Completion
