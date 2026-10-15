import Proof.CaseAnalysis.FinalCompletion
import Proof.CaseAnalysis.FinalStageSeamBridge
import Proof.CaseAnalysis.FinalSupplierCall
import Proof.CaseAnalysis.WitnessInputCutoff

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The width-growth link, in the direction the ledger needs -/

/-- **The native width dominates every fixed threshold, eventually.**  The
selected source's native width at length `N` is `Nat.log 2` of the projection
envelope of `N`, and the envelope dominates `N + 1`
(`input_le_envelope`, `Proof/CaseAnalysis/NativeWidthStep.lean`); so once
`2 ^ T <= N`, the width is at least `T`.  This is
`input_cutoff_native` (`Proof/CaseAnalysis/WitnessInputCutoff.lean`) with its
fixed `minimumArity` replaced by a free `T` -- the same proof, nothing new. -/
theorem nativeWidth_ge (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (T N : ℕ) (hN : 2 ^ T ≤ N) :
    T ≤ (outer sources k clock).result.pcp.nativeWidth N := by
  let H := (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
  have hp : 2 ^ T ≤ ProjectionNormalization.Dimensions.envelope (fixedProjection sources)
      (HierarchyEncode.length H (padding sources k clock) N) :=
    hN.trans ((Nat.le_succ N).trans
      (CloseoutNativeWidth.input_le_envelope (fixedProjection sources) H
        (padding sources k clock) N))
  exact (Nat.le_log_of_pow_le (by decide : 1 < 2) hp).trans (Nat.le_succ _)

theorem hgrow_of_dyadic (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (kappa onset : ℕ)
    (honset : 2 ^ C10LogFitFull.fullOnset kappa ≤ onset) :
    ∀ N, onset ≤ N →
      C10LogFitFull.fullOnset kappa ≤ (outer sources k clock).result.pcp.nativeWidth N :=
  fun N hN => nativeWidth_ge sources k clock _ N (honset.trans hN)

/-! ## Section 2  The ledger -/

def ledger_of_parts (sources : EightSources) (k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (P : C10StageSeamBridge.Parts sources k p)
    (emitFuel callCap tailBudget : ℕ → ℕ)
    (preFuel cost : Phase → ℕ → ℕ) (clauseBits : ℕ → ℕ)
    (driverCoeff driverExp tableCoeff tableExp rowExp onset A : ℕ)
    (hcallShape : ∀ ph N, P.callFuel ph N
      = C10SupplierCall.callFuel (preFuel ph N) (clauseBits N) (cost ph N))
    (honset : 2 ^ C10LogFitFull.fullOnset
        (6 + (fixedProjection sources).degrees.proofLog
          + C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp rowExp
          + 2) ≤ onset)
    (hdriver : ∀ N, onset ≤ N →
      C10SupplierStage.driverFuel P.entryWidth P.callCount N ≤ driverCoeff
        * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
            ^ driverExp)
    (hrows : ∀ N, onset ≤ N → 2 ^ clauseBits N
      ≤ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
          ^ rowExp)
    (hrow : ∀ (ph : Phase) (N : ℕ), onset ≤ N →
      C10SupplierCall.rowFuel (preFuel ph N) (cost ph N) ≤ tableCoeff
        * (2 ^ ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N
              - (6 + (fixedProjection sources).degrees.proofLog
                  + C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp
                      rowExp + 2)
                * (Nat.log 2
                    ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
                  + 1))
            * ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N + 1)
                ^ tableExp))
    (hrest : ∀ N, onset ≤ N →
      dockedFuel emitFuel (P.entryWidth N) (callCap N) N + tailBudget N ≤ A * (N + 1) ^ 1)
    (hbudget : P.budget = C10SupplierFuel.budgetOf onset
      (C10SupplierStage.stageFuel P.callFuel P.entryWidth P.callCount)
      emitFuel P.entryWidth callCap tailBudget) :
    Runtime sources k (PolynomialClock.ordinaryClock k)
      (C10StageSeamBridge.stageData_of_parts sources k p P).budget := by
  have htwo : (2 : ℕ) ≤ 2 ^ C10LogFitFull.fullOnset
      (6 + (fixedProjection sources).degrees.proofLog
        + C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp rowExp + 2) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num)
          (le_trans (by norm_num) (C10LogFitFull.two_le_fullOnset _))
  have hwidth : ∀ N, onset ≤ N →
      1 ≤ (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N := by
    intro N hN
    exact nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) 1 N
      (by simpa using le_trans (le_trans htwo honset) hN)
  have hsplit := C10SupplierStage.stageFuel_split P.callFuel P.entryWidth P.callCount
    (fun _ N => C10SupplierStage.driverFuel P.entryWidth P.callCount N)
    (fun _ N => 2 ^ clauseBits N)
    (fun ph N => C10SupplierCall.rowFuel (preFuel ph N) (cost ph N)) onset
    (by
      intro ph N _
      rw [hcallShape ph N]
      exact C10SupplierCall.callFuel_le_row _ _ _)
    (fun _ _ _ => le_rfl)
  exact C10Completion.runtimeOf sources k p
    (C10StageSeamBridge.stageData_of_parts sources k p P) emitFuel callCap tailBudget onset A 1
    (6 + (fixedProjection sources).degrees.proofLog)
    (6 + (fixedProjection sources).degrees.proofLog
      + C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp rowExp + 2)
    (C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp rowExp)
    (Nat.succ_le_succ (Nat.zero_le k)) le_rfl le_rfl
    (hgrow_of_dyadic sources k (PolynomialClock.ordinaryClock k) _ onset honset)
    (fun ph N hN => C10SupplierFuel.stageFuel_core
      (fun N => (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N)
      (fun N => Nat.log 2
        ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N) + 1)
      (C10SupplierStage.stageFuel P.callFuel P.entryWidth P.callCount)
      (fun _ N => C10SupplierStage.driverFuel P.entryWidth P.callCount N)
      (fun _ N => 2 ^ clauseBits N)
      (fun ph N => C10SupplierCall.rowFuel (preFuel ph N) (cost ph N))
      (6 + (fixedProjection sources).degrees.proofLog
        + C10SupplierFuel.stageExponent driverCoeff driverExp tableCoeff tableExp rowExp + 2)
      driverCoeff driverExp tableCoeff tableExp rowExp onset hwidth hsplit
      (fun _ N h => hdriver N h) (fun _ N h => hrows N h) hrow ph N hN)
    hrest hbudget

end
end NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly
