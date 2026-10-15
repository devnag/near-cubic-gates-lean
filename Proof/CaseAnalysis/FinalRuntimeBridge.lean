import Proof.CaseAnalysis.FinalResidualLeaves
import Proof.CaseAnalysis.FinalRuntimeSplit

namespace NearCubicWires.RepairSource.CloseoutFinal

open SelectedRecoveryIntegration SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **`c10.runtime` from the ledger.** `Runtime` is a structure with data fields, so this
is a `def` (its type is not a proposition). -/
noncomputable def runtime_of_ledger (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2)))
    (fuel : ℕ → ℕ) (A a sigma kappa splitOnset : ℕ) (logWidth : ℕ → ℕ)
    (ha : a ≤ k+1) (hsigma : 6+(fixedProjection sources).degrees.proofLog ≤ sigma)
    (hsk : sigma ≤ kappa)
    (hpoly : ∀ N, splitOnset ≤ N → fuel N+2 ≤ A*(N+1)^a
      + hotOf kappa (fun N => (outer sources k clock).result.pcp.nativeWidth N) logWidth N)
    (hlog : ∀ N, splitOnset ≤ N →
      (outer sources k clock).result.pcp.nativeWidth N ≤ 2^(logWidth N))
    (hfit : ∀ N, splitOnset ≤ N →
      kappa*logWidth N ≤ (outer sources k clock).result.pcp.nativeWidth N) :
    Runtime sources k clock fuel where
  A := A
  B := 1
  a := a
  sigma := sigma
  hot := hotOf kappa (fun N => (outer sources k clock).result.pcp.nativeWidth N) logWidth
  ha := ha
  hsigma := hsigma
  splitOnset := splitOnset
  hpoly := hpoly
  hdamp := hdamp_of_ledger kappa sigma splitOnset
    (fun N => (outer sources k clock).result.pcp.nativeWidth N) logWidth hsk hlog hfit

end NearCubicWires.RepairSource.CloseoutFinal
