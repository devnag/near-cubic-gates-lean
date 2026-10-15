import Proof.CaseAnalysis.ScheduleBounds
import Proof.Foundations.PolynomialSchedule

/-! Uniform native-width bound along the actual source lengths N=2^s.
The same source and hierarchy encoding are retained. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairOrdinary ProjectionNormalization
open CloseoutNativeWidth PolynomialSchedule
open SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_dyadic_bound (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s : Nat) :
    (outer sources k clock).result.pcp.nativeWidth (2^s) ≤
      (outer sources k clock).result.pcp.nativeWidth 1+
        nativeJump k (fixedProjection sources).degrees.proofLog*s := by
  induction s with
  | zero=>simp
  | succ s ih=>
    have h:=native_step (fixedProjection sources)
      (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy (padding sources k clock) (2^s)
    have he : 2^(s+1)=2*2^s := by rw [pow_succ];ring
    rw [he]
    change (outer sources k clock).result.pcp.nativeWidth (2*2^s) ≤
      (outer sources k clock).result.pcp.nativeWidth (2^s)+
        nativeJump k (fixedProjection sources).degrees.proofLog at h
    nlinarith

theorem native_dyadic_polynomial (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) :
    PolynomiallyBounded (fun s=>(outer sources k clock).result.pcp.nativeWidth (2^s)) :=
  polynomiallyBounded_mono (native_dyadic_bound sources k clock)
    (polynomiallyBounded_add (polynomiallyBounded_constant ((outer sources k clock).result.pcp.nativeWidth 1))
      (polynomiallyBounded_mul
        (polynomiallyBounded_constant (nativeJump k (fixedProjection sources).degrees.proofLog))
        polynomiallyBounded_id))

end
end NearCubicWires.RepairSource.CloseoutLanguage
