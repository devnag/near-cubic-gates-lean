import Proof.Hierarchy.HierarchyEncodeBounds
import Proof.PCP.ProjectionNormalizationDimensions

/-! The single selected U source supplies length-only normalized dimensions.
The fixed-slice coefficient bridge transports its proof envelope to the
original hierarchy clock, without changing the source witness or clock. -/
namespace NearCubicWires.RepairSource.HierarchyProjection
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :=
  Dimensions.width source (HierarchyEncode.length H Cpad n)
def queries {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :=
  Dimensions.queries source (HierarchyEncode.length H Cpad n)
def proofCoefficient {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  2*source.coefficient*HierarchyEncode.timeCoefficient H Cpad*
    (HierarchyEncode.timeLogCoefficient H Cpad)^source.degrees.proofLog

theorem width_fits {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    (source.output (HierarchyEncode.encode H Cpad r)).width ≤ width source H Cpad r.1 :=
  Dimensions.width_fits source _ (by have := HierarchyEncode.encode_length H Cpad hpad r; omega)

theorem queries_fit {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    (source.output (HierarchyEncode.encode H Cpad r)).queries ≤ queries source H Cpad r.1 :=
  Dimensions.queries_fit source _ (by have := HierarchyEncode.encode_length H Cpad hpad r; omega)

theorem proof_bound {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) :
    2^width source H Cpad n ≤ proofCoefficient source H Cpad*H.time n*
      logScale (H.time n)^(5+source.degrees.proofLog) := by
  have hp := Dimensions.proof_size source (HierarchyEncode.encode H Cpad ⟨n,fun _ => false⟩)
    (by have := HierarchyEncode.encode_length H Cpad hpad ⟨n,fun _ => false⟩; omega)
  calc _ ≤ 2*(source.coefficient*UAggregateClock.time (HierarchyEncode.length H Cpad n)*
      logScale (UAggregateClock.time (HierarchyEncode.length H Cpad n))^source.degrees.proofLog) := hp
       _ ≤ 2*(source.coefficient*(HierarchyEncode.timeCoefficient H Cpad*H.time n*logScale (H.time n)^5)*
         (HierarchyEncode.timeLogCoefficient H Cpad*logScale (H.time n))^source.degrees.proofLog) := by
         gcongr
         · exact HierarchyEncode.time_bound H Cpad hcoeff n
         · exact HierarchyEncode.time_log_bound H Cpad hcoeff n
       _ = proofCoefficient source H Cpad*H.time n*logScale (H.time n)^(5+source.degrees.proofLog) := by
         simp only [proofCoefficient,mul_pow,pow_add]
         ring

theorem query_bound {v : OrdinaryVerifier} (source : ProjectionSourceAlgorithm v UAggregateClock.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    queries source H Cpad n ≤ source.coefficient*(width source H Cpad n+1)^source.degrees.queries :=
  Nat.le_refl _

end NearCubicWires.RepairSource.HierarchyProjection
