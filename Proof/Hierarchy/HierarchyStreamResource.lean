import Proof.Hierarchy.HierarchyStreamMass

/-! One proved scalar bounds the actual query/clause byte streams and their
width/query drivers. Fixed polynomial serializer costs therefore preserve a
source-fixed input exponent before the hierarchy degree is selected. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Streams
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resource (p : RawProjectionPCP) (R Q : ℕ) :=
  (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length+(DedupBytes.fields p).length+R+Q+1

theorem resource_bound (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    resource p R Q ≤ 2051*(p.word.length+R+Q+1)^3 := by
  obtain ⟨hquery,hclause⟩ := output_mass p R Q hr hq
  have hz : R+Q+1 ≤ (p.word.length+R+Q+1)^3 :=
    (by omega : R+Q+1 ≤ p.word.length+R+Q+1).trans (Nat.le_self_pow (by decide) _)
  dsimp only [resource]
  omega

end NearCubicWires.RepairSource.ProjectionNormalization.Streams
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreamCost
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

noncomputable def resourceCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  2051*(sizeCoefficient source H Cpad)^3

theorem resource_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    Streams.resource (source.output (HierarchyEncode.encode H Cpad r))
      (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1) ≤
      resourceCoefficient source H Cpad*(r.1+1)^inputExponent source*
        (natBitLength (H.time r.1)+1)^logExponent source := by
  have hb := Streams.resource_bound (source.output (HierarchyEncode.encode H Cpad r))
    (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)
    (HierarchyProjection.width_fits source H Cpad hpad r) (HierarchyProjection.queries_fit source H Cpad hpad r)
  have hz := size_bound source H Cpad hcoeff hpad r
  have hc := Nat.mul_le_mul_left 2051 (Nat.pow_le_pow_left hz 3)
  refine (hb.trans hc).trans_eq ?_
  dsimp only [resourceCoefficient,inputExponent,logExponent]
  simp only [mul_pow,←pow_mul]
  ring

theorem polynomial_resource_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) (C d : ℕ) :
    C*(Streams.resource (source.output (HierarchyEncode.encode H Cpad r))
      (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)+1)^d ≤
      (C*(resourceCoefficient source H Cpad+1)^d)*(r.1+1)^(inputExponent source*d)*
        (natBitLength (H.time r.1)+1)^(logExponent source*d) := by
  have hb := resource_bound source H Cpad hcoeff hpad r
  let M := (r.1+1)^inputExponent source*(natBitLength (H.time r.1)+1)^logExponent source
  have hM : 1 ≤ M := by
    have hpositive : 0<M := by dsimp [M]; positivity
    omega
  have ha : Streams.resource (source.output (HierarchyEncode.encode H Cpad r))
      (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)+1 ≤
      (resourceCoefficient source H Cpad+1)*M := by
    rw [Nat.mul_assoc] at hb
    change _ ≤ resourceCoefficient source H Cpad*M at hb
    nlinarith
  have hc := Nat.mul_le_mul_left C (Nat.pow_le_pow_left ha d)
  refine hc.trans_eq ?_
  dsimp only [M]
  simp only [mul_pow,←pow_mul]
  ring

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreamCost
