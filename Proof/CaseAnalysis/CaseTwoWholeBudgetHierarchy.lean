import Proof.PCP.PCPPNativeCanonicalBounds
import Proof.Circuits.PaddedRunnerBudgetClosure
import Proof.Foundations.RecoveryScheduleEnvelope

/-! Fixed-source polynomials for the original hierarchy request. These
constants may depend on the fixed hierarchy clock, as allowed in C.12. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudgetHierarchy
open SourceInterfaces RepairSource RepairRepresentation OuterPCPRecovery RecoveryScheduleEnvelope PolynomialClock
open RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
  (Cpad degree : ℕ)

def clockScale (n : ℕ) := natBitLength (H.time n)+1
def width (n : ℕ) := HierarchySourceCost.widthCoefficient source H Cpad*clockScale H n
def oracleSize (n : ℕ) := (width source H Cpad n+1)^(2^oracleDepth degree)
def oracleScale (n : ℕ) := 40*(width source H Cpad n+oracleSize source H Cpad degree n+5)^2
def parameter (n : ℕ) :=
  (HierarchyStreamCost.sizeCoefficient source H Cpad+1)*(n+1)^HierarchySourceCost.inputExponent source*
    (clockScale H n)^HierarchyStreamCost.logBase source*oracleScale source H Cpad degree n
def requestSize (n : ℕ) :=
  (2*a.minimumArity+5)*(4098*(parameter source H Cpad degree n)^3)
def nativeBudget (n : ℕ) :=
  PCPPNativeHierarchySource.coefficient source a H Cpad*(n+1)^PCPPNativeHierarchySource.inputExponent source a*
    (clockScale H n)^PCPPNativeHierarchySource.logExponent source a*
      (oracleScale source H Cpad degree n)^PCPPNativeHierarchySource.degree a
def inputSize (n : ℕ) := 2*n+2*clockScale H n+2
def envelope (n : ℕ) :=
  nativeBudget source a H Cpad degree n+
    PCPPQueryCachedBounds.capacity a (requestSize source a H Cpad degree n)+
      oracleScale source H Cpad degree n+inputSize H n+5

theorem clock_polynomial : SourcePoly (clockScale H) := by
  have ht : SourcePoly (H.time) :=
    ((sourcePoly_pow sourcePoly_id (k+2)).add (polyDominated_const 1)).const_mul H.coefficient
  apply ((ht.add (polyDominated_const 1)).add (polyDominated_const 1)).mono
  intro n
  exact Nat.add_le_add_right (PCPPQueryCost.width_le (H.time n)) 1

theorem envelope_polynomial : SourcePoly (envelope source a H Cpad degree) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v) := polyDominated_const v
  have hz:=clock_polynomial H
  have hw:=hz.const_mul (HierarchySourceCost.widthCoefficient source H Cpad)
  have ho:=sourcePoly_pow (hw.add (hc 1)) (2^oracleDepth degree)
  have hos:=(sourcePoly_pow ((hw.add ho).add (hc 5)) 2).const_mul 40
  have hn:=sourcePoly_id.add (hc 1)
  have hp:=(((sourcePoly_pow hn (HierarchySourceCost.inputExponent source)).const_mul
    (HierarchyStreamCost.sizeCoefficient source H Cpad+1)).mul
      (sourcePoly_pow hz (HierarchyStreamCost.logBase source))).mul hos
  have hr:=((sourcePoly_pow hp 3).const_mul 4098).const_mul (2*a.minimumArity+5)
  have hm:=(sourcePoly_pow (hr.add (hc 1)) (PCPPQueryCachedBounds.degree a)).const_mul
    (PCPPQueryCachedBounds.coefficient a)
  have hb:=(((sourcePoly_pow hn (PCPPNativeHierarchySource.inputExponent source a)).const_mul
    (PCPPNativeHierarchySource.coefficient source a H Cpad)).mul
      (sourcePoly_pow hz (PCPPNativeHierarchySource.logExponent source a))).mul
        (sourcePoly_pow hos (PCPPNativeHierarchySource.degree a))
  have hi:=((sourcePoly_id.const_mul 2).add (hz.const_mul 2)).add (hc 2)
  exact (((hb.add hm).add hos).add hi).add (hc 5)

theorem request_size_bound (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let c:=PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
    (PCPPRequestBoundary.request a c).circuit.size+(PCPPRequestBoundary.request a c).arity≤
      (2*a.minimumArity+5)*(4098*
        (PCPPNativeHierarchySource.parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle)^3) := by
  dsimp only
  let p:=PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let Q:=PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let c:=PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
  let Z:=PCPPNativeHierarchySource.parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle
  have hrp : p.width≤R := PCPPNativeHierarchyNodes.width_fits source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
  have hqp : p.queries≤Q := PCPPNativeHierarchyNodes.queries_fit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
  have hR : R≤Z := by dsimp [R,Z,PCPPNativeHierarchySource.parameter,PCPPNativeResourceCost.sourceParameter];omega
  have hs : c.size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length :=
    PCPPNativeCompactNodes.circuit_size p R Q hrp hqp r.2 oracle
  have hcarrier:=PCPPNativeResourceCost.carrier_bound oracle p Q hrp hqp
  have hsize:=(PCPPNativeResources.bounds R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length).2.2.2.1
  have h13 : Z≤Z^3 := Nat.le_self_pow (by decide) Z
  have hS : R+c.size+1≤4098*Z^3 := by
    rw [hs]
    dsimp only [PCPPNativeResourceCost.carrier] at hcarrier
    change _≤4096*Z^3 at hcarrier
    dsimp only [R] at hsize
    omega
  have hreq:=PCPPNativeResourceCost.cache_parameter a c
  have hm:=Nat.mul_le_mul_left (2*a.minimumArity+5) hS
  change (PCPPRequestBoundary.request a c).arity+(PCPPRequestBoundary.request a c).circuit.size+5≤
    (2*a.minimumArity+5)*(R+c.size+1) at hreq
  exact (by omega : (PCPPRequestBoundary.request a c).circuit.size+
    (PCPPRequestBoundary.request a c).arity≤(2*a.minimumArity+5)*(R+c.size+1)).trans hm

theorem bounds (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (horacle : oracle.size≤oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let req:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    PCPPNativeHierarchySource.originalBudget source a H Cpad hpad r oracle≤envelope source a H Cpad degree r.1 ∧
      PCPPQueryCachedBounds.capacity a (req.circuit.size+req.arity)≤envelope source a H Cpad degree r.1 ∧
      (PCPPNative.descriptor oracle).length≤envelope source a H Cpad degree r.1 ∧
      (HierarchySourceInput.hierarchyInput H r).length≤envelope source a H Cpad degree r.1 := by
  dsimp only
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  have hr : R≤width source H Cpad r.1 := by
    obtain ⟨_,he,_⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
    dsimp only [R,PCPPNativeHierarchyNodes.width]
    rw [he]
    exact HierarchySourceCost.width_bound source H Cpad hcoeff hpad r.1
  have ho : oracle.size≤oracleSize source H Cpad degree r.1 := by
    have hb:=pairIter_add_one_le_pow (oracleDepth degree) R
    have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) (2^oracleDepth degree)
    change oracle.size≤(width source H Cpad r.1+1)^(2^oracleDepth degree)
    change oracle.size≤pairIter (oracleDepth degree) R at horacle
    omega
  have hbase : R+oracle.size+5≤width source H Cpad r.1+oracleSize source H Cpad degree r.1+5 := by omega
  have hp : PCPPNativeHierarchySource.oracleParameter oracle≤oracleScale source H Cpad degree r.1 :=
    (PCPPNative.oracle_parameter_bound oracle).trans (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left hbase 2))
  have hl : (PCPPNative.descriptor oracle).length≤oracleScale source H Cpad degree r.1 := by
    have hb:=PCPPNative.descriptor_length_bound oracle
    change (PCPPNative.descriptor oracle).length≤39*(R+oracle.size+5)^2 at hb
    have hm:=Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left hbase 2)
    unfold oracleScale
    omega
  have hparameter : PCPPNativeHierarchySource.parameter source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2 oracle≤parameter source H Cpad degree r.1 := by
    exact (PCPPNativeHierarchySource.parameter_bound source H Cpad hcoeff hpad r oracle).trans
      (Nat.mul_le_mul_left _ hp)
  have hreq:=request_size_bound source a H Cpad hpad r oracle
  have hreq' := hreq.trans (Nat.mul_le_mul_left (2*a.minimumArity+5)
    (Nat.mul_le_mul_left 4098 (Nat.pow_le_pow_left hparameter 3)))
  have hm:=Nat.mul_le_mul_left (PCPPQueryCachedBounds.coefficient a)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hreq' 1) (PCPPQueryCachedBounds.degree a))
  have hb : PCPPNativeHierarchySource.originalBudget source a H Cpad hpad r oracle≤nativeBudget source a H Cpad degree r.1 := by
    apply (PCPPNativeHierarchySource.original_budget_bound source a H Cpad hcoeff hpad r oracle).trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp (PCPPNativeHierarchySource.degree a))
  have hi : (HierarchySourceInput.hierarchyInput H r).length≤ inputSize H r.1 := by
    have hbits:=PCPPQueryBounds.bits_le (H.time r.1)
    simp only [HierarchySourceInput.hierarchyInput,List.length_append,frame_length,List.length_ofFn]
    dsimp only [inputSize,clockScale]
    omega
  unfold envelope
  change _≤PCPPQueryCachedBounds.capacity a (requestSize source a H Cpad degree r.1) at hm
  exact ⟨by omega,hm.trans (by omega),by omega,by omega⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudgetHierarchy
