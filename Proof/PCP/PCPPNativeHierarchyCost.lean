import Proof.PCP.PCPPNativeSourceCost
import Proof.PCP.PCPPNativeHierarchySourceReady

/-! Whole original hierarchy/native/source/cache runtime, before separating
the selected source word bound into the original input and clock currencies. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
open PCPPNativeResourceCost
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def parameter (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k CH Cpad code x)) :=
  PCPPNativeResourceCost.sourceParameter oracle (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)
    (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
def degree (a : PointwisePCPPAlgorithm) := max 12 (3*cacheDegree a)
def nativeCoefficient (a : PointwisePCPPAlgorithm) :=
  528+48*counterCoefficient+cacheCoefficient a*4098^cacheDegree a

theorem original_budget_polynomial (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    originalBudget source a H Cpad hpad r oracle≤
      48*(HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source)+
      nativeCoefficient a*(parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle)^degree a := by
  let p:=PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let Q:=PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let c:=PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle
  let Z:=parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle
  have hrp : p.width≤R := PCPPNativeHierarchyNodes.width_fits source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
  have hqp : p.queries≤Q := PCPPNativeHierarchyNodes.queries_fit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
  have hz : 1≤Z := by dsimp [Z,parameter,PCPPNativeResourceCost.sourceParameter]; omega
  have hR : R≤Z := by dsimp [R,Z,parameter,PCPPNativeResourceCost.sourceParameter]; omega
  have hL : (PCPPNative.descriptor oracle).length≤Z := by dsimp [Z,parameter,PCPPNativeResourceCost.sourceParameter]; omega
  have hcsize : c.size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length :=
    PCPPNativeCompactNodes.circuit_size p R Q hrp hqp r.2 oracle
  have carrier:=carrier_bound oracle p Q hrp hqp
  have hsize:=(PCPPNativeResources.bounds R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length).2.2.2.1
  have h13 : Z≤Z^3 := Nat.le_self_pow (by decide) Z
  have hS : R+c.size+1≤4098*Z^3 := by
    rw [hcsize]
    dsimp only [PCPPNativeResourceCost.carrier] at carrier
    change _≤4096*Z^3 at carrier
    dsimp only [R] at hsize
    omega
  have hcounter:=source_counter_budget oracle p Q hrp hqp
  change PCPPNativeCounterNodes.budget oracle p Q≤counterCoefficient*Z^12 at hcounter
  have h12:=Nat.pow_le_pow_right hz (show 12≤degree a from Nat.le_max_left _ _)
  have hd:=Nat.pow_le_pow_right hz (show 3*cacheDegree a≤degree a from Nat.le_max_right _ _)
  have hpower:=Nat.pow_le_pow_left hS (cacheDegree a)
  rw [mul_pow,←pow_mul] at hpower
  have hscaled:=Nat.mul_le_mul_left (4098^cacheDegree a) hd
  have hwhole:=Nat.mul_le_mul_left (cacheCoefficient a) (hpower.trans hscaled)
  have hCounterWhole:=Nat.mul_le_mul_left counterCoefficient h12
  have hOne : 1≤Z^degree a := Nat.one_le_pow _ _ hz
  have hZ : Z≤Z^degree a := Nat.le_self_pow (by unfold degree; omega) Z
  obtain ⟨native,hn,ns,_,head,_⟩:=PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hlen:=SelectiveReset.prefix_head (prefix_of_run _ _ _ native hn).1 (PCPPNativeHierarchyNodes.slots source k 177)
  rw [head] at hlen
  change (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤0+native.steps at hlen
  have hpaid : (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle := by omega
  have hsource:=PCPPNativeResourceCost.source_budget a c (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle) hpaid
  change originalBudget source a H Cpad hpad r oracle≤48*PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle+
    cacheCoefficient a*(R+c.size+1)^cacheDegree a at hsource
  unfold PCPPNativeHierarchyNodes.originalBudget at hsource
  change originalBudget source a H Cpad hpad r oracle≤_+nativeCoefficient a*Z^degree a
  unfold nativeCoefficient
  dsimp only [p,Q] at hcounter
  nlinarith

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
