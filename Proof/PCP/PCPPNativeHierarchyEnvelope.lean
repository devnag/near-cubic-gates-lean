import Proof.PCP.PCPPNativeHierarchyCost

/-! The complete original native/source/cache constructor has exponents
fixed by the selected source algorithms before the hierarchy k is chosen. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def inputExponent (a : PointwisePCPPAlgorithm) := HierarchySourceCost.inputExponent source*degree a
def logExponent (a : PointwisePCPPAlgorithm) := HierarchyStreamCost.logBase source*degree a
def oracleParameter {R : ℕ} (oracle : BooleanCircuit R) := oracle.size+(PCPPNative.descriptor oracle).length+1
def coefficient (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) :=
  48*HierarchyStreamCost.coefficient source H Cpad+
    nativeCoefficient a*(HierarchyStreamCost.sizeCoefficient source H Cpad+1)^degree a
def envelope (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (r : InputRequest) {R : ℕ} (oracle : BooleanCircuit R) :=
  coefficient source a H Cpad*(r.1+1)^inputExponent source a*
    (natBitLength (H.time r.1)+1)^logExponent source a*(oracleParameter oracle)^degree a

theorem parameter_bound {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle≤
      (HierarchyStreamCost.sizeCoefficient source H Cpad+1)*(r.1+1)^HierarchySourceCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logBase source*oracleParameter oracle := by
  have hs:=HierarchyStreamCost.size_bound source H Cpad hcoeff hpad r
  obtain ⟨he,hr,hq⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  have actual : (PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2).word.length+
      PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2+
      PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2+1≤
        HierarchyStreamCost.sizeCoefficient source H Cpad*(r.1+1)^HierarchySourceCost.inputExponent source*
          (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logBase source := by
    dsimp only [PCPPNativeHierarchyNodes.pcp,PCPPNativeHierarchyNodes.width,PCPPNativeHierarchyNodes.queries]
    rw [he,hr,hq]
    exact hs
  let M:=(r.1+1)^HierarchySourceCost.inputExponent source*(natBitLength (H.time r.1)+1)^HierarchyStreamCost.logBase source
  have hm : 1≤M := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have ho : 1≤oracleParameter oracle := by unfold oracleParameter; omega
  have hmo:=Nat.mul_le_mul_left M ho
  have hom:=Nat.mul_le_mul_right (oracleParameter oracle) hm
  have hc:=Nat.mul_le_mul_left (HierarchyStreamCost.sizeCoefficient source H Cpad) hmo
  unfold parameter PCPPNativeResourceCost.sourceParameter
  dsimp only [M] at *
  unfold oracleParameter at *
  nlinarith

theorem original_budget_bound (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hcoeff : H.coefficient≤Cpad)
    (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    originalBudget source a H Cpad hpad r oracle≤envelope source a H Cpad r oracle := by
  let X:=r.1+1
  let Z:=natBitLength (H.time r.1)+1
  let A:=HierarchySourceCost.inputExponent source
  let B:=HierarchyStreamCost.logBase source
  let D:=degree a
  let O:=oracleParameter oracle
  let M:=X^(A*D)*Z^(B*D)*O^D
  have hx : 1≤X := by dsimp [X]; omega
  have hz : 1≤Z := by dsimp [Z]; omega
  have ho : 1≤O := by dsimp [O,oracleParameter]; omega
  have hd : 3≤D := by dsimp [D,degree]; omega
  have hmono:=HierarchySourceScales.monomial_le X Z (A*D) (B*D) (3*A) (3*B) hx hz
    (by nlinarith) (by nlinarith)
  have hmore:=Nat.mul_le_mul_left (X^(A*D)*Z^(B*D)) (Nat.one_le_pow D O ho)
  have hhm : X^(3*A)*Z^(3*B)≤M := hmono.trans (by simpa only [mul_one] using hmore)
  have hH:=Nat.mul_le_mul_left (48*HierarchyStreamCost.coefficient source H Cpad) hhm
  have hparam:=parameter_bound source H Cpad hcoeff hpad r oracle
  have hp : (parameter source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 oracle)^D≤
      (HierarchyStreamCost.sizeCoefficient source H Cpad+1)^D*M := by
    refine (Nat.pow_le_pow_left hparam D).trans_eq ?_
    dsimp only [M,X,Z,A,B,O]
    simp only [mul_pow,←pow_mul]
    ring
  have hnative:=Nat.mul_le_mul_left (nativeCoefficient a) hp
  have hb:=original_budget_polynomial source a H Cpad hcoeff hpad r oracle
  unfold envelope coefficient inputExponent logExponent
  dsimp only [M,X,Z,A,B,D,O,HierarchyStreamCost.inputExponent,HierarchyStreamCost.logExponent] at *
  nlinarith

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
