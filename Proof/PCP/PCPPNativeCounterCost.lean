import Proof.PCP.PCPPNativeMetadataCost
import Proof.Hierarchy.HierarchyStreamMass

/-! Native execution cost in the actual selected source word, normalized
dimensions, and original oracle input. The exponent is the fixed value 12. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
open SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceParameter {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :=
  p.word.length+R+Q+oracle.size+(PCPPNative.descriptor oracle).length+1
def counterCoefficient := 300000000000*4096^4

theorem carrier_bound {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hr : p.width≤R) (hq : p.queries≤Q) :
    carrier oracle p Q+1≤4096*(sourceParameter oracle p Q)^3 := by
  let Z:=sourceParameter oracle p Q
  have hz : 1≤Z := by dsimp [Z,sourceParameter]; omega
  have hqz : Q≤Z := by dsimp [Z,sourceParameter]; omega
  have hsz : oracle.size≤Z := by dsimp [Z,sourceParameter]; omega
  have ht : p.word.length+R+Q+1≤Z := by dsimp [Z,sourceParameter]; omega
  obtain ⟨hquery,hclause⟩:=Streams.output_mass p R Q hr hq
  have hcube:=Nat.mul_le_mul_left 1025 (Nat.pow_le_pow_left ht 3)
  have hlq:=hquery.trans hcube
  have hlc:=hclause.trans hcube
  have hm:=Streams.clause_count p Q hq
  have hmq:=(Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hqz) 3)
  have hmz : (Codec.clauses p).length≤8*Z^3 := by
    simpa only [mul_pow,show 2^3=8 by decide] using hm.trans hmq
  have hprod:=Nat.mul_le_mul hqz hsz
  have h13 : Z≤Z^3 := Nat.le_self_pow (by decide) Z
  have h23 : Z^2≤Z^3 := Nat.pow_le_pow_right hz (by decide)
  change carrier oracle p Q+1≤4096*Z^3
  unfold carrier PCPPNativeResources.W PCPPNativeEnvelope.value PCPPNativeCount.nativeSize
    PCPPNativeCount.outputIndex PCPPNativeCount.queryEnd PCPPNativeCount.stride
  change (PCPPNativeMetadataMass.queryBytes p R Q).length≤1025*Z^3 at hlq
  have hlin : R+Q+oracle.size+(PCPPNative.descriptor oracle).length+1≤Z := by dsimp [Z,sourceParameter]; omega
  nlinarith

theorem source_counter_budget {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hr : p.width≤R) (hq : p.queries≤Q) :
    PCPPNativeCounterNodes.budget oracle p Q≤counterCoefficient*(sourceParameter oracle p Q)^12 := by
  have hc:=counter_budget oracle p Q
  have hb:=Nat.mul_le_mul_left 300000000000 (Nat.pow_le_pow_left (carrier_bound oracle p Q hr hq) 4)
  refine (hc.trans hb).trans_eq ?_
  simp only [mul_pow,←pow_mul,counterCoefficient]
  ring

end NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
