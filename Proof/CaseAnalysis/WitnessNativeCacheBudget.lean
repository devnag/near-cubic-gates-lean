import Proof.CaseAnalysis.WitnessLegalBudget
import Proof.PCP.PCPPNativeSourceCost

/-! The actual native/cache continuation uses the existing measured-node
and faithful-source bounds, including framing of its real emitted nodes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
open PaddedRunnerBudgetClosure BudgetTools PCPPNativeResourceCost
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bound (a : PointwisePCPPAlgorithm) (Z : ℕ) :=
  48*(counterCoefficient*Z^12)+cacheCoefficient a*(4098*Z^3)^cacheDegree a

theorem emitted_length (p : RawProjectionPCP) (R Q : ℕ) (hR:p.width≤R) (hQ:p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    ((PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle).nodes.flatMap PCPPRequestNodeSchema.native).length≤
      nativeBudget oracle p Q := by
  obtain ⟨r,hr,_rt,rh,_rh14,_rt14,_rh16,_rt16,rs⟩:=PCPPNativeClauseOracle.original_run p R Q hR hQ x oracle []
    (PCPPNativeCompactNodes.clauses p R Q hR hQ x)
  simp only [List.append_nil,PCPPNativeCompactNodes.count,PCPPNativeCompactNodes.fields] at hr rs
  have heads:=SelectiveReset.prefix_head (prefix_of_run _ _ _ r hr).1 (102 : Fin 363)
  rw [rh] at heads
  have emitted:((PCPPNativeCompactNodes.nodes p R Q hR hQ x oracle).flatMap PCPPRequestNodeSchema.native).length≤r.steps:=by
    simpa only [initialConfiguration,Nat.zero_add,PCPPNativeCompactNodes.nodes] using heads
  rw [PCPPNativeCompactNodes.circuit_nodes]
  exact emitted.trans rs

theorem budget_le (a : PointwisePCPPAlgorithm) (p : RawProjectionPCP) (R Q : ℕ) (hR:p.width≤R) (hQ:p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    budget a p R Q hR hQ x oracle≤bound a (sourceParameter oracle p Q) := by
  let c:=PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle
  let Z:=sourceParameter oracle p Q
  have hz:1≤Z:=by dsimp only [Z,sourceParameter];omega
  have hRZ:R≤Z:=by dsimp only [Z,sourceParameter];omega
  have carrier:=carrier_bound oracle p Q hR hQ
  change PCPPNativeResourceCost.carrier oracle p Q+1≤4096*Z^3 at carrier
  have size:=(PCPPNativeResources.bounds R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length).2.2.2.1
  have cube:Z≤Z^3:=Nat.le_self_pow (by decide) Z
  have hc:R+c.size+1≤4098*Z^3:=by
    rw [show c.size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length from
      PCPPNativeCompactNodes.circuit_size p R Q hR hQ x oracle]
    dsimp only [PCPPNativeResourceCost.carrier] at carrier
    omega
  have fuel:nativeBudget oracle p Q≤counterCoefficient*Z^12:=by
    have larger:=source_counter_budget oracle p Q hR hQ
    unfold PCPPNativeCounterNodes.budget at larger
    exact (Nat.le_add_left _ _).trans larger
  have original:=source_budget a c (nativeBudget oracle p Q) (emitted_length p R Q hR hQ x oracle)
  exact original.trans (Nat.add_le_add (Nat.mul_le_mul_left 48 fuel)
    (Nat.mul_le_mul_left (cacheCoefficient a) (Nat.pow_le_pow_left hc (cacheDegree a))))

theorem bound_polynomial (a : PointwisePCPPAlgorithm) {Z : ℕ→ℕ} (hz:SourcePoly Z) :
    SourcePoly (fun n=>bound a (Z n)) := by
  dsimp only [bound]
  fast_budget_poly

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
