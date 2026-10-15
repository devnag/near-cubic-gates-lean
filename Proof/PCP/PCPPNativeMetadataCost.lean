import Proof.PCP.PCPPNativeResourceCost

/-! Paid original metadata scans and the original compact-clause loop fit
the same measured resource polynomial as the query loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
open SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dimension_budget (Q : ℕ) : RecoveryProjectionDimension.budget Q.bits≤64*(Q+1)^2 := by
  have hl:=HierarchySourceScales.bits_length_le Q
  have hn : natBitLength Q≤Q+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 Q) 1
  unfold RecoveryProjectionDimension.budget Unary.budget
  rw [RecoveryUnpair.bits_value]
  nlinarith

theorem cold_budget (p : RawProjectionPCP) (R Q s B : ℕ)
    (hr : R≤B) (hq : Q≤B) (hs : s≤B) (hm : (Codec.clauses p).length≤B)
    (hquery : (PCPPNativeMetadataMass.queryBytes p R Q).length≤B) (hclause : (DedupBytes.fields p).length≤B) :
    PCPPNativeColdCounters.budget p R Q s≤4096*(B+1)^2 := by
  have fr:=(PCPPNativeNodeRead.field_budget R).trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  have fs:=(PCPPNativeNodeRead.field_budget s).trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2))
  have fq:=(dimension_budget Q).trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  unfold PCPPNativeColdCounters.budget PCPPNativeMetadataMass.budget PCPPNativeMetadata.budget
    PCPPNativeMetadataPrefix.budget PCPPNativeOracleCold.budget PCPPNativeQueryHeader.budget
    PCPPNativeTripleMass.budget WilliamsUnaryProduct.budget
  rw [PCPPNativeOriginalMass.triple_source,DedupBytes.output_fields,DedupBytes.output_count]
  nlinarith

theorem oracle_scalar_budget {R : ℕ} (oracle : BooleanCircuit R) (B : ℕ)
    (hr : R≤B) (hs : oracle.size≤B) (hl : (PCPPNative.descriptor oracle).length≤B) :
    PCPPNativeOracleScalars.budget oracle≤1024*(B+1)^2 := by
  have hi : oracle.output.val≤B := oracle.output.isLt.le.trans hs
  have fi:=(PCPPNativeNodeRead.field_budget oracle.output.val).trans
    (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
  have hR : natBitLength R≤R+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 R) 1
  have hS : natBitLength oracle.size≤oracle.size+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 oracle.size) 1
  have body : (PCPPNativeOracleSkip.stream oracle.nodes).length≤B := by
    rw [PCPPNativeQuery.original_parts] at hl
    simpa only [PCPPNativeOracleSkip.stream,PCPPNativeQuery.originalBody,PCPPNativeNodeLoop.nativeWords]
      using (show (PCPPNativeQuery.originalBody oracle).length≤B from by simp only [List.length_append] at hl; omega)
  unfold PCPPNativeOracleScalars.budget PCPPNativeOracleOutputCold.budget PCPPNativeOracleOutputCold.rawBudget
    PCPPNativeOracleOutput.budget PCPPNativeOracleFooterPosition.budget PCPPQueryField.pairCost PCPPQueryField.fieldCost
  nlinarith

theorem clause_budget (W M : ℕ) (hm : M≤W) :
    PCPPNativeClauseRawRun.budget (PCPPNativeCapacityReady.C W) M≤1000000*(W+1)^3 := by
  have hp:=Nat.mul_le_mul_right ((W+1)^2) (show M≤W+1 by omega)
  have hp3 : M*(W+1)^2≤(W+1)^3 := by simpa [pow_succ,Nat.mul_comm] using hp
  have h23 : (W+1)^2≤(W+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h13 : W+1≤(W+1)^3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0<W+1) (by decide : 1≤3))
  unfold PCPPNativeClauseRawRun.budget PCPPNativeClauseDrivers.budget PCPPNativeCapacityReady.C
  nlinarith

def carrier {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :=
  PCPPNativeResources.W R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length+(PCPPNative.descriptor oracle).length

theorem counter_budget {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :
    PCPPNativeCounterNodes.budget oracle p Q≤300000000000*(carrier oracle p Q+1)^4 := by
  let W:=PCPPNativeResources.W R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length
  let B:=carrier oracle p Q
  obtain ⟨_,hr,hq,hn,ht,hlq,hlc⟩:=PCPPNativeResources.bounds R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length
  have hwb : W≤B := by dsimp [W,B,carrier]; omega
  have hs : oracle.size≤W := by dsimp [PCPPNativeCount.stride] at ht; omega
  have hm : (Codec.clauses p).length≤W := by
    dsimp [PCPPNativeCount.nativeSize,PCPPNativeCount.outputIndex] at hn
    omega
  have cold:=cold_budget p R Q oracle.size B (hr.trans hwb) (hq.trans hwb) (hs.trans hwb)
    (hm.trans hwb) (hlq.trans hwb) (hlc.trans hwb)
  have scalar:=oracle_scalar_budget oracle B (hr.trans hwb) (hs.trans hwb) (by dsimp [B,carrier]; omega)
  have query:=query_budget R Q oracle.size (Codec.clauses p).length
    (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length
  have clause:=clause_budget W (Codec.clauses p).length hm
  have h24 : (B+1)^2≤(B+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h34 : (W+1)^3≤(B+1)^4 := (Nat.pow_le_pow_left (Nat.add_le_add_right hwb 1) 3).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  have h44 : (W+1)^4≤(B+1)^4 := Nat.pow_le_pow_left (Nat.add_le_add_right hwb 1) 4
  have hp : 1≤(B+1)^4 := Nat.one_le_pow _ _ (by omega)
  change PCPPNativeCounterNodes.budget oracle p Q≤300000000000*(B+1)^4
  unfold PCPPNativeCounterNodes.budget PCPPNativeClauseOracle.budget PCPPNativeClauseOracle.prefixBudget
  dsimp only [W,B] at *
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
