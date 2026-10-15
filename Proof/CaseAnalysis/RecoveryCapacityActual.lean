import Proof.CaseAnalysis.RecoveryCapacityEnvelope

/-! Apply the fixed recovery envelope to the original padded universal
source, its exact normalized clause stream, and the live final-length bound. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCapacity
open RepairOrdinary ProjectionNormalization SourceInterfaces OuterPCPRecovery RecoveryScheduleEnvelope
open CloseoutRecoveryWorkspace PolynomialClock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem clause_bytes (p : RawProjectionPCP) : (DedupBytes.fields p).length ≤ p.word.length := by
  have h:=((List.dedup_sublist (DedupBytes.rows p)).map ClauseEquality.stream).flatten.length_le
  change (SuffixScan.stream (DedupBytes.rows p).dedup).length ≤
    (SuffixScan.stream (DedupBytes.rows p)).length at h
  rw [DedupBytes.output_fields] at h
  exact h.trans (Streams.source_sizes p).2.2.2.1

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad degree : ℕ)

theorem actual_bounds (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (n : ℕ) (hN : r.1 ≤ 2^n)
    (hR : HierarchyProjection.width source H Cpad r.1 ≤ n) :
    let p:=source.output (HierarchyEncode.encode H Cpad r)
    let R:=HierarchyProjection.width source H Cpad r.1
    let Q:=HierarchyProjection.queries source H Cpad r.1
    let B:=oracleSizeBound degree R
    let W:=majorant source H Cpad degree (2^n)
    originalWorkspace R B Q (Codec.clauses p).length ≤ W ∧
      R ≤ W ∧ Q ≤ W ∧ B ≤ W ∧ (DedupBytes.fields p).length ≤ W ∧ 2^R ≤ W := by
  intro p R Q B W
  let x:=2^n
  let Z:=sourceUpper source H Cpad x
  have hs:=source_bound source H Cpad hcoeff hpad r x hN
  change p.word.length+R+Q+1 ≤ Z at hs
  have hr : R ≤ width x := by
    have he : width x=n+1 := by simp [width,x,natBitLength,Nat.log_pow]
    rw [he]
    exact hR.trans (Nat.le_succ n)
  have hb : B ≤ fullBound degree x := by
    have h:=pairIter_add_one_le_pow (oracleDepth degree) R
    have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) (2^oracleDepth degree)
    change pairIter (oracleDepth degree) R ≤ (width x+1)^(2^oracleDepth degree)
    omega
  have hq : Q ≤ Z := by omega
  have hcl : (Codec.clauses p).length ≤ (2*Z)^3 :=
    (Streams.clause_count p Q (HierarchyProjection.queries_fit source H Cpad hpad r)).trans
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hq) 3)
  have hg:=(workspace_mono hr hb hq hcl)
  have hgW : originalWorkspace R B Q (Codec.clauses p).length ≤ W := hg.trans (by
    change originalWorkspace (width x) (fullBound degree x) Z ((2*Z)^3) ≤
      originalWorkspace (width x) (fullBound degree x) Z ((2*Z)^3)+1024*(Z+1)^3+2^width x+x+1
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))
  have hf:=original_workspace_fields R B Q (Codec.clauses p).length
  have hbytes : (DedupBytes.fields p).length ≤ W := by
    have hbts:=(clause_bytes p).trans (by omega : p.word.length ≤ Z)
    have hz : Z ≤ 1024*(Z+1)^3 := by
      have hh : Z+1 ≤ (Z+1)^3 := Nat.le_self_pow (by decide) _
      omega
    apply hbts.trans (hz.trans _)
    change 1024*(Z+1)^3 ≤
      originalWorkspace (width x) (fullBound degree x) Z ((2*Z)^3)+1024*(Z+1)^3+2^width x+x+1
    exact (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have htwo : 2^R ≤ W := (Nat.pow_le_pow_right (by decide : 0 < 2) hr).trans (by
    dsimp only [W,majorant,x]
    omega)
  exact ⟨hgW,hf.1.trans hgW,hf.2.2.1.trans hgW,hf.2.1.trans hgW,hbytes,htwo⟩

/-- One physically constructible W funds every live original source request. -/
theorem actual_capacity (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ∃ A B0 : ℕ, ∀ (n : ℕ) (r : InputRequest), r.1 ≤ 2^n →
      HierarchyProjection.width source H Cpad r.1 ≤ n →
      let p:=source.output (HierarchyEncode.encode H Cpad r)
      let R:=HierarchyProjection.width source H Cpad r.1
      let Q:=HierarchyProjection.queries source H Cpad r.1
      let B:=oracleSizeBound degree R
      let W:=CloseoutCapacity.capacity A B0 n
      originalWorkspace R B Q (Codec.clauses p).length ≤ W ∧
        R ≤ W ∧ Q ≤ W ∧ B ≤ W ∧ (DedupBytes.fields p).length ≤ W ∧ 2^R ≤ W := by
  obtain ⟨A,B0,hW⟩:=exists_capacity source H Cpad degree
  refine ⟨A,B0,fun n r hn hr=>?_⟩
  obtain ⟨hg,hR,hQ,hB,hbytes,htwo⟩:=actual_bounds source H Cpad degree hcoeff hpad r n hn hr
  exact ⟨hg.trans (hW n),hR.trans (hW n),hQ.trans (hW n),hB.trans (hW n),
    hbytes.trans (hW n),htwo.trans (hW n)⟩

end
end NearCubicWires.RepairSource.CloseoutRecoveryCapacity
