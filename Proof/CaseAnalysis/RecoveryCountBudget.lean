import Proof.CaseAnalysis.RecoveryCountResources

/-! One loose iteration budget includes the entire original grammar,
all original rows, every handoff, and the paid next-candidate driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyBudget (B W R : ℕ):=32768*(W+1)*(B+2)+RecoveryBoundedFixedRows.reusableBudget B W R

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem Resources.body_budget (z : Resources p R Q hr hq (bound:=bound) x) (count : Fin bound) :
    RecoveryBoundedCountPipeline.budget (capacity z.base.W) z.base.D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L R count.val Q
      (Codec.clauses p).length z.base.B z.base.W bound≤bodyBudget z.base.B z.base.W R := by
  let C:=capacity z.base.W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
  have hi:=RecoveryBoundedCounts.packet_inputs z.room z.allocation count Q (Codec.clauses p).length
    z.base.query_bound z.clauses_bound
  have h0:=hi.1 0
  have h1:=hi.1 1
  have h2:=hi.1 2
  have h3:=hi.1 3
  have h4:=hi.1 4
  have h5:=hi.1 5
  change 2*C+4≤z.base.B at h0
  change 2*F+4≤z.base.B at h1
  change 2*R+4≤z.base.B at h2
  change 2*count.val+4≤z.base.B at h3
  change 2*Q+4≤z.base.B at h4
  change 2*(Codec.clauses p).length+4≤z.base.B at h5
  have hc:=hi.2.1
  have hp:=RecoveryBoundedRowPacketAppend.refresh_bound C F R (count.val+1) Q
    (Codec.clauses p).length z.base.B (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hl:=RecoveryBoundedRowReload.budget_bound (z.fields (count.val+1)) z.base.B
    (z.metadata_all (count.val+1) (by omega))
  have install : RecoveryBoundedRowPacketInstall.budget C z.base.D F z.base.L R (count.val+1)
      Q (Codec.clauses p).length z.base.B≤1024*(z.base.B+1) := by
    unfold RecoveryBoundedRowPacketInstall.budget RecoveryBoundedRowPacketLoad.budget
    change RecoveryBoundedRowPacketAppend.refreshBudget C F R (count.val+1) Q (Codec.clauses p).length z.base.B+1+
      ((2*z.base.B+4)+1+RecoveryBoundedRowReload.budget (z.fields (count.val+1)) z.base.B)≤_
    omega
  have hbound:=(z.allocation.scalars (⟨0,by omega⟩ : Fin (bound+1))).limit 5
  change bound+1≤z.base.W at hbound
  have hg:=RecoveryBoundedGrammarCold.total_budget_W z.base.B bound count.val z.base.W count.isLt hbound
  have hm : z.base.B+2≤(z.base.W+1)*(z.base.B+2):=by
    exact Nat.le_mul_of_pos_left _ (by omega)
  unfold RecoveryBoundedCountPipeline.budget RecoveryBoundedCountPipeline.afterGrammarBudget
    RecoveryBoundedCountPipeline.afterRowsBudget RecoveryBoundedCountPipeline.afterPacketBudget
    RecoveryBoundedCountScalarReset.budget RecoveryBoundedCountRowEntry.budget
    RecoveryBoundedGrammarCold.atomBudget bodyBudget
  change (128*(z.base.B+2)+1+RecoveryBoundedGrammarCold.compiledBudget z.base.B bound count.val)+1+
    ((64*(z.base.B+2)+1+(2*count.val+4+1+RecoveryBoundedRowPacketInstall.budget C z.base.D F z.base.L R
      (count.val+1) Q (Codec.clauses p).length z.base.B)+1+RecoveryBoundedFixedRows.reusableBudget z.base.B z.base.W R)+1+
      RecoveryBoundedGrammarDriverBank.refreshBudget z.base.B (count.val+1))≤_
  simp only [Nat.mul_assoc] at hg ⊢
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
