import Proof.CaseAnalysis.CommonProgramSource

/-! The actual original full-formula recovery supplies every field used
by both common branches; no recovery receipt is assumed here. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open SelectedRecoveryIntegration RecoveryScheduleEnvelope OrdinaryOracleCompose RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def recoveryBudget (p : Parameters) (r : InputRequest) (W : ℕ):=
  RecoveryBoundedCold.budget (source p) p.k p.degree (hierarchy p).coefficient (pad p) (code p) r.2 W (pad_large p)
def recoveryDescription (p : Parameters) (r : InputRequest):=frame
  (RecoveryPrefixBody.search true
    (RecoveryBoundedCold.payload (source p) p.k p.degree (hierarchy p).coefficient (pad p) (code p) r.2 (pad_large p))
    (RecoveryBoundedCold.total (source p) p.k p.degree (hierarchy p).coefficient (pad p) (code p) r.2) [])

theorem source_recovery (p : Parameters) (r : InputRequest) (W : ℕ) (fits : Fits p r W) :
    ∃ cost ≤ recoveryBudget p r W,∃ final : (recovery p).Config,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (recovery p) cost
        (initialConfiguration (recovery p).base.machine
          (RecoveryBoundedCold.input (source p) p.k p.degree (hierarchyWord p r) W)) final ∧
      (recovery p).base.machine.halted final.control=true ∧
      readTapeBit (final.tapes (recoveryFlagLocal p)) 0=caseTwo (globalPCP p) p.degree r.2 ∧
      final.heads (recoveryFlagLocal p)=0 ∧
      (final.tapes (RecoveryBoundedCold.queryPort (source p) p.k p.degree)).length ≤ cost ∧
      final.heads (RecoveryBoundedCold.queryPort (source p) p.k p.degree)=0 ∧
      (∀ j,final.tapes (twoRecoveryLocal p j)=
        twoRecoveryWords (hierarchyWord p r) (recoveryDescription p r) (R p r) (B p r) j) ∧
      (∀ j,final.heads (twoRecoveryLocal p j)=0):=by
  have hb : 0 < oracleSizeBound p.degree
      (PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2):=by
    rw [native_width]
    exact bound_positive p r
  have hW := fits.workspace
  have hbytes:=fits.bytes
  have htwo:=fits.two
  rw [←native_source p r] at hW hbytes
  rw [←native_width p r,←native_queries p r] at hW
  have hW' : CloseoutRecoveryWorkspace.originalWorkspace
      (PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2)
      (oracleSizeBound p.degree (PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2))
      (PCPPNativeHierarchyNodes.queries (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2)).length ≤ W:=by
    simpa only [native_width,B] using hW
  rw [←native_width p r] at htwo
  obtain ⟨cost,hcost,final,trace,halt,flag,desc,queryBound,queryHead,scalars,word,wordHead,
      _capacity,_capacityHead,searchHeads⟩:=RecoveryBoundedCold.run (source p) p.k p.degree
        (hierarchy p).coefficient (pad p) (code p) r.2 ((hierarchy p).time r.1).bits W
        (pad_large p) hb hW' hbytes htwo
  refine ⟨cost,hcost,final,trace,halt,flag.trans ?_,searchHeads 369,queryBound,queryHead,?_,?_⟩
  · exact RecoveryBoundedCold.flag_hierarchy (source p) (hierarchy p) (pad p) (pad_large p) p.degree r
  · intro j
    fin_cases j
    · exact word
    · exact desc
    · have h:=(scalars 0).1
      change _=List.replicate
        (PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2) true at h
      exact h.trans (congrArg (fun z=>List.replicate z true) (native_width p r))
    · have h:=(scalars 2).1
      change _=List.replicate (oracleSizeBound p.degree
        (PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2)) true at h
      exact h.trans (congrArg (fun z=>List.replicate (oracleSizeBound p.degree z) true) (native_width p r))
  · intro j
    fin_cases j
    · exact wordHead
    · exact searchHeads 787
    · exact (scalars 0).2
    · exact (scalars 2).2

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
