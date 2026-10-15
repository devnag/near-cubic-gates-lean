import Proof.CaseAnalysis.RecoverySearchExecution
import Proof.CaseAnalysis.RecoveryCaseQuery

/-! The executed flag and descriptor have the original recovery meaning.
Canonical description order is supplied by the existing prefix theorem. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open SourceInterfaces OuterPCPRecovery CanonicalSATSelfReduction CanonicalRecoveryLanguage
open BoundedOracleStructuralCircuit RecoveryScheduleEnvelope RecoveryChoice RecoveryFormulaPrefix
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_search {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (degree : Nat) {n : Nat} (x : BitInput n)
    (small : SmallOracle pcp degree x) :
    RecoveryPrefixBody.search true
      (payload (boundedOracleRecoveryFormula pcp x (oracleSizeBound degree (pcp.nativeWidth n))))
      (oracleCount pcp degree n) []=
    canonicalBoundedCircuitDescription (oracleSizeBound degree (pcp.nativeWidth n))
      (oracleSelector pcp degree x small).circuit := by
  rw [RecoveryPrefixBody.search_canonical true _ _ _ (payload_decodes _)
    (boundedOracleRecoveryFormula_wellSized pcp x _) (oracle_range pcp degree x)]
  rw [oracle_prefix pcp degree x small (oracleCount pcp degree n)
    (show oracleCount pcp degree n ≤ descriptionWidth (pcp.nativeWidth n)
      (oracleSizeBound degree (pcp.nativeWidth n)) from Nat.le_refl _)]
  rw [List.take_of_length_le (by rw [List.length_ofFn];exact Nat.le_refl _)]
  exact listOfFn_canonicalDescriptionInput _ _

theorem oracle_ready {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (degree : Nat) {n : Nat} (x : BitInput n) (B : Nat) :
    let value:=payload (boundedOracleRecoveryFormula pcp x (oracleSizeBound degree (pcp.nativeWidth n)))
    let total:=oracleCount pcp degree n
    ∃ cost ≤ 1099511627776*(RecoveryPrefixCold.radius value total)^3,
      ∃ out : Fin 790→List Bool,
      Ready RecoveryOracle.correctedSat (program 1073741824) cost (input value total B) out ∧
      readTapeBit (out 369) 0=caseTwo pcp degree x ∧
      (∀ small : SmallOracle pcp degree x,
        out 787=frame (canonicalBoundedCircuitDescription (oracleSizeBound degree (pcp.nativeWidth n))
          (oracleSelector pcp degree x small).circuit)) ∧
      out 1=ZeroPadding.pad B (List.replicate total true) := by
  dsimp only
  obtain ⟨cost,hcost,out,hr,hflag,hdesc,hkeep⟩:=ready 1073741824
    (payload (boundedOracleRecoveryFormula pcp x (oracleSizeBound degree (pcp.nativeWidth n))))
    (oracleCount pcp degree n) B (Nat.le_refl _)
  refine ⟨cost,hcost.trans (RecoveryBoundedSearch.full_budget_bound _ _),out,hr,
    hflag.trans (CloseoutRecoveryCaseQuery.case_query pcp degree x),?_,hkeep⟩
  intro small
  rw [hdesc,canonical_search pcp degree x small]

end NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
