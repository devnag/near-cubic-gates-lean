import Proof.CaseAnalysis.RecoveryCaseQuery

/-! The actual unconstrained case query reuses the whole compact-query
machine, retaining the original payload for the subsequent canonical search.
The capacity driver and all prepared fields are explicit caller obligations. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open SourceInterfaces OuterPCPRecovery CanonicalSATSelfReduction
open BoundedOracleStructuralCircuit RecoveryScheduleEnvelope
open RecoveryChoice RecoveryQuery RecoveryFormulaPrefix RecoveryOracle
open RecoveryQueryKernel
open private query_halted from Proof.Amplification.RecoveryPrefixBody
open private query_start_initial from Proof.Amplification.RecoveryPrefixBodyReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem case_ready {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (degree : Nat) {n : Nat}
    (input : BitInput n) (cap log : Nat)
    (ambient : Fin 357→List Bool) (payloadPadding zeroPadding countPadding : List Bool)
    (hcap : capacity (payload (boundedOracleRecoveryFormula pcp input
      (oracleSizeBound degree (pcp.nativeWidth n)))) 0 0 ≤ cap)
    (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate log false) (hz : log ≤ cap+1)
    (hp : ambient 0=frame (payload (boundedOracleRecoveryFormula pcp input
      (oracleSizeBound degree (pcp.nativeWidth n)))).bits++payloadPadding)
    (ha : ambient 1=frame []++zeroPadding)
    (hn : ambient 2=frame []++countPadding) :
    ∃ cost ≤ 18*cap, ∃ out : Fin 357→List Bool,
      Ready correctedSat (RecoveryQueryStep.program true) cost ambient out ∧
      readTapeBit (out RecoveryQueryStep.answerSlot) 0=caseTwo pcp degree input ∧
      (∀ i : Fin 357, i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧
      Bounded cap out := by
  let value := payload (boundedOracleRecoveryFormula pcp input
    (oracleSizeBound degree (pcp.nativeWidth n)))
  obtain ⟨cost,hcost,out,hr,answer,keep,driver,logOut,bounded⟩ :=
    RecoveryQueryStep.step_trace cap log true value 0 0 ambient
      payloadPadding zeroPadding countPadding hcap hb hd hl hz hp ha hn
  have hstart : RecoveryQueryStep.start true ambient=
      initialConfiguration (RecoveryQueryStep.program true).base.machine ambient :=
    query_start_initial _ _ _
  rw [hstart] at hr
  refine ⟨cost,hcost,out,⟨RecoveryQueryStep.stopped true out,hr,?_,fun _=>rfl,rfl⟩,
    answer.trans (case_query pcp degree input),keep,driver,logOut,bounded⟩
  exact query_halted (kernel true) RecoveryQueryStep.answerSlot out

end NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
