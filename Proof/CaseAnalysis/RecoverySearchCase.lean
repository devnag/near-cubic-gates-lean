import Proof.CaseAnalysis.RecoverySearchCaseClear

/-! One cold unconstrained SAT query, including actual request decoding,
workspace construction and query-port reset, from a single framed request. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchCase
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryPrefixCold RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coldPieces (C : Nat) : Fin 4→Piece 389
  | ⟨0,_⟩ => ordinary unwrap
  | ⟨1,_⟩ => ordinary (prepare C)
  | ⟨2,_⟩ => piece
  | ⟨3,_⟩ => ordinary clearMachine
  | ⟨n+4,h⟩ => False.elim (by omega)
def coldNext (C : Nat) (j : Fin 4) (_ : Fin (coldPieces C j).states)
    (_ : Fin 389→Bool) : Option (Fin 4) :=
  if h : j.val<3 then some ⟨j.val+1,by omega⟩ else none
noncomputable abbrev coldProgram (C : Nat) :=
  RecoveryPrefixCold.ports.program (graph (coldPieces C) 0 (coldNext C))
def coldBudget (C payload total : Nat) :=
  4*(RecoveryPrefixMeasure.request payload total).length+2+
  RecoveryPrefixColdPrepare.budget C payload total+
  20*RecoveryPrefixColdPrepare.capacity C payload total+8

theorem cold_ready (C payload total : Nat) (hC : 1073741824 ≤ C) :
    ∃ cost ≤ coldBudget C payload total,∃ out : Fin 389→List Bool,
      Ready correctedSat (coldProgram C) cost (input payload total) out ∧
      readTapeBit (out 357) 0=correctedSat (RecoveryQuery.code true payload 0 0) ∧
      out 0=frame (RecoveryPrefixMeasure.request payload total) ∧
      out 344=List.replicate (RecoveryPrefixColdPrepare.capacity C payload total) false := by
  obtain ⟨c0,hc0,h0⟩:=ordinary_ready (o:=correctedSat) RecoveryPrefixCold.ports unwrap _ _
    (unwrap_ready payload total)
  obtain ⟨prepared,hp,hprepared⟩:=prepare_ready C payload total hC
  have hrequest:=prepare_request C payload total prepared hp
  obtain ⟨c1,hc1,h1⟩:=ordinary_ready (o:=correctedSat) RecoveryPrefixCold.ports (prepare C) _ _ hp
  obtain ⟨c2,hc2,asked,h2,ha,h0keep,hd,hl,hquery⟩:=prepared_ready C payload total hC prepared hprepared
  have h3:=clear_ready (RecoveryPrefixColdPrepare.capacity C payload total) asked hquery hd hl
  obtain ⟨hout,hrequestKeep,hanswerKeep⟩:=cleared_fields
    (RecoveryPrefixColdPrepare.capacity C payload total) asked
  have hp0:=Ready.call RecoveryPrefixCold.ports (coldPieces C) 0 (coldNext C) 0 1 h0 (by intro q;rfl)
  have hp1:=Ready.call RecoveryPrefixCold.ports (coldPieces C) 0 (coldNext C) 1 2 h1 (by intro q;rfl)
  have hp2:=Ready.call RecoveryPrefixCold.ports (coldPieces C) 0 (coldNext C) 2 3 h2 (by intro q;rfl)
  have hp3:=Ready.stop RecoveryPrefixCold.ports (coldPieces C) 0 (coldNext C) 3 h3 (by intro q;rfl)
  have hwhole:=trans hp0 (trans hp1 (trans hp2 hp3))
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(coldPieces C j).states) 0)
      (initialConfiguration (coldPieces C 0).machine (input payload total))=
      initialConfiguration (coldProgram C).base.machine (input payload total) := rfl
  rw [hstart] at hwhole
  refine ⟨(c0+1)+((c1+1)+((c2+1)+(2*RecoveryPrefixColdPrepare.capacity C payload total+4+1))),
    ?_,_,?_,?_,hrequestKeep.trans (h0keep.trans hrequest),hout⟩
  · dsimp only [coldBudget]
    omega
  · refine ⟨_,hwhole,?_,fun _=>rfl,rfl⟩
    simp [coldProgram,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · rw [hanswerKeep]
    exact ha

end NearCubicWires.RepairSource.RecoveryBoundedSearchCase
