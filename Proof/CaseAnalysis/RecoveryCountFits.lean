import Proof.CaseAnalysis.RecoveryCountGrammarEntryDock

/-! The already checked original grammar allocation and one Room pay
all scalar reset and row-packet input margins for a count iteration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCounts
open LocalBitMultitape BoundedOracleStructuralCircuit OuterPCPRecovery
open RecoveryBoundedGrammarCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem packet_inputs {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (count : Fin bound) (Q clauses : ℕ) (hQ : Q≤W) (hclauses : clauses≤W) :
    (∀ j,2*RecoveryBoundedRowPacketAppend.values C (boundedCircuitFieldLimit q bound) q count.val Q clauses j+4≤B) ∧
    2*(count.val+1)+4≤B ∧ 6+boundedCircuitFieldLimit q bound≤C := by
  have scalars:=alloc.scalars (⟨0,by omega⟩ : Fin (bound+1))
  have hF:=scalars.index 2
  change 0*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W at hF
  have hbound:=scalars.limit 5
  change bound+1≤W at hbound
  have hlimit : boundedCircuitFieldLimit q bound=q+bound+1:=rfl
  have hc:=count.isLt
  have hb:=room.packet
  have cap:=room.capacity
  refine ⟨?_,by omega,?_⟩
  · intro j
    fin_cases j <;> simp [RecoveryBoundedRowPacketAppend.values] <;> omega
  · nlinarith [Nat.zero_le (W^2)]

theorem reset_inputs {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W) :
    (bound+1)*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤B ∧
    bound+1≤B ∧ 6+boundedCircuitFieldLimit q bound+2≤B := by
  have sc:=(alloc.next_scalars (⟨bound,by omega⟩ : Fin (bound+1))).2.2
  have hindex:=sc.index 2
  change (bound+1)*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W at hindex
  have hbound:=sc.limit 5
  change bound+1≤W at hbound
  have hF:=(alloc.scalars (⟨0,by omega⟩ : Fin (bound+1))).index 2
  change 0*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W at hF
  have hb:=room.packet
  have hw:=room.wB
  exact ⟨hindex.trans hw,hbound.trans hw,by omega⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedCounts
