import Proof.CaseAnalysis.RecoveryPreparedRun

/-! The same original graph allocation and paid room discharge every cold
initialization fit, including the actual unary product's rewind log. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape BoundedOracleStructuralCircuit OuterPCPRecovery
open RecoveryBoundedGrammarCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fits {q bound G W C D L S B P Q clauses : ℕ}
    (ha : Allocation q bound G W) (hr : Room W C D L S B P)
    (hQ : Q≤W) (hc : clauses≤W) :
    (∀ j,RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j≤B) ∧
      2*(q+bound+1)+8≤B ∧ bound+3≤B ∧ rowWidth q bound*(2*(bound+1)+3)+2≤B := by
  have hf : G+3*(q+bound+1)≤W:=ha.field
  have hp:=hr.packet
  have hC:=hr.cB
  have hW:=hr.wB
  have hw : rowWidth q bound≤W := by
    simpa only [RecoveryBoundedNativeUnaryLoop.firstIndex,Fin.val_zero,Nat.zero_mul,Nat.zero_add] using
      ha.index (0 : Fin (bound+1)) 0 (Nat.zero_le _)
  have hd : rowWidth q bound*(bound+1)≤W := by
    have h:=ha.index (⟨bound,Nat.lt_succ_self bound⟩ : Fin (bound+1)) 0 (Nat.zero_le _)
    change bound*rowWidth q bound+0+rowWidth q bound≤W at h
    calc
      _=bound*rowWidth q bound+0+rowWidth q bound := by ring
      _≤W:=h
  refine ⟨?_,by omega,by omega,?_⟩
  · intro j
    fin_cases j <;> simp [RecoveryBoundedColdScalarMetadata.values] <;> omega
  · have he : rowWidth q bound*(2*(bound+1)+3)+2=
        2*(rowWidth q bound*(bound+1))+3*rowWidth q bound+2 := by ring
    rw [he]
    omega

theorem allocated_run {q bound G W C D L S B P Q clauses : ℕ}
    (ha : Allocation q bound G W) (hr : Room W C D L S B P)
    (hQ : Q≤W) (hc : clauses≤W) (proj : Fin 37→List Bool) (source : List Bool) :
    ∃ r,run machine (budget B) (input q bound C Q clauses B proj source)=some r ∧
      r.steps≤budget B ∧ r.final.heads=RecoveryBoundedColdPosition.positioned (fun _=>0) ∧
      r.final.tapes=preparedData q bound C Q clauses B proj source := by
  obtain ⟨a,b,c,d⟩:=fits ha hr hQ hc
  exact prepared_run q bound C Q clauses B proj source a b c d

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
