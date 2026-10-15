import Proof.CaseAnalysis.RecoveryGrammarReselect

/-! The same accepted workspace covers the next physical row, including
the terminal row cursor bound+1 after the final padding row. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open BoundedOracleStructuralCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Allocation.next_scalars {q bound G W : ℕ} (alloc : Allocation q bound G W) (row : Fin (bound+1)) :
    (row.val+1)*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W ∧
    row.val+1≤W ∧ ScalarFits q bound (row.val+1) W := by
  have sc:=alloc.scalars row
  have index:=alloc.index row (rowWidth q bound) le_rfl
  unfold RecoveryBoundedNativeUnaryLoop.firstIndex at index
  have field : 6+boundedCircuitFieldLimit q bound≤rowWidth q bound:=by unfold rowWidth;omega
  have nextIndex : (row.val+1)*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have rowBound : row.val+1≤W := by
    have hl:=sc.limit 5
    have hr:=row.isLt
    change bound+1≤W at hl
    omega
  refine ⟨nextIndex,rowBound,⟨?_,sc.limit,?_,sc.value⟩⟩
  · intro j
    fin_cases j
    · change (row.val+1)*rowWidth q bound≤W;omega
    · change (row.val+1)*rowWidth q bound+6≤W;omega
    · exact nextIndex
    · exact Nat.zero_le _
  · intro j
    fin_cases j
    · exact Nat.zero_le _
    · exact sc.upper 1
    · exact rowBound

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
