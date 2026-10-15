import Proof.CaseAnalysis.RecoveryGrammarChildrenRun

/-! The original graph bound supplies all temporary grammar positions.
These are exactly the unary/less workers' existing allocation premises. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape BoundedOracleStructuralCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Allocation (q bound G W : ℕ) : Prop where
  graph : G≤W
  tag : G+18≤W
  field : G+3*boundedCircuitFieldLimit q bound≤W
  less : G+boundedCircuitFieldLimit q bound*(3*boundedCircuitFieldLimit q bound+1)+
    3*boundedCircuitFieldLimit q bound≤W
  index : ∀ (row : Fin (bound+1)) start,start≤rowWidth q bound →
    RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+rowWidth q bound≤W

theorem Allocation.scalars {q bound G W : ℕ} (h : Allocation q bound G W) (row : Fin (bound+1)) :
    ScalarFits q bound row.val W := by
  have ht:=h.tag
  have hf:=h.field
  have hh : boundedCircuitFieldLimit q bound=q+bound+1:=rfl
  rw [hh] at hf
  constructor
  · intro j
    have h0:=h.index row 0 (Nat.zero_le _)
    have h1:=h.index row 6 (by unfold rowWidth;omega)
    have h2:=h.index row (6+boundedCircuitFieldLimit q bound) (by unfold rowWidth;omega)
    unfold RecoveryBoundedNativeUnaryLoop.firstIndex at h0 h1 h2
    fin_cases j <;> simp [rowIndex] <;> omega
  · intro j
    fin_cases j <;> simp [rowLimit,boundedCircuitFieldLimit] <;> omega
  · intro j
    have hr:=row.isLt
    fin_cases j <;> simp [rowUpper] <;> omega
  · omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
