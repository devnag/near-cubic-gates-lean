import Proof.CaseAnalysis.RecoveryRowFits
import Proof.Circuits.BalancedAtomCodeLedger

/-! The original graph envelope and physical workspace stay polynomial in
the actual source length. This applies only the existing arithmetic ledger;
it imports no symbolic-machine simulation as an ordinary run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspacePolynomial
open PaddedRunnerBudgetClosure R1Leaf56BalancedAtomCodeLedger
open BoundedOracleStructuralCircuit CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_workspace
    {width bound queries clauses : ℕ → ℕ}
    (hw : SourcePoly width) (hb : SourcePoly bound)
    (hq : SourcePoly queries) (hc : SourcePoly clauses)
    (htwo : SourcePoly (fun n => 2^width n)) :
    SourcePoly (fun n => originalWorkspace (width n) (bound n) (queries n) (clauses n)) := by
  have hg := ((sourcePoly_structuralGateEnvelope hw hb hq hc htwo).add hq).add hc
  have hf := (hw.add hb).add (polyDominated_const 1)
  exact hg.add ((sourcePoly_pow hf 2).const_mul 256)

theorem row_workspace {support width : ℕ → ℕ}
    (hs : SourcePoly support) (hw : SourcePoly width) :
    SourcePoly (fun n => 32*support n+10000000000*(width n+1)^6+64) :=
  ((hs.const_mul 32).add
    ((sourcePoly_pow (hw.add (polyDominated_const 1)) 6).const_mul 10000000000)).add
      (polyDominated_const 64)

/-- These are the actual shared C/D/L reservations, with their charged size.
No numerical value or degree is chosen before the complete source bounds. -/
theorem shared_reservations {width : ℕ → ℕ} (hw : SourcePoly width) :
    SourcePoly (fun n =>
      16384*(width n+1)^2+8388608*(width n+1)^3+268435600*(width n+1)^4) := by
  have h := hw.add (polyDominated_const 1)
  exact (((sourcePoly_pow h 2).const_mul 16384).add
    ((sourcePoly_pow h 3).const_mul 8388608)).add
      ((sourcePoly_pow h 4).const_mul 268435600)

theorem original_bound
    {width bound queries clauses support : ℕ → ℕ}
    (hw : SourcePoly width) (hb : SourcePoly bound)
    (hq : SourcePoly queries) (hc : SourcePoly clauses)
    (htwo : SourcePoly (fun n => 2^width n)) (hs : SourcePoly support) :
    ∃ coefficient degree : ℕ, 1 ≤ coefficient ∧ ∀ n,
      let W := originalWorkspace (width n) (bound n) (queries n) (clauses n)
      descriptionWidth (width n) (bound n)+
        (32*support n+10000000000*(W+1)^6+64)+
        (16384*(W+1)^2+8388608*(W+1)^3+268435600*(W+1)^4) ≤
          coefficient*(n+1)^degree := by
  have hW := original_workspace hw hb hq hc htwo
  have h := ((sourcePoly_descriptionWidth hw hb).add (row_workspace hs hW)).add
    (shared_reservations hW)
  obtain ⟨degree,coefficient,hbound⟩ := h
  refine ⟨coefficient+1,degree,by omega,fun n => ?_⟩
  exact (hbound n).trans (Nat.mul_le_mul_right _ (by omega))

end NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspacePolynomial
