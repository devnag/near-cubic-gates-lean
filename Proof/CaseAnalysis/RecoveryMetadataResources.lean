import Proof.CaseAnalysis.RecoveryMetadataRun
import Proof.CaseAnalysis.RecoveryGrammarAllocationFits

/-! The existing original-graph workspace pays for every cold scalar
operation. No derived-field or arithmetic-fit premise remains at this entry. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
open LocalBitMultitape RecoveryRootRound RecoveryBoundedGrammarAdvance
open RecoveryBoundedGrammarScalarAdd (unary)
open RecoveryBoundedGrammarCold (Allocation Room numbers)
open CloseoutRecoveryWorkspace CloseoutRecoveryGrammarResources
open BoundedOracleStructuralCircuit OuterPCPRecovery PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem allocated_ready (q bound G W C D L S B P Q clauses : ℕ)
    (ha : Allocation q bound G W) (hr : Room W C D L S B P) :
    ClockJoin.ReadyRun machine (budget B) (input q bound C Q clauses B) (output q bound C Q clauses B) := by
  have hf : G+3*(q+bound+1) ≤ W := ha.field
  have hp := hr.packet
  exact ready q bound C Q clauses B (by omega)

theorem output_support (q bound C Q clauses B : ℕ)
    (hB : 2*(q+bound+1)+8 ≤ B) (hC : C ≤ B) (hQ : Q ≤ B) (hc : clauses ≤ B)
    (i : Fin 37) : (output q bound C Q clauses B i).length ≤ B+1 := by
  have hu (n : ℕ) (hn : n ≤ B) : (unary B n).length ≤ B+1 := by
    simp only [unary,ZeroPadding.pad_length,List.length_replicate]
    omega
  refine Fin.addCases (m:=33) (n:=4) (motive:=fun i =>
    (output q bound C Q clauses B i).length ≤ B+1) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    all_goals
      first
      | apply hu; assumption
      | apply hu; omega
      | (change (unary B _).length ≤ B+1
         apply hu
         dsimp [numbers,extra,extraValues,rowWidth,boundedCircuitFieldLimit]
         omega)
  · fin_cases j <;>
      dsimp [output,bank,Fin.addCases] <;> simp only [List.length_replicate] <;> omega

theorem original_ready (q bound Q clauses S : ℕ) (hS : 1 ≤ S) :
    let W := originalWorkspace q bound Q clauses
    let B := backing W S
    let C := 16384*(W+1)^2
    ClockJoin.ReadyRun machine (budget B) (input q bound C Q clauses B) (output q bound C Q clauses B) ∧
      ∀ i,(output q bound C Q clauses B i).length ≤ B+1 := by
  let G := R1Leaf56StructuralGateBudgetEnvelope.structuralGateEnvelope q bound Q clauses+Q+clauses
  let W := originalWorkspace q bound Q clauses
  have ha : Allocation q bound G W := allocation q bound G
  have hr := room W S hS
  have hf : G+3*(q+bound+1) ≤ W := ha.field
  have hQ : Q ≤ W := by dsimp [W,originalWorkspace,workspace]; omega
  have hc : clauses ≤ W := by dsimp [W,originalWorkspace,workspace]; omega
  have hp := hr.packet
  refine ⟨allocated_ready q bound G W _ _ _ S _ _ Q clauses ha hr,?_⟩
  intro i
  exact output_support q bound _ Q clauses _ (by omega) ((Nat.le_add_right _ 1).trans hr.cB)
    (hQ.trans hr.wB) (hc.trans hr.wB) i

theorem budget_polynomial {backingSize : ℕ → ℕ} (hB : SourcePoly backingSize) :
    SourcePoly (fun n => budget (backingSize n)) :=
  (hB.add (polyDominated_const 2)).const_mul 512

theorem source_bound {width bound queries clauses support : ℕ → ℕ}
    (hw : SourcePoly width) (hb : SourcePoly bound)
    (hq : SourcePoly queries) (hc : SourcePoly clauses)
    (htwo : SourcePoly (fun n => 2^width n)) (hs : SourcePoly support) :
    ∃ coefficient degree : ℕ,1 ≤ coefficient ∧ ∀ n,
      let W := originalWorkspace (width n) (bound n) (queries n) (clauses n)
      let B := backing W (support n)
      budget B+37*(B+1) ≤ coefficient*(n+1)^degree := by
  have hW := CloseoutRecoveryWorkspacePolynomial.original_workspace hw hb hq hc htwo
  have hB := backing_polynomial hW hs
  have ht := (budget_polynomial hB).add ((hB.add (polyDominated_const 1)).const_mul 37)
  obtain ⟨degree,coefficient,hbound⟩ := ht
  refine ⟨coefficient+1,degree,by omega,fun n => ?_⟩
  exact (hbound n).trans (Nat.mul_le_mul_right _ (by omega))

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdMetadata
