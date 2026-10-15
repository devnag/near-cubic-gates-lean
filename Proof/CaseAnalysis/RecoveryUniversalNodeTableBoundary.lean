import Proof.CaseAnalysis.RecoveryTableIndexAdvance

/-! The literal node's final bank exposes exactly the original table's
reference and row-index consumers. Keep all capacities and fields symbolic. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeTableBoundary
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedUniversalNodeBank
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finished (first node C D F total L : ℕ) (result source : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ) (i : Fin 55):=
  if i=1 ∨ i=41 then ZeroPadding.pad C (List.replicate tag true)
  else data first node C D 5 F total L result source second tag left right constant address count
    (RecoveryBoundedTagPacket.word constant current) i

theorem tag_output (first node C D value F total L : ℕ) (out result source : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ) :
    RecoveryBoundedNodeTagSelect.output
      (prepared (data first current C D value F total L out source second tag left right constant address count [])
        constant current tag C) node C result=
      finished first node C D F total L result source second tag left right constant current address count := by
  funext i
  fin_cases i <;> rfl

theorem reference_heads (out : List Bool) (j : Fin 9) :
    heads out (RecoveryBoundedTableReferenceBank.slots j)=RecoveryBoundedTableReferenceReset.finalHeads j := by
  fin_cases j <;> rfl
theorem reference_tapes (refs : List ℕ) (first node C D F L : ℕ) (result : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ) (j : Fin 9) :
    finished first node C D F refs.length L result (ZeroPadding.pad C (sourceWord refs))
      second tag left right constant current address count (RecoveryBoundedTableReferenceBank.slots j)=
      RecoveryBoundedTableReferenceBank.input refs node C D j := by
  fin_cases j <;> rfl

theorem index_heads (out : List Bool) (six : Bool) (j : Fin 5) :
    heads out (RecoveryBoundedTableIndexBank.slots six j)=RecoveryBoundedTableIndexBank.heads j := by
  cases six <;> fin_cases j <;> rfl
theorem index_tapes (refs : List ℕ) (first node C D F L : ℕ) (result : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ) (six : Bool) (j : Fin 5) :
    RecoveryBoundedTableReferenceBank.output
      (finished first node C D F refs.length L result (ZeroPadding.pad C (sourceWord refs))
        second tag left right constant current address count) refs node C (RecoveryBoundedTableIndexBank.slots six j)=
      RecoveryBoundedTableIndexBank.input first second tag C (if six then 6 else F) j := by
  cases six <;> fin_cases j <;> rfl

theorem original_next {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (wires : List (LiveWire b)) :
    (compileUniversalNode b row address wires).compiled.output.val+1=
      (compileUniversalNode b row address wires).compiled.final.nodes.length := by
  let seven:=RecoveryBoundedUniversalNode.cases b row address wires
  have hblock : 0+6 ≤ rowWidth n bound := by simp only [rowWidth];omega
  have hn:=RecoveryBoundedSelectorReuse.output_next seven.final row 0 6 hblock seven.values
  change (compileFieldSelect seven.final tagEqualsExpr row seven.values).output.val+1=
    (compileFieldSelect seven.final tagEqualsExpr row seven.values).final.nodes.length at hn
  have meaning:=RecoveryBoundedUniversalNode.original_node b row address wires
  rw [←meaning.2.1,←meaning.1] at hn
  exact hn

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeTableBoundary
