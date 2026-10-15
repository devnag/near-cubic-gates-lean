import Proof.CaseAnalysis.RecoveryTableOutputRun

/-! Five changing raw table fields need backing before the enclosing query
loop may erase and reuse them. Padding commutes with the accepted whole run. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 56):=if i=42∨i=44∨i=46∨i=49∨i=52 then C else 0
def paddedData (C : ℕ) (A : Fin 56→List Bool) (i : Fin 56):=ZeroPadding.pad (caps C i) (A i)
def reusableSlots : Fin 5→Fin 56:=![42,44,46,49,52]
theorem reusable_tapes (index base C D value F prior L : ℕ) (out source : List Bool)
    (second tag : ℕ) (address : List Bool) (count driver : ℕ) (j : Fin 5) :
    paddedData C (bankData index base C D value F prior L out source second tag address count driver) (reusableSlots j)=
      ZeroPadding.pad C (![CompareMachine.word prior,List.replicate second true,List.replicate index true,address,List.replicate tag true] j) := by
  fin_cases j <;> rfl

theorem unchanged (C : ℕ) (A : Fin 56→List Bool) (i : Fin 56)
    (hi : ¬(i=42∨i=44∨i=46∨i=49∨i=52)) : paddedData C A i=A i := by
  rw [paddedData,caps,if_neg hi,ZeroPadding.pad_zero]

theorem padded_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht) (hout : Fits b address total W ht)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom wholeMachine (budget total W)
      ⟨wholeMachine.start,bankHeads out,paddedData C (bankData 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 (List.ofFn address) n total)⟩=some r ∧
      r.steps ≤ budget total W ∧ r.final.heads=bankHeads result ∧
      r.final.tapes=paddedData C (bankData (RecoveryBoundedTable.index n bound total 6) compiled.compiled.output.val C D total F total L result
        (ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht)))
        (RecoveryBoundedTable.index n bound total (6+F)) (RecoveryBoundedTable.index n bound total 0)
        (List.ofFn address) n total) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=output_run b address total W D L out [] ht hfit hout hD hL
  simp only [List.append_nil] at pr pt
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config wholeMachine (caps (capacity W)) _ _ p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    exact ph
  · rw [rf]
    change paddedData (capacity W) p.final.tapes=_
    rw [pt]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
