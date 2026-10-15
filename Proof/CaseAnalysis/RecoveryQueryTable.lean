import Proof.CaseAnalysis.RecoveryTableOutputPadded

/-! The query address loader uses the existing explicit trailing sentinel.
One extra zero on the retained width tape commutes with the whole table run. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryTable
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
open RecoveryBoundedTableOutput (bankHeads bankData)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverCaps (n : ℕ) (i : Fin 56):=if i=50 then n+2 else 0
def data (n C : ℕ) (A : Fin 56→List Bool):=
  Function.update (RecoveryBoundedTableOutput.paddedData C A) 50 (UnaryTemplate.tape n)
theorem width_tape (n : ℕ) : ZeroPadding.pad (n+2) (CompareMachine.word n)=UnaryTemplate.tape n := by
  simp only [ZeroPadding.pad,CompareMachine.word,List.length_cons,List.length_replicate]
  rw [show n+2-(n+1)=1 by omega]
  rfl
theorem driver_pad (n C : ℕ) (A : Fin 56→List Bool) (h50 : A 50=CompareMachine.word n) :
    (fun i=>ZeroPadding.pad (driverCaps n i) (RecoveryBoundedTableOutput.paddedData C A i))=data n C A := by
  funext i
  by_cases hi : i=50
  · subst i
    change ZeroPadding.pad (n+2) (RecoveryBoundedTableOutput.paddedData C A 50)=UnaryTemplate.tape n
    rw [RecoveryBoundedTableOutput.unchanged C A 50 (by decide),h50,width_tape]
  · simp only [driverCaps,if_neg hi,ZeroPadding.pad_zero,data,Function.update_of_ne hi]

theorem table_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht)
    (hout : RecoveryBoundedTableOutput.Fits b address total W ht)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom RecoveryBoundedTableOutput.wholeMachine (RecoveryBoundedTableOutput.budget total W)
      ⟨RecoveryBoundedTableOutput.wholeMachine.start,bankHeads out,data n C (bankData 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 (List.ofFn address) n total)⟩=some r ∧
      r.steps ≤ RecoveryBoundedTableOutput.budget total W ∧ r.final.heads=bankHeads result ∧
      r.final.tapes=data n C (bankData (RecoveryBoundedTable.index n bound total 6) compiled.compiled.output.val C D total F total L result
        (ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht)))
        (RecoveryBoundedTable.index n bound total (6+F)) (RecoveryBoundedTable.index n bound total 0)
        (List.ofFn address) n total) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTableOutput.padded_run b address total W D L out ht hfit hout hD hL
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config RecoveryBoundedTableOutput.wholeMachine (driverCaps n) _ _ p pr
  change runFrom _ _ ⟨_,bankHeads out,fun i=>ZeroPadding.pad (driverCaps n i)
    (RecoveryBoundedTableOutput.paddedData (capacity W) _ i)⟩=some r at hr
  rw [driver_pad n (capacity W) _ (by rfl)] at hr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (driverCaps n i) (p.final.tapes i))=_
    rw [pt,driver_pad n (capacity W) _ (by rfl)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryTable
