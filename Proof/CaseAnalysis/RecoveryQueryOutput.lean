import Proof.CaseAnalysis.RecoveryQueryBank

/-! Physically load one projected address, then execute its complete original
table and output expression without disturbing the outer query streams. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
open LocalBitMultitape RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def table:=TapeEmbedding.machine 4 RecoveryBoundedTableOutput.wholeMachine
noncomputable def loadTable:=Composition.machine RecoveryBoundedQueryLoad.machine table
def loadTableBudget (n total W : ℕ):=CompetitorSameBucketRecordCopy.budget n+1+RecoveryBoundedTableOutput.budget total W

theorem table_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L pos : ℕ) (out source refs : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht)
    (hout : RecoveryBoundedTableOutput.Fits b address total W ht)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom table (RecoveryBoundedTableOutput.budget total W)
      ⟨table.start,heads out pos refs,data 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 (List.ofFn address) n total source refs⟩=some r ∧
      r.steps ≤ RecoveryBoundedTableOutput.budget total W ∧ r.final.heads=heads result pos refs ∧
      r.final.tapes=data (RecoveryBoundedTable.index n bound total 6) compiled.compiled.output.val C D total F total L result
        (ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht)))
        (RecoveryBoundedTable.index n bound total (6+F)) (RecoveryBoundedTable.index n bound total 0)
        (List.ofFn address) n total source refs := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedQueryTable.table_run b address total W D L out ht hfit hout hD hL
  rw [←blockData_eq] at pr pt
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let r:=TapeEmbedding.receipt (extraHeads pos refs) (extraData F source refs) p
  have hr:=TapeEmbedding.run_embed RecoveryBoundedTableOutput.wholeMachine (extraHeads pos refs) (extraData F source refs) _ _ p pr
  refine ⟨r,hr,ps,?_,?_⟩
  · change Fin.addCases (m:=56) (n:=4) (motive:=fun _=>ℕ) p.final.heads (extraHeads pos refs)=_
    rw [ph]
    rfl
  · change Fin.addCases (m:=56) (n:=4) (motive:=fun _=>List Bool) p.final.tapes (extraData F source refs)=_
    rw [pt]
    rfl

theorem load_table_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out pre tail refs : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht)
    (hout : RecoveryBoundedTableOutput.Fits b address total W ht) (hn : n ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let source:=pre++List.ofFn address++tail
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom loadTable (loadTableBudget n total W)
      ⟨loadTable.start,heads out pre.length refs,data 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 [] n total source refs⟩=some r ∧
      r.steps ≤ loadTableBudget n total W ∧ r.final.heads=heads result (pre.length+n) refs ∧
      r.final.tapes=data (RecoveryBoundedTable.index n bound total 6) compiled.compiled.output.val C D total F total L result
        (ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht)))
        (RecoveryBoundedTable.index n bound total (6+F)) (RecoveryBoundedTable.index n bound total 0)
        (List.ofFn address) n total source refs := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let source:=pre++List.ofFn address++tail
  have hC : 2*(List.ofFn address).length+4 ≤ C := by
    rw [List.length_ofFn]
    dsimp [C,capacity]
    nlinarith [Nat.zero_le (W^2)]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedQueryLoad.load_run (heads out pre.length refs)
    (data 6 b.nodes.length C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] (List.ofFn address).length total source refs)
    C pre (List.ofFn address) tail (load_heads out pre refs)
    (load_tapes b.nodes.length C D F total L out pre (List.ofFn address) tail refs) hC
  rw [loaded_heads] at ph
  rw [loaded_tapes] at pt
  simp only [List.length_ofFn] at pr ps ph pt
  obtain ⟨q,qr,qs,qh,qt⟩:=table_run b address total W D L (pre.length+n) out source refs ht hfit hout hD hL
  have qr' : runFrom table (RecoveryBoundedTableOutput.budget total W) (restart p.final table.start)=some q := by
    change runFrom table _ ⟨table.start,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join RecoveryBoundedQueryLoad.machine table _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ loadTableBudget n total W
  unfold loadTableBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
