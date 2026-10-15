import Proof.CaseAnalysis.RecoveryTableOutputState

/-! Execute the complete literal original compileUniversalOutput, including
the table, its paid loop rewind, and the original first-field selection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
open LocalBitMultitape RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def wholeMachine:=Composition.machine RecoveryBoundedTable.machine machine
def budget (total W : ℕ):=RecoveryBoundedTable.budget total W+1+RecoveryBoundedSelectorReuse.resetBudget total W
def Fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W : ℕ) (ht : total ≤ bound) : Prop :=
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let table:=compileUniversalNodes b address total ht
  RecoveryBoundedTable.index n bound total 6+F ≤ W ∧
  table.final.nodes.length+total*(3*F+2)+3*F ≤ W ∧
  (compileUniversalOutput b address total ht).compiled.final.nodes.length ≤ W ∧ total ≤ W

theorem initial_config {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out addressTail : List Bool) :
    RecoveryBoundedTable.configuration 0 b address W D L out addressTail 0 (by omega) total 1=
      (⟨RecoveryBoundedTable.machine.start,bankHeads out,
        bankData 6 b.nodes.length (capacity W) D 0 (OuterPCPRecovery.boundedCircuitFieldLimit n bound) 0 L out
          (ZeroPadding.pad (capacity W) []) (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound) 0
          (List.ofFn address++addressTail) n total⟩ : Configuration 56 _) := by
  apply configuration_ext
  · rfl
  · rw [configuration_heads]
    change bankHeads (out++[])=bankHeads out
    rw [List.append_nil]
  · rw [configuration_tapes]
    have hi (start : ℕ) : RecoveryBoundedTable.index n bound 0 start=start := by
      simp only [RecoveryBoundedTable.index,Nat.zero_mul,Nat.zero_add]
    have hf : (compileUniversalNodes b address 0 (by omega)).final=b:=rfl
    have hn : RecoveryBoundedTable.native b address 0 (by omega)=[]:=rfl
    have hr : RecoveryBoundedTable.references b address 0 (by omega)=[]:=rfl
    simp only [hi,hf,hn,hr,List.append_nil,sourceWord,List.flatMap_nil]

theorem output_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out addressTail : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht) (hout : Fits b address total W ht)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom wholeMachine (budget total W)
      ⟨wholeMachine.start,bankHeads out,bankData 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 (List.ofFn address++addressTail) n total⟩=some r ∧
      r.steps ≤ budget total W ∧ r.final.heads=bankHeads result ∧
      r.final.tapes=bankData (RecoveryBoundedTable.index n bound total 6) compiled.compiled.output.val C D total F total L result
        (ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht)))
        (RecoveryBoundedTable.index n bound total (6+F)) (RecoveryBoundedTable.index n bound total 0)
        (List.ofFn address++addressTail) n total := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let table:=compileUniversalNodes b address total ht
  let row : Fin (bound+1):=⟨total,by omega⟩
  let selected:=compileFirstFieldSelect table.final row table.values
  let compiled:=compileUniversalOutput b address total ht
  let first:=RecoveryBoundedTable.index n bound total 6
  let second:=RecoveryBoundedTable.index n bound total (6+F)
  let tag:=RecoveryBoundedTable.index n bound total 0
  let tableWord:=out++RecoveryBoundedTable.native b address total ht
  let source:=ZeroPadding.pad C (sourceWord (RecoveryBoundedTable.references b address total ht))
  let tail:=List.replicate (C-(sourceWord (RecoveryBoundedTable.references b address total ht)).length) false
  let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  have hlen : table.values.length=total:=compileUniversalNodes_values_length b address total ht
  rcases hout with ⟨hi,hp,hg,hc⟩
  obtain ⟨p,pr,pf,ps⟩:=RecoveryBoundedTable.table_run b address total W D L out addressTail ht hfit hD hL
  rw [initial_config] at pr
  have hH : ∀ j,bankHeads tableWord (slots j)=RecoveryBoundedSelectorReuse.finalHeads tableWord j:=bank_head_slot tableWord
  have hA : ∀ j,bankData first table.final.nodes.length C D 0 F total L tableWord source second tag (List.ofFn address++addressTail) n total (slots j)=
      RecoveryBoundedSelectorReuse.finalData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row 6)
        table.final.nodes.length C D 0 F table.values.length L tableWord
        (sourceWord (table.values.map (fun w=>w.output.val))++tail) j := by
    intro j
    rw [hlen]
    exact bank_tape_slot first table.final.nodes.length C D 0 F total L tableWord source second tag (List.ofFn address++addressTail) n total j
  obtain ⟨q,qr,qs,qh,qt⟩:=selector_run table.final row W D L table.values tableWord tail
    (bankHeads tableWord) (bankData first table.final.nodes.length C D 0 F total L tableWord source second tag (List.ofFn address++addressTail) n total)
    hH hA hi (by rw [hlen];exact hp) hg (by rw [hlen];exact hc) hD hL
  rw [hlen] at qr qs qt
  have qr' : runFrom machine (RecoveryBoundedSelectorReuse.resetBudget total W) (restart p.final machine.start)=some q := by
    change runFrom machine _ ⟨machine.start,p.final.heads,p.final.tapes⟩=some q
    rw [pf,configuration_heads,configuration_tapes]
    exact qr
  have full:=Composition.run_join RecoveryBoundedTable.machine machine _ _ _ p q pr qr'
  have hw : tableWord++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native=result := by
    change (out++RecoveryBoundedTable.native b address total ht)++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    rw [original_native]
    exact List.append_assoc _ _ _
  change q.final.heads=outputHeads (bankHeads tableWord) (tableWord++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native) at qh
  change q.final.tapes=output
    (bankData first table.final.nodes.length C D 0 F total L tableWord source second tag (List.ofFn address++addressTail) n total)
    selected.output.val total C (tableWord++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native) at qt
  rw [hw,bank_output_heads] at qh
  rw [hw,bank_output_tapes] at qt
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ budget total W
  unfold budget
  omega

theorem budget_quintic (total W : ℕ) (ht : total ≤ W) : budget total W ≤ 5000000000*(W+1)^5 := by
  have hs:=RecoveryBoundedSelectorFinish.reset_budget_quartic total W ht
  change RecoveryBoundedSelectorReuse.resetBudget total W ≤ 536871202*(W+1)^4 at hs
  have hm:=Nat.mul_le_mul_right (RecoveryBoundedTableNode.budget W+2) ht
  unfold budget RecoveryBoundedTable.budget RecoveryBoundedTableNode.budget
  unfold RecoveryBoundedTableNode.budget at hm
  nlinarith [Nat.zero_le (W^5),Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
