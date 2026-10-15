import Proof.CaseAnalysis.RecoveryQueryRestore

/-! One complete original projected-query iteration: load the actual address,
compile its whole table/output, append the live reference and restore all
working fields. All physical stream cursors are retained for the next query. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
open LocalBitMultitape RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem append_heads (out refs : List Bool) (pos : ℕ) (j : Fin 7) :
    heads out pos refs (RecoveryBoundedQueryAppend.slots j)=RecoveryBoundedTagReferenceAppend.heads refs j := by
  fin_cases j <;> rfl
theorem append_tapes (index node C D value F prior L : ℕ) (out priorRefs : List Bool)
    (second tag : ℕ) (address : List Bool) (n total : ℕ) (source refs : List Bool) (j : Fin 7) :
    data index node C D value F prior L out priorRefs second tag address n total source refs (RecoveryBoundedQueryAppend.slots j)=
      RecoveryBoundedQueryAppend.input node C refs j := by
  fin_cases j <;> rfl
theorem appended_heads (out refs next : List Bool) (pos : ℕ) :
    RecoveryBoundedQueryAppend.heads (heads out pos refs) next=heads out pos next := by
  funext i
  fin_cases i <;> rfl
theorem appended_tapes (index node C D value F prior L : ℕ) (out priorRefs : List Bool)
    (second tag : ℕ) (address : List Bool) (n total : ℕ) (source refs next : List Bool) :
    RecoveryBoundedQueryAppend.output
      (data index node C D value F prior L out priorRefs second tag address n total source refs) next=
      data index node C D value F prior L out priorRefs second tag address n total source next := by
  funext i
  fin_cases i <;> rfl

theorem output_next {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total : ℕ) (ht : total ≤ bound) :
    (compileUniversalOutput b address total ht).compiled.output.val+1=
      (compileUniversalOutput b address total ht).compiled.final.nodes.length := by
  exact RecoveryBoundedSelectorReuse.output_next (compileUniversalNodes b address total ht).final
    ⟨total,by omega⟩ 6 (OuterPCPRecovery.boundedCircuitFieldLimit n bound) (by simp [rowWidth];omega)
    (compileUniversalNodes b address total ht).values

noncomputable def appended:=Composition.machine loadTable RecoveryBoundedQueryAppend.machine
noncomputable def machine:=Composition.machine appended RecoveryBoundedQueryRestore.machine
def budget (W : ℕ):=6000000000*(W+1)^5

theorem body_budget (n total node F W : ℕ) (hn : n ≤ W) (ht : total ≤ W) (hg : node ≤ W) (hF : F ≤ W) :
    loadTableBudget n total W+1+RecoveryBoundedTagReferenceAppend.budget node (capacity W)+1+
      RecoveryBoundedQueryRestore.budget node F (capacity W) ≤ budget W := by
  have h:=RecoveryBoundedTableOutput.budget_quintic total W ht
  unfold loadTableBudget CompetitorSameBucketRecordCopy.budget RecoveryBoundedTagReferenceAppend.budget
    RecoveryBoundedQueryRestore.budget capacity budget
  nlinarith [Nat.zero_le (W^5),Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2)]

theorem query_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out pre tail refs : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht)
    (hout : RecoveryBoundedTableOutput.Fits b address total W ht) (hn : n ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let source:=pre++List.ofFn address++tail
    let compiled:=compileUniversalOutput b address total ht
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let nextRefs:=refs++frame (List.replicate compiled.compiled.output.val true)
    ∃ r,runFrom machine (budget W)
      ⟨machine.start,heads out pre.length refs,data 6 b.nodes.length C D 0 F 0 L out
        (ZeroPadding.pad C []) (6+F) 0 [] n total source refs⟩=some r ∧
      r.steps ≤ budget W ∧ r.final.heads=heads result (pre.length+n) nextRefs ∧
      r.final.tapes=data 6 compiled.compiled.final.nodes.length C D 0 F 0 L result
        (ZeroPadding.pad C []) (6+F) 0 [] n total source nextRefs := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let source:=pre++List.ofFn address++tail
  let compiled:=compileUniversalOutput b address total ht
  let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let nextRefs:=refs++frame (List.replicate compiled.compiled.output.val true)
  let table:=compileUniversalNodes b address total ht
  let prior:=RecoveryBoundedTable.references b address total ht
  let first:=RecoveryBoundedTable.index n bound total 6
  let second:=RecoveryBoundedTable.index n bound total (6+F)
  let tag:=RecoveryBoundedTable.index n bound total 0
  let A:=data first compiled.compiled.output.val C D total F total L result (ZeroPadding.pad C (sourceWord prior))
    second tag (List.ofFn address) n total source refs
  have hOut:=hout
  rcases hOut with ⟨hi,hp,hg,hc⟩
  change first+F ≤ W at hi
  change table.final.nodes.length+total*(3*F+2)+3*F ≤ W at hp
  change compiled.compiled.final.nodes.length ≤ W at hg
  have hnode : compiled.compiled.output.val ≤ W:=compiled.compiled.output.isLt.le.trans hg
  have hfirst : first ≤ W:=by omega
  have hsecond : second ≤ W := by
    have h : second=first+F:=by dsimp [second,first,RecoveryBoundedTable.index];omega
    rw [h]
    exact hi
  have htag : tag ≤ W := by
    have h : tag ≤ first:=by dsimp [tag,first,RecoveryBoundedTable.index];omega
    omega
  have hinit : 6+F ≤ W := by
    have h : 6 ≤ first:=by dsimp [first,RecoveryBoundedTable.index];omega
    omega
  have hlen : prior.length=total:=RecoveryBoundedTable.references_length b address total ht
  have hrefs : ∀ r∈prior,r≤W := by
    intro r hm
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hm
    exact w.output.isLt.le.trans (by change table.final.nodes.length ≤ W;omega)
  obtain ⟨p,pr,ps,ph,pt⟩:=load_table_run b address total W D L out pre tail refs ht hfit hout hn hD hL
  have hC : 2*compiled.compiled.output.val+1 ≤ C := by
    dsimp [C,capacity]
    nlinarith [Nat.zero_le (W^2)]
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedQueryAppend.append_run (heads result (pre.length+n) refs) A
    compiled.compiled.output.val C refs (append_heads result refs (pre.length+n))
    (append_tapes first compiled.compiled.output.val C D total F total L result
      (ZeroPadding.pad C (sourceWord prior)) second tag (List.ofFn address) n total source refs) hC
  rw [appended_heads] at qh
  rw [appended_tapes] at qt
  have qr' : runFrom RecoveryBoundedQueryAppend.machine (RecoveryBoundedTagReferenceAppend.budget compiled.compiled.output.val C)
      (restart p.final RecoveryBoundedQueryAppend.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have pq:=Composition.run_join loadTable RecoveryBoundedQueryAppend.machine _ _ _ p q pr qr'
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedQueryRestore.restore_run prior first compiled.compiled.output.val W D F L (pre.length+n)
    result second tag (List.ofFn address) n total source nextRefs hfirst hsecond htag hnode hinit
    (by rw [List.length_ofFn];exact hn) (by rw [hlen];exact hc) hrefs
  rw [hlen] at sr
  have sr' : runFrom RecoveryBoundedQueryRestore.machine (RecoveryBoundedQueryRestore.budget compiled.compiled.output.val F C)
      (restart (joinedReceipt p q).final RecoveryBoundedQueryRestore.machine.start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  have full:=Composition.run_join appended RecoveryBoundedQueryRestore.machine _ _ _ (joinedReceipt p q) s pq sr'
  let cost:=loadTableBudget n total W+1+RecoveryBoundedTagReferenceAppend.budget compiled.compiled.output.val C+1+
    RecoveryBoundedQueryRestore.budget compiled.compiled.output.val F C
  have hb : cost ≤ budget W:=body_budget n total compiled.compiled.output.val F W hn hc hnode (by omega)
  have more:=runFrom_moreFuel machine _ (budget W-cost) _ (joinedReceipt (joinedReceipt p q) s) full
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨joinedReceipt (joinedReceipt p q) s,more,?_,sh,?_⟩
  · change p.steps+1+q.steps+1+s.steps ≤ budget W
    change s.steps=RecoveryBoundedQueryRestore.budget compiled.compiled.output.val F C at ss
    dsimp [cost] at hb
    omega
  · rw [output_next] at st
    exact st

end NearCubicWires.RepairOrdinary.RecoveryBoundedQuery
