import Proof.CaseAnalysis.RecoveryRowPrototype

/-! The complete paid post-row continuation: save the original output,
erase the work bank, reload the original prototype and rewind its source. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAfter
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedRowPrototype (fields)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out stack : List Bool) (i : Fin 78):=if i=20 then out.length else if i=74 then stack.length else 0
def data (A : Fin 73→List Bool) (B : ℕ) (stack packet : List Bool) : Fin 78→List Bool:=
  Fin.addCases (m:=73) (n:=5) (motive:=fun _=>List Bool) A
    ![List.replicate B false,stack,packet,List.replicate B true,List.replicate (B+1) false]
def old (i : Fin 73) : Fin 78:=i.castAdd 5

theorem old_data (A : Fin 73→List Bool) (B : ℕ) (stack packet : List Bool) (i : Fin 73) :
    data A B stack packet (old i)=A i := Fin.addCases_left i
theorem collect_heads (out stack next : List Bool) :
    RecoveryBoundedRowCollect.heads (heads out stack) next=heads out next := by
  funext i
  by_cases h74 : i=74
  · subst i;rfl
  · simp only [RecoveryBoundedRowCollect.heads,Function.update_of_ne h74,heads,if_neg h74]
theorem collect_data (A : Fin 73→List Bool) (B : ℕ) (stack next packet : List Bool) :
    RecoveryBoundedRowCollect.data (data A B stack packet) next=data A B next packet := by
  funext i
  refine Fin.addCases (m:=73) (n:=5) ?_ ?_ i
  · intro j
    have hn : (j.castAdd 5 : Fin 78)≠74 := by
      intro he;have hv:=congrArg (fun i : Fin 78=>i.val) he;have hj:=j.isLt;change j.val=74 at hv;omega
    simp only [RecoveryBoundedRowCollect.data,Function.update_of_ne hn,data,Fin.addCases_left]
  · intro j;fin_cases j <;> rfl

theorem erase_heads (out stack : List Bool) : ∀ i,heads out stack (RecoveryBoundedRowErase.slots i)=0 := by
  intro i
  refine Fin.addCases (m:=70) (n:=2) ?_ ?_ i
  · intro j
    have hw:=RecoveryBoundedRowErase.work_spec j
    have h74:=RecoveryBoundedRowErase.work_high j 74 (by decide)
    simp only [RecoveryBoundedRowErase.slots,Fin.addCases_left,heads,if_neg hw.2.1,if_neg h74]
  · intro j;fin_cases j <;> rfl
theorem erase_sizes (A : Fin 73→List Bool) (B : ℕ) (stack packet : List Bool)
    (hA : ∀ i,(A i).length ≤ B) :
    ∀ i,(data A B stack packet (RecoveryBoundedRowErase.work i)).length ≤ B := by
  intro i
  let j : Fin 73:=⟨(RecoveryBoundedRowErase.work i).val,(RecoveryBoundedRowErase.work_spec i).1⟩
  have hj : old j=RecoveryBoundedRowErase.work i:=Fin.ext rfl
  rw [←hj,old_data]
  exact hA j

theorem erased_port (A : Fin 78→List Bool) (B : ℕ) :
    ∀ j∈RecoveryBoundedRowReload.ports,RecoveryBoundedRowErase.data B A j=List.replicate B false := by
  intro j hj
  apply if_pos
  simp only [RecoveryBoundedRowReload.ports,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem heads_port (out stack : List Bool) : ∀ j∈RecoveryBoundedRowReload.ports,heads out stack j=0 := by
  intro j hj
  simp only [RecoveryBoundedRowReload.ports,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

noncomputable def first:=Composition.machine RecoveryBoundedRowCollect.machine RecoveryBoundedRowErase.machine
noncomputable def machine:=Composition.machine first RecoveryBoundedRowReload.machine
def budget (ref B : ℕ) (f : Fin 78→List Bool):=(4*ref+6)+1+(2*B+4)+1+RecoveryBoundedRowReload.budget f B

theorem after_run (node ref C D F L n total queries clauses B : ℕ) (out source stack tail : List Bool)
    (A : Fin 73→List Bool) (hA : ∀ i,(A i).length ≤ B)
    (a20 : A 20=out) (a25 : A 25=List.replicate node true) (a70 : A 70=source)
    (a45 : A 45=ZeroPadding.pad B (List.replicate ref true))
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B) (href : 2*ref+2≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields C D F L n total queries clauses j).length≤B)
    (hw : (RecoveryBoundedRowReload.word (fields C D F L n total queries clauses)).length≤B) :
    let f:=fields C D F L n total queries clauses
    let packet:=RecoveryBoundedRowReload.word f++tail
    let nextStack:=RecoveryBoundedClauseCollect.pushed ref stack
    let nextData:=RecoveryBoundedRowReuse.paddedData B
      (RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses)
    ∃ r,runFrom machine (budget ref B f) ⟨machine.start,heads out stack,data A B stack packet⟩=some r ∧
      r.steps ≤ budget ref B f ∧ r.final.heads=heads out nextStack ∧
      r.final.tapes=data nextData B nextStack packet := by
  let f:=fields C D F L n total queries clauses
  let packet:=RecoveryBoundedRowReload.word f++tail
  let nextStack:=RecoveryBoundedClauseCollect.pushed ref stack
  let oldA:=data A B stack packet
  let nextA:=data A B nextStack packet
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedRowCollect.collect_run (heads out stack) oldA ref B stack
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j;exact a45;rfl;rfl) href
  rw [collect_heads] at ph
  dsimp only [oldA] at pt
  rw [collect_data] at pt
  obtain ⟨q,qr,qh,qt,qs⟩:=RecoveryBoundedRowErase.erase_run B (heads out nextStack) nextA
    (erase_heads out nextStack) (erase_sizes A B nextStack packet hA) rfl rfl
  have qr' : runFrom RecoveryBoundedRowErase.machine (2*B+4) (restart p.final RecoveryBoundedRowErase.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have firstRun:=Composition.run_join RecoveryBoundedRowCollect.machine RecoveryBoundedRowErase.machine _ _ _ p q pr qr'
  let pq:=joinedReceipt p q
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedRowReload.reload_run f B tail (heads out nextStack)
    (RecoveryBoundedRowErase.data B nextA) rfl rfl rfl (heads_port out nextStack) rfl rfl rfl
    (erased_port nextA B) hf hw
  have sr' : runFrom RecoveryBoundedRowReload.machine (RecoveryBoundedRowReload.budget f B)
      (restart pq.final RecoveryBoundedRowReload.machine.start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  have whole:=Composition.run_join first RecoveryBoundedRowReload.machine _ _ _ pq s firstRun sr'
  refine ⟨joinedReceipt pq s,whole,?_,sh,?_⟩
  · change p.steps+1+q.steps+1+s.steps ≤ budget ref B f
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right ps 1) qs) 1) ss
  · change s.final.tapes=_
    rw [st]
    funext i
    refine Fin.addCases (m:=73) (n:=5) ?_ ?_ i
    · intro j
      rw [data,Fin.addCases_left]
      exact RecoveryBoundedRowPrototype.reload_original node C D F L n total queries clauses B out source nextA
        hC hD hL a20 a25 a70 j
    · intro j;fin_cases j
      all_goals rw [RecoveryBoundedRowReload.loaded_apply,if_neg (by decide)]
      all_goals rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAfter
