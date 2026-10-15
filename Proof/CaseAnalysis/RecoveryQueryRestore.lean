import Proof.CaseAnalysis.RecoveryQueryScalar

/-! The complete original query handoff restores the initial table indices,
blank working address/prior list, actual next graph count and prior head. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryRestore
open LocalBitMultitape RepairRepresentation Composition
open RepairSource.VerifierDecoding
open RecoveryBoundedSelectorLoop (capacity sourceWord)
open RecoveryBoundedQuery (data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=Composition.machine RecoveryBoundedQueryClear.machine RecoveryBoundedQueryScalar.first
noncomputable def saved:=Composition.machine first (RecoveryBoundedQueryScalar.copy false)
noncomputable def second:=Composition.machine saved (RecoveryBoundedQueryScalar.copy true)
noncomputable def graph:=Composition.machine second RecoveryBoundedQueryScalar.graph
noncomputable def machine:=Composition.machine graph (RecoveryBoundedQueryClear.position true)
def budget (node F C : ℕ):=4*C+2*F+2*node+86
def output (A : Fin 60→List Bool) (node F C : ℕ):=
  RecoveryBoundedQueryScalar.graphOutput
    (RecoveryBoundedQueryScalar.copyOutput
      (RecoveryBoundedQueryScalar.copyOutput
        (RecoveryBoundedQueryScalar.firstOutput (RecoveryBoundedQueryClear.output A C) C) false 6 C) true (6+F) C) node

theorem restored_heads (out refs : List Bool) (pos : ℕ) :
    RecoveryBoundedQueryClear.heads (RecoveryBoundedQueryClear.heads (RecoveryBoundedQuery.heads out pos refs) false) true=
      RecoveryBoundedQuery.heads out pos refs := by
  funext i
  fin_cases i <;> rfl
theorem restored_tapes (index node C D value F prior L : ℕ) (out priorRefs : List Bool)
    (second tag : ℕ) (address : List Bool) (n total : ℕ) (source refs : List Bool) (hC : 1 ≤ C) :
    output (data index node C D value F prior L out priorRefs second tag address n total source refs) node F C=
      data 6 (node+1) C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total source refs := by
  funext i
  fin_cases i
  all_goals first | rfl |
    (change List.replicate C false=ZeroPadding.pad C [false];exact (RecoveryBoundedSelectorLoop.pad_false C hC).symm)

theorem restore_run (refs : List ℕ) (index node W D F L pos : ℕ) (out : List Bool)
    (nextSecond tag : ℕ) (address : List Bool) (n total : ℕ) (source queryRefs : List Bool)
    (hi : index ≤ W) (hs : nextSecond ≤ W) (ht : tag ≤ W) (hn : node ≤ W)
    (hinit : 6+F ≤ W) (ha : address.length ≤ W) (hc : refs.length ≤ W) (hr : ∀ r∈refs,r≤W) :
    let C:=capacity W
    ∃ r,runFrom machine (budget node F C)
      ⟨machine.start,RecoveryBoundedQuery.heads out pos queryRefs,
        data index node C D refs.length F refs.length L out (ZeroPadding.pad C (sourceWord refs))
          nextSecond tag address n total source queryRefs⟩=some r ∧
      r.steps=budget node F C ∧ r.final.heads=RecoveryBoundedQuery.heads out pos queryRefs ∧
      r.final.tapes=data 6 (node+1) C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total source queryRefs := by
  let C:=capacity W
  let H:=RecoveryBoundedQuery.heads out pos queryRefs
  let H0:=RecoveryBoundedQueryClear.heads H false
  let A:=data index node C D refs.length F refs.length L out (ZeroPadding.pad C (sourceWord refs))
    nextSecond tag address n total source queryRefs
  let A0:=RecoveryBoundedQueryClear.output A C
  let A1:=RecoveryBoundedQueryScalar.firstOutput A0 C
  let A2:=RecoveryBoundedQueryScalar.copyOutput A1 false 6 C
  let A3:=RecoveryBoundedQueryScalar.copyOutput A2 true (6+F) C
  have hWC : W+1 ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have hword : (sourceWord refs).length ≤ C := by
    have h:=RecoveryBoundedTableReferenceReset.source_length_bound refs W hr
    have hm:=Nat.mul_le_mul_right (2*W+1) hc
    dsimp [C,capacity]
    nlinarith [Nat.zero_le (W^2)]
  have hfit : ∀ j,(A (RecoveryBoundedQueryClear.saved j)).length ≤ C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (sourceWord refs)).length ≤ C
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl hword
    · change (ZeroPadding.pad C (CompareMachine.word refs.length)).length ≤ C
      simp only [ZeroPadding.pad_length,CompareMachine.word,List.length_cons,List.length_replicate]
      omega
    · change (ZeroPadding.pad C (List.replicate nextSecond true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      omega
    · change (ZeroPadding.pad C (List.replicate index true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      omega
    · change (ZeroPadding.pad C address).length ≤ C
      rw [ZeroPadding.pad_length]
      omega
    · change (ZeroPadding.pad C (List.replicate tag true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      omega
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedQueryClear.retreat_clear_run H A C (by rfl)
    (by intro j;fin_cases j <;> rfl) (by rfl) (by rfl) hfit
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedQueryScalar.first_run H0 A0 index refs.length C
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) (by omega) (by omega) (by omega)
  have qr' : runFrom RecoveryBoundedQueryScalar.first (RecoveryBoundedTagPrepare.budget 6 C)
      (restart p.final RecoveryBoundedQueryScalar.first.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have pq:=Composition.run_join RecoveryBoundedQueryClear.machine RecoveryBoundedQueryScalar.first _ _ _ p q pr qr'
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedQueryScalar.copy_run false H0 A1 6 C
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) (by omega)
  have sr' : runFrom (RecoveryBoundedQueryScalar.copy false) (2*6+4)
      (restart (joinedReceipt p q).final (RecoveryBoundedQueryScalar.copy false).start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  have pqs:=Composition.run_join first (RecoveryBoundedQueryScalar.copy false) _ _ _ (joinedReceipt p q) s pq sr'
  obtain ⟨t,tr,ts,th,tt⟩:=RecoveryBoundedQueryScalar.copy_run true H0 A2 (6+F) C
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) (by omega)
  have tr' : runFrom (RecoveryBoundedQueryScalar.copy true) (2*(6+F)+4)
      (restart (joinedReceipt (joinedReceipt p q) s).final (RecoveryBoundedQueryScalar.copy true).start)=some t := by
    change runFrom _ _ ⟨_,s.final.heads,s.final.tapes⟩=some t
    rw [sh,st]
    exact tr
  have pqst:=Composition.run_join saved (RecoveryBoundedQueryScalar.copy true) _ _ _ (joinedReceipt (joinedReceipt p q) s) t pqs tr'
  obtain ⟨u,ur,us,uh,ut⟩:=RecoveryBoundedQueryScalar.graph_run H0 A3 node C
    (by rfl) (by rfl) (by rfl) (by rfl) (by omega)
  have ur' : runFrom RecoveryBoundedQueryScalar.graph (2*node+4)
      (restart (joinedReceipt (joinedReceipt (joinedReceipt p q) s) t).final RecoveryBoundedQueryScalar.graph.start)=some u := by
    change runFrom _ _ ⟨_,t.final.heads,t.final.tapes⟩=some u
    rw [th,tt]
    exact ur
  have pqstu:=Composition.run_join second RecoveryBoundedQueryScalar.graph _ _ _ (joinedReceipt (joinedReceipt (joinedReceipt p q) s) t) u pqst ur'
  obtain ⟨v,vr,vs,vh,vt⟩:=RecoveryBoundedQueryClear.position_run true H0 (RecoveryBoundedQueryScalar.graphOutput A3 node) (by rfl)
  have vr' : runFrom (RecoveryBoundedQueryClear.position true) 1
      (restart (joinedReceipt (joinedReceipt (joinedReceipt (joinedReceipt p q) s) t) u).final (RecoveryBoundedQueryClear.position true).start)=some v := by
    change runFrom _ _ ⟨_,u.final.heads,u.final.tapes⟩=some v
    rw [uh,ut]
    exact vr
  have full:=Composition.run_join graph (RecoveryBoundedQueryClear.position true) _ _ _
    (joinedReceipt (joinedReceipt (joinedReceipt (joinedReceipt p q) s) t) u) v pqstu vr'
  have he : (2*C+6)+1+RecoveryBoundedTagPrepare.budget 6 C+1+(2*6+4)+1+(2*(6+F)+4)+1+(2*node+4)+1+1=budget node F C := by
    unfold budget RecoveryBoundedTagPrepare.budget
    omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt (joinedReceipt (joinedReceipt (joinedReceipt p q) s) t) u) v,full,?_,?_,?_⟩
  · change p.steps+1+q.steps+1+s.steps+1+t.steps+1+u.steps+1+v.steps=budget node F C
    rw [ps,qs,ss,ts,us,vs,he]
  · exact vh.trans (restored_heads out queryRefs pos)
  · exact vt.trans (restored_tapes index node C D refs.length F refs.length L out
      (ZeroPadding.pad C (sourceWord refs)) nextSecond tag address n total source queryRefs (by omega))

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryRestore
