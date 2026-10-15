import Proof.CaseAnalysis.RecoveryTableScalarFinish

/-! The complete paid original table handoff: append the actual live
reference, advance all row indices, clear saved fields, restore both first
indices, and advance graph/prior counts. Return the next full node bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableRestore
open LocalBitMultitape RepairRepresentation Composition
open RecoveryBoundedUniversalNodeBank RecoveryBoundedUniversalNodeTableBoundary
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def indexed:=Composition.machine RecoveryBoundedTableReferenceBank.machine RecoveryBoundedTableIndexAdvance.machine
noncomputable def cleared:=Composition.machine indexed RecoveryBoundedTableSavedClear.machine
noncomputable def machine:=Composition.machine cleared RecoveryBoundedTableScalarFinish.machine
def budget (refs : List ℕ) (next node F C W : ℕ):=
  ((RecoveryBoundedTableReferenceReset.budget refs node C+1+RecoveryBoundedTableIndexAdvance.budget F W)+1+(2*C+4))+1+
    RecoveryBoundedTableScalarFinish.budget next node refs.length C

theorem next_tapes (refs : List ℕ) (first node C D F L : ℕ) (result : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ) :
    RecoveryBoundedTableScalarFinish.output
      (RecoveryBoundedTableSavedClear.output
        (RecoveryBoundedTableIndexBank.output
          (RecoveryBoundedTableReferenceBank.output
            (finished first node C D F refs.length L result (ZeroPadding.pad C (sourceWord refs))
              second tag left right constant current address count) refs node C)
          first second tag (2*F+6)) C) (first+(2*F+6)) node refs.length C=
      data (first+(2*F+6)) (node+1) C D 0 F (refs.length+1) L result
        (ZeroPadding.pad C (sourceWord (refs++[node]))) (second+(2*F+6)) (tag+(2*F+6)) 0 0 0 address count [] := by
  funext i
  fin_cases i <;> rfl

theorem restore_run (refs : List ℕ) (first node D F L W : ℕ) (result : List Bool)
    (second tag left right constant current : ℕ) (address : List Bool) (count : ℕ)
    (ha : first+(2*F+6) ≤ W) (hb : second+(2*F+6) ≤ W) (hc : tag+(2*F+6) ≤ W)
    (hn : node ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hk : constant ≤ W) (hi : current ≤ W)
    (hcount : refs.length ≤ W) (hrefs : ∀ r∈refs,r≤W) (hD : 8388608*(W+1)^3 ≤ D) :
    let C:=capacity W
    ∃ r,runFrom machine (budget refs (first+(2*F+6)) node F C W)
      ⟨machine.start,heads result,finished first node C D F refs.length L result (ZeroPadding.pad C (sourceWord refs))
        second tag left right constant current address count⟩=some r ∧
      r.steps ≤ budget refs (first+(2*F+6)) node F C W ∧ r.final.heads=heads result ∧
      r.final.tapes=data (first+(2*F+6)) (node+1) C D 0 F (refs.length+1) L result
        (ZeroPadding.pad C (sourceWord (refs++[node]))) (second+(2*F+6)) (tag+(2*F+6)) 0 0 0 address count [] := by
  let C:=capacity W
  let A:=finished first node C D F refs.length L result (ZeroPadding.pad C (sourceWord refs))
    second tag left right constant current address count
  let A1:=RecoveryBoundedTableReferenceBank.output A refs node C
  let A2:=RecoveryBoundedTableIndexBank.output A1 first second tag (2*F+6)
  let A3:=RecoveryBoundedTableSavedClear.output A2 C
  dsimp only
  have hWC : W+1 ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have fit : ∀ v≤W,v≤C:=by intro v hv;omega
  have hframe : 2*node+1 ≤ C := by dsimp [C,capacity];nlinarith [Nat.zero_le (W^2)]
  have hlog : RecoveryBoundedTableReferenceAppend.budget refs node C ≤ D := by
    have h:=RecoveryBoundedTableReferenceReset.append_budget_quadratic refs node W hcount hrefs hn
    change RecoveryBoundedTableReferenceAppend.budget refs node C ≤ 65536*(W+1)^2 at h
    nlinarith [Nat.zero_le (W^3)]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTableReferenceBank.reference_run (heads result) A refs node C D
    (reference_heads result) (reference_tapes refs first node C D F L result second tag left right constant current address count)
    hframe hlog
  have hF : ∀ j,A1 (RecoveryBoundedTableIndexBank.slots false j)=RecoveryBoundedTableIndexBank.input first second tag C F j:=
    index_tapes refs first node C D F L result second tag left right constant current address count false
  have h6 : ∀ j,A1 (RecoveryBoundedTableIndexBank.slots true j)=RecoveryBoundedTableIndexBank.input first second tag C 6 j:=
    index_tapes refs first node C D F L result second tag left right constant current address count true
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedTableIndexAdvance.advance_run (heads result) A1 first second tag F C W
    (index_heads result) hF h6 ha hb hc hWC
  have qr' : runFrom RecoveryBoundedTableIndexAdvance.machine (RecoveryBoundedTableIndexAdvance.budget F W)
      (restart p.final RecoveryBoundedTableIndexAdvance.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have pq:=Composition.run_join RecoveryBoundedTableReferenceBank.machine RecoveryBoundedTableIndexAdvance.machine _ _ _ p q pr qr'
  have hfit : ∀ j,(A2 (RecoveryBoundedTableSavedClear.saved j)).length ≤ C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (List.replicate left true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact max_le le_rfl (fit left hl)
    · change (ZeroPadding.pad C (List.replicate right true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact max_le le_rfl (fit right hr)
    · change (ZeroPadding.pad C (List.replicate constant true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact max_le le_rfl (fit constant hk)
    · change (ZeroPadding.pad C (RecoveryBoundedTagPacket.word constant current)).length ≤ C
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl (RecoveryBoundedTagPacketReset.packet_fits constant current W hk hi)
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedTableSavedClear.clear_run (heads result) A2 C
    (by intro j;fin_cases j <;> rfl) (by rfl) (by rfl) hfit
  have sr' : runFrom RecoveryBoundedTableSavedClear.machine (2*C+4)
      (restart (joinedReceipt p q).final RecoveryBoundedTableSavedClear.machine.start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  have pqs:=Composition.run_join indexed RecoveryBoundedTableSavedClear.machine _ _ _ (joinedReceipt p q) s pq sr'
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedTableScalarFinish.finish_run (heads result) A3 (first+(2*F+6)) tag 5 node refs.length C
    (by intro j;fin_cases j <;> rfl) (by rfl) (by rfl) (by intro j;fin_cases j <;> rfl) (by rfl) (by rfl)
    (fit tag (by omega)) (fit 5 (by omega)) (by omega) (by omega)
  have rr' : runFrom RecoveryBoundedTableScalarFinish.machine
      (RecoveryBoundedTableScalarFinish.budget (first+(2*F+6)) node refs.length C)
      (restart (joinedReceipt (joinedReceipt p q) s).final RecoveryBoundedTableScalarFinish.machine.start)=some r := by
    change runFrom _ _ ⟨_,s.final.heads,s.final.tapes⟩=some r
    rw [sh,st]
    exact rr
  have full:=Composition.run_join cleared RecoveryBoundedTableScalarFinish.machine _ _ _ (joinedReceipt (joinedReceipt p q) s) r pqs rr'
  refine ⟨joinedReceipt (joinedReceipt (joinedReceipt p q) s) r,full,?_,rh,?_⟩
  · change p.steps+1+q.steps+1+s.steps+1+r.steps ≤ budget refs (first+(2*F+6)) node F C W
    unfold budget
    omega
  · change r.final.tapes=_
    exact rt.trans (next_tapes refs first node C D F L result second tag left right constant current address count)

theorem budget_quadratic (refs : List ℕ) (next node F W : ℕ)
    (hc : refs.length ≤ W) (hr : ∀ r∈refs,r≤W) (hn : node ≤ W) (hnext : next ≤ W) (hF : F ≤ W) (h6 : 6 ≤ W) :
    budget refs next node F (capacity W) W ≤ 524288*(W+1)^2 := by
  have href:=RecoveryBoundedTableReferenceReset.budget_quadratic refs node W hc hr hn
  have hindex:=RecoveryBoundedTableIndexAdvance.budget_quadratic F W hF h6
  have hscalar:=RecoveryBoundedTableScalarFinish.budget_quadratic next node refs.length W hnext hn hc
  have hclear : 2*capacity W+4 ≤ 32772*(W+1)^2 := by unfold capacity;nlinarith [Nat.zero_le (W^2)]
  unfold budget
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableRestore
