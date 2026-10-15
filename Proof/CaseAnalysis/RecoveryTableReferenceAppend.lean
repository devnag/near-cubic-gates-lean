import Proof.CaseAnalysis.RecoveryTableReferenceSeek

/-! One fixed table handoff locates the original prior-reference stream's
end and appends the actual new node output using the checked framed writer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceAppend
open LocalBitMultitape RepairRepresentation Composition
open RepairSource.VerifierDecoding RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 8→ℕ:=
  Fin.addCases (m:=7) (n:=1) (motive:=fun _=>ℕ) (RecoveryBoundedTagReferenceAppend.heads out) (fun _=>1)
def data (node C count : ℕ) (out : List Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedTagReferenceAppend.paddedData node 0 C out) (fun _=>CompareMachine.word count)
def seekSlots : Fin 2→Fin 8:=![4,7]
noncomputable def seek:=RecoveryFocus.machine seekSlots RecoveryBoundedTableReferenceSeek.machine
noncomputable def append:=TapeEmbedding.machine 1 RecoveryBoundedTagReferenceAppend.machine
noncomputable def machine:=Composition.machine seek append
def budget (refs : List ℕ) (node C : ℕ):=
  RecoveryBoundedTableReferenceSeek.budget refs+1+RecoveryBoundedTagReferenceAppend.budget node C

theorem seek_run (refs : List ℕ) (node C : ℕ) :
    ∃ r,runFrom seek (RecoveryBoundedTableReferenceSeek.budget refs)
      ⟨seek.start,heads [],data node C refs.length (sourceWord refs)⟩=some r ∧
      r.steps ≤ RecoveryBoundedTableReferenceSeek.budget refs ∧
      r.final.heads=heads (sourceWord refs) ∧ r.final.tapes=data node C refs.length (sourceWord refs) := by
  let tail:=List.replicate (C-(sourceWord refs).length) false
  let src:=RecoveryBoundedTableReferenceSeek.cfg 0 refs tail 0
  obtain ⟨p,pr,ps,pf⟩:=RecoveryBoundedTableReferenceSeek.seek_run refs tail
  have hH : ∀ j,heads [] (seekSlots j)=src.heads j := by
    intro j
    rw [RecoveryBoundedTableReferenceSeek.cfg_heads]
    fin_cases j <;> rfl
  have hA : ∀ j,data node C refs.length (sourceWord refs) (seekSlots j)=src.tapes j := by
    intro j
    rw [RecoveryBoundedTableReferenceSeek.cfg_tapes]
    fin_cases j <;> rfl
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock seekSlots (by decide)
    RecoveryBoundedTableReferenceSeek.machine _ (heads []) (data node C refs.length (sourceWord refs)) src hH hA p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,seekSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf,RecoveryBoundedTableReferenceSeek.cfg_heads]
      fin_cases j <;> rfl
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h4 : i≠4:=fun h=>hi ⟨0,h.symm⟩
      fin_cases i <;> first | rfl | exact False.elim (h4 rfl)
  · funext i
    by_cases hi : ∃ j,seekSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pf,RecoveryBoundedTableReferenceSeek.cfg_tapes]
      fin_cases j <;> rfl
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).2

theorem append_run (refs : List ℕ) (node C : ℕ) (hC : 2*node+1 ≤ C) :
    ∃ r,runFrom append (RecoveryBoundedTagReferenceAppend.budget node C)
      ⟨append.start,heads (sourceWord refs),data node C refs.length (sourceWord refs)⟩=some r ∧
      r.steps ≤ RecoveryBoundedTagReferenceAppend.budget node C ∧
      r.final.heads=heads (sourceWord (refs++[node])) ∧
      r.final.tapes=data node C refs.length (sourceWord (refs++[node])) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTagReferenceAppend.padded_run node 0 C (sourceWord refs) hC
  let eh : Fin 1→ℕ:=fun _=>1
  let et : Fin 1→List Bool:=fun _=>CompareMachine.word refs.length
  have hr:=TapeEmbedding.run_embed RecoveryBoundedTagReferenceAppend.machine eh et _ _ p pr
  refine ⟨TapeEmbedding.receipt eh et p,hr,ps,?_,?_⟩
  · change Fin.addCases (m:=7) (n:=1) (motive:=fun _=>ℕ) p.final.heads eh=_
    rw [ph]
    simp only [heads,sourceWord,List.flatMap_append,List.flatMap_singleton,eh]
  · change Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool) p.final.tapes et=_
    rw [pt]
    simp only [data,sourceWord,List.flatMap_append,List.flatMap_singleton,et]

theorem reference_run (refs : List ℕ) (node C : ℕ) (hC : 2*node+1 ≤ C) :
    ∃ r,runFrom machine (budget refs node C)
      ⟨machine.start,heads [],data node C refs.length (sourceWord refs)⟩=some r ∧
      r.steps ≤ budget refs node C ∧ r.final.heads=heads (sourceWord (refs++[node])) ∧
      r.final.tapes=data node C refs.length (sourceWord (refs++[node])) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=seek_run refs node C
  obtain ⟨q,qr,qs,qh,qt⟩:=append_run refs node C hC
  have qr' : runFrom append (RecoveryBoundedTagReferenceAppend.budget node C) (restart p.final append.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join seek append _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ budget refs node C
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceAppend
