import Proof.CaseAnalysis.RecoveryTableSavedClear
import Proof.Amplification.RecoveryEraseWidth

/-! Restore the original first-field index twice, advance the actual graph
count and advance the actual prior-reference count in the retained bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableScalarFinish
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots : Fin 7→Fin 55:=![46,1,41,34,32,22,23]
noncomputable def first:=RecoveryFocus.machine firstSlots RecoveryBoundedTagPrepare.machine
def firstOutput:=RecoveryBoundedNodeTagPrepare.output

theorem first_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (next index value C : ℕ)
    (hH : ∀ j,H (firstSlots j)=0) (hA : ∀ j,A (firstSlots j)=RecoveryBoundedTagPrepare.data next index value C 0 j)
    (hi : index ≤ C) (hv : value ≤ C) (hn : next+1 ≤ C) :
    ∃ r,runFrom first (RecoveryBoundedTagPrepare.budget next C) ⟨first.start,H,A⟩=some r ∧
      r.steps=RecoveryBoundedTagPrepare.budget next C ∧ r.final.heads=H ∧ r.final.tapes=firstOutput A next C := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedTagPrepare.prepare_ready next index value C hi hv hn).focus_at
    firstSlots (by decide) H A hA hH
  have he : install firstSlots A (RecoveryBoundedTagPrepare.data next index value C 3)=firstOutput A next C := by
    apply HierarchyWidth.install_eq firstSlots (by decide)
    · intro j
      have hj:=hA j
      fin_cases j <;> first | rfl | exact hj
    · intro i hi
      have h1 : i≠1:=fun h=>hi 1 h.symm
      have h41 : i≠41:=fun h=>hi 2 h.symm
      have h34 : i≠34:=fun h=>hi 3 h.symm
      simp only [firstOutput,RecoveryBoundedNodeTagPrepare.output,h1,h41,or_self,if_false,if_neg h34]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

def graphSlots : Fin 2→Fin 55:=![25,32]
noncomputable def graph:=RecoveryFocus.machine graphSlots RepairSource.RecoveryTseitinRawIncrement.machine
def graphOutput (A : Fin 55→List Bool) (node : ℕ):=Function.update A 25 (List.replicate (node+1) true)

theorem graph_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (node C : ℕ)
    (h25 : H 25=0) (h32 : H 32=0) (a25 : A 25=List.replicate node true) (a32 : A 32=List.replicate C false)
    (hC : node+1 ≤ C) :
    ∃ r,runFrom graph (2*node+4) ⟨graph.start,H,A⟩=some r ∧
      r.steps=2*node+4 ∧ r.final.heads=H ∧ r.final.tapes=graphOutput A node := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready node C hC).focus_at
    graphSlots (by decide) H A
    (by intro j;fin_cases j;exact a25;exact a32) (by intro j;fin_cases j;exact h25;exact h32)
  have he : install graphSlots A ![List.replicate (node+1) true,List.replicate C false]=graphOutput A node := by
    apply HierarchyWidth.install_eq graphSlots (by decide)
    · intro j
      fin_cases j
      · rfl
      · exact a32
    · intro i hi
      have h25 : i≠25:=fun h=>hi 0 h.symm
      simp only [graphOutput,Function.update_of_ne h25]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

def countSlots : Fin 1→Fin 55:=fun _=>42
noncomputable def count:=RecoveryFocus.machine countSlots RecoveryEraseWidth.incrementMachine
def countOutput (A : Fin 55→List Bool) (value : ℕ):=Function.update A 42 (CompareMachine.word (value+1))

theorem count_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (value : ℕ)
    (h42 : H 42=1) (a42 : A 42=CompareMachine.word value) :
    ∃ r,runFrom count (2*value+2) ⟨count.start,H,A⟩=some r ∧
      r.steps=2*value+2 ∧ r.final.heads=H ∧ r.final.tapes=countOutput A value := by
  obtain ⟨p,pr,pf,ps⟩:=RecoveryEraseWidth.increment_run value
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock countSlots (by decide) RecoveryEraseWidth.incrementMachine _ H A
    (RecoveryEraseWidth.cfg 0 value 1) (by intro j;fin_cases j;exact h42) (by intro j;fin_cases j;exact a42) p pr
  refine ⟨r,hr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : i=42
    · subst i
      have h:=rh 0
      rw [pf] at h
      exact h.trans h42.symm
    · exact (rkeep i (by intro j;fin_cases j;exact Ne.symm hi)).1
  · funext i
    by_cases hi : i=42
    · subst i
      have h:=rt 0
      rw [pf] at h
      exact h
    · rw [(rkeep i (by intro j;fin_cases j;exact Ne.symm hi)).2]
      simp only [countOutput,Function.update_of_ne hi]

noncomputable def firstGraph:=Composition.machine first graph
noncomputable def machine:=Composition.machine firstGraph count
def budget (next node value C : ℕ):=2*C+4*next+2*node+2*value+22
def output (A : Fin 55→List Bool) (next node value C : ℕ):=countOutput (graphOutput (firstOutput A next C) node) value

theorem finish_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (next index value node prior C : ℕ)
    (hH : ∀ j,H (firstSlots j)=0) (h25 : H 25=0) (h42 : H 42=1)
    (hA : ∀ j,A (firstSlots j)=RecoveryBoundedTagPrepare.data next index value C 0 j)
    (a25 : A 25=List.replicate node true) (a42 : A 42=CompareMachine.word prior)
    (hi : index ≤ C) (hv : value ≤ C) (hn : next+1 ≤ C) (hg : node+1 ≤ C) :
    ∃ r,runFrom machine (budget next node prior C) ⟨machine.start,H,A⟩=some r ∧
      r.steps=budget next node prior C ∧ r.final.heads=H ∧ r.final.tapes=output A next node prior C := by
  obtain ⟨p,pr,ps,ph,pt⟩:=first_run H A next index value C hH hA hi hv hn
  obtain ⟨q,qr,qs,qh,qt⟩:=graph_run H (firstOutput A next C) node C h25 (hH 4) a25 (hA 4) hg
  have qr' : runFrom graph (2*node+4) (restart p.final graph.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have pq:=Composition.run_join first graph _ _ _ p q pr qr'
  obtain ⟨r,rr,rs,rh,rt⟩:=count_run H (graphOutput (firstOutput A next C) node) prior h42 a42
  have rr' : runFrom count (2*prior+2) (restart (joinedReceipt p q).final count.start)=some r := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some r
    rw [qh,qt]
    exact rr
  have full:=Composition.run_join firstGraph count _ _ _ (joinedReceipt p q) r pq rr'
  have he : ((RecoveryBoundedTagPrepare.budget next C+1+(2*node+4))+1+(2*prior+2))=budget next node prior C := by
    unfold budget RecoveryBoundedTagPrepare.budget
    omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt p q) r,full,?_,rh,rt⟩
  change p.steps+1+q.steps+1+r.steps=budget next node prior C
  rw [ps,qs,rs,he]

theorem budget_quadratic (next node prior W : ℕ) (hn : next ≤ W) (hg : node ≤ W) (hp : prior ≤ W) :
    budget next node prior (RecoveryBoundedSelectorLoop.capacity W) ≤ 65536*(W+1)^2 := by
  unfold budget RecoveryBoundedSelectorLoop.capacity
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableScalarFinish
