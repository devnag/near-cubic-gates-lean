import Proof.CaseAnalysis.RecoveryRowErase
import Proof.CaseAnalysis.RowsBankPorts

/-! Reload the fifteen nonzero row metadata words from one retained paid
prototype packet, then rewind that same packet for its next use. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReload
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports : List (Fin 78):=[1,22,35,41,42,44,46,50,53,54,55,56,57,60,72]
def word (fields : Fin 78→List Bool):=CloseoutRowsPacketLoad.stream fields ports
noncomputable def load:=CloseoutRowsPacketLoad.machine (75 : Fin 78) 73 ports
def loadBudget (fields : Fin 78→List Bool):=CloseoutRowsPacketLoad.cost fields ports
def loaded (fields : Fin 78→List Bool) (B : ℕ) (A : Fin 78→List Bool):=
  CloseoutRowsPacketLoad.written fields B ports A
def rewindSlots : Fin 3→Fin 78:=![75,76,73]
noncomputable def rewind:=RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
noncomputable def machine:=Composition.machine load rewind
def budget (fields : Fin 78→List Bool) (B : ℕ):=loadBudget fields+1+(2*B+2)

theorem loaded_apply (fields : Fin 78→List Bool) (B : ℕ) (A : Fin 78→List Bool) (i : Fin 78) :
    loaded fields B A i=if i∈ports then ZeroPadding.pad B (fields i) else A i :=
  CloseoutRowsBankPorts.written_apply fields B ports A i

theorem rewind_run (H : Fin 78→ℕ) (A : Fin 78→List Bool) (source : List Bool) (B pos : ℕ)
    (hH : ∀ j,H (rewindSlots j)=(![pos,0,0] : Fin 3→ℕ) j)
    (hA : ∀ j,A (rewindSlots j)=(![source,List.replicate B true,List.replicate B false] : Fin 3→List Bool) j)
    (hp : pos ≤ B) :
    ∃ r,runFrom rewind (2*B+2) ⟨rewind.start,H,A⟩=some r ∧
      r.steps=2*B+2 ∧ r.final.heads=Function.update H 75 0 ∧ r.final.tapes=A := by
  obtain ⟨p,pr,ps,pf⟩:=RecoveryBoundedQueryRewind.padded_run source B pos hp
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock rewindSlots (by decide)
    CompetitorRecordRewind.machine _ H A (RecoveryBoundedQueryRewind.padded 0 source pos B) hH hA p pr
  refine ⟨r,rr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,rewindSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf]
      fin_cases j
      · rfl
      · change 0=Function.update H 75 0 76
        rw [Function.update_of_ne (by decide)]
        exact (hH 1).symm
      · change 0=Function.update H 75 0 73
        rw [Function.update_of_ne (by decide)]
        exact (hH 2).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      exact (Function.update_of_ne (fun he=>hi ⟨0,he.symm⟩) _ _).symm
  · funext i
    by_cases hi : ∃ j,rewindSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pf]
      exact (hA j).symm
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).2

theorem reload_run (fields : Fin 78→List Bool) (B : ℕ) (tail : List Bool)
    (H : Fin 78→ℕ) (A : Fin 78→List Bool)
    (hs : H 75=0) (hl : H 73=0) (hd : H 76=0) (hj : ∀ j∈ports,H j=0)
    (ds : A 75=word fields++tail) (dl : A 73=List.replicate B false)
    (dd : A 76=List.replicate B true) (dj : ∀ j∈ports,A j=List.replicate B false)
    (hfield : ∀ j∈ports,(fields j).length ≤ B) (hword : (word fields).length ≤ B) :
    ∃ r,runFrom machine (budget fields B) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ budget fields B ∧ r.final.heads=H ∧ r.final.tapes=loaded fields B A := by
  obtain ⟨p,pr,ph,pt,ps⟩:=CloseoutRowsPacketLoad.list_run (75 : Fin 78) 73 ports fields
    (by decide) (by decide)
    (by intro j h he;subst j;simp [ports] at h)
    (by intro j h he;subst j;simp [ports] at h)
    [] tail B B H A hs hl hj (by simpa only [List.nil_append,word] using ds) dl dj hfield
  have hr : ∀ j,(Function.update H 75 (word fields).length) (rewindSlots j)=
      (![ (word fields).length,0,0] : Fin 3→ℕ) j := by
    intro j;fin_cases j
    · rfl
    · change Function.update H 75 (word fields).length 76=0
      rw [Function.update_of_ne (by decide)]
      exact hd
    · change Function.update H 75 (word fields).length 73=0
      rw [Function.update_of_ne (by decide)]
      exact hl
  have ht : ∀ j,loaded fields B A (rewindSlots j)=
      (![word fields++tail,List.replicate B true,List.replicate B false] : Fin 3→List Bool) j := by
    intro j;fin_cases j
    · change loaded fields B A 75=word fields++tail
      rw [loaded_apply,if_neg (by decide : (75 : Fin 78)∉ports)]
      exact ds
    · change loaded fields B A 76=List.replicate B true
      rw [loaded_apply,if_neg (by decide : (76 : Fin 78)∉ports)]
      exact dd
    · change loaded fields B A 73=List.replicate B false
      rw [loaded_apply,if_neg (by decide : (73 : Fin 78)∉ports)]
      exact dl
  obtain ⟨q,qr,qs,qh,qt⟩:=rewind_run (Function.update H 75 (word fields).length)
    (loaded fields B A) (word fields++tail) B (word fields).length hr ht hword
  have qr' : runFrom rewind (2*B+2) (restart p.final rewind.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    simpa only [List.length_nil,Nat.zero_add,word,loaded] using qr
  have whole:=Composition.run_join load rewind _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,?_,qt⟩
  · change p.steps+1+q.steps ≤ budget fields B
    rw [ps,qs]
    exact Nat.le_refl _
  · change q.final.heads=H
    rw [qh,Function.update_idem]
    simpa only [hs] using Function.update_eq_self 75 H

theorem budget_bound (fields : Fin 78→List Bool) (B : ℕ)
    (hfield : ∀ j∈ports,(fields j).length ≤ B) : budget fields B ≤ 47*B+48 := by
  have h:=CloseoutRowsPacketLoad.cost_bound fields ports B hfield
  change loadBudget fields ≤ 15*(3*B+3) at h
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReload
