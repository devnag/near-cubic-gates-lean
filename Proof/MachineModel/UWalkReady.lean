import Proof.MachineModel.UWalkScalars

/-! The complete walk-numeric supplier starts and ends at the literal
sentinel heads. Entering and restoring these heads are actual transitions. -/
namespace NearCubicWires.RepairOrdinary.UWalkNumbers
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 42) : Bool := i.val==1 || i.val==2 || i.val==3
def heads (i : Fin 42) : ℕ := if selected i then 1 else 0
def shift (move : HeadMove) : Machine 42 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some
    ⟨1,fun _ => none,fun i => if selected i then move else .stay⟩ else none

theorem shift_left (tapes : Store) :
    ∃ r,runFrom (shift .left) 1 (RecoveryCalls.restarted (shift .left) heads tapes)=some r ∧
      r.final.tapes=tapes ∧ r.final.heads=(fun _ => 0) ∧ r.steps=1 := by
  let last : Configuration 42 2 := ⟨1,fun _ => 0,tapes⟩
  have hs : step (shift .left) (RecoveryCalls.restarted (shift .left) heads tapes)=some last := by
    simp [step,shift,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i
      cases h : selected i <;> simp [applyAction,heads,h,HeadMove.apply,last]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

theorem shift_right (tapes : Store) :
    ∃ r,run (shift .right) 1 tapes=some r ∧
      r.final.tapes=tapes ∧ r.final.heads=heads ∧ r.steps=1 := by
  let last : Configuration 42 2 := ⟨1,heads,tapes⟩
  have hs : step (shift .right) (initialConfiguration (shift .right) tapes)=some last := by
    simp [step,shift,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      cases h : selected i <;> simp [applyAction,heads,h,HeadMove.apply,last]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

noncomputable def entered := Composition.machine (shift .left) core
noncomputable def machine := Composition.machine entered (shift .right)
noncomputable def entry (w t j c : ℕ) := RecoveryCalls.restarted machine heads (input w t j c)

theorem entered_run (w t j c : ℕ) (hw : 1 ≤ w) :
    ∃ r,runFrom entered (coreCost w t j+2)
      (RecoveryCalls.restarted entered heads (input w t j c))=some r ∧
      r.final.tapes=afterUnit w t j c ∧ (∀ i,r.final.heads i=0) ∧ r.steps ≤ coreCost w t j+2 := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := shift_left (input w t j c)
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := core_ready w t j c hw
  have he : Composition.restart first.final core.start=initialConfiguration core (input w t j c) := by
    apply configuration_ext
    · rfl
    · exact hh
    · exact ht
  unfold run at hlast
  rw [←he] at hlast
  have h := Composition.run_join (shift .left) core 1 (coreCost w t j) _ first last hfirst hlast
  have heq : 1+1+coreCost w t j=coreCost w t j+2 := by omega
  rw [heq] at h
  refine ⟨Composition.joinedReceipt first last,h,hlt,hlh,?_⟩
  dsimp only [Composition.joinedReceipt]
  omega

theorem total_run (w t j c : ℕ) (hw : 1 ≤ w) :
    ∃ r,runFrom machine (budget w t j) (entry w t j c)=some r ∧
      r.final.tapes=afterUnit w t j c ∧ r.final.heads=heads ∧ r.steps ≤ budget w t j := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := entered_run w t j c hw
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := shift_right (afterUnit w t j c)
  have he : Composition.restart first.final (shift .right).start=
      initialConfiguration (shift .right) (afterUnit w t j c) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  unfold run at hlast
  rw [←he] at hlast
  have h := Composition.run_join entered (shift .right) (coreCost w t j+2) 1 _ first last hfirst hlast
  have heq : coreCost w t j+2+1+1=coreCost w t j+4 := by omega
  rw [heq] at h
  let r := Composition.joinedReceipt first last
  have hmore := runFrom_moreFuel machine (coreCost w t j+4) (budget w t j-(coreCost w t j+4)) _ r h
  rw [Nat.add_sub_of_le (core_bound w t j)] at hmore
  refine ⟨r,hmore,hlt,hlh,?_⟩
  dsimp only [r,Composition.joinedReceipt]
  have := core_bound w t j
  omega

theorem cap_eq (w t j : ℕ) : q w t j+1=UWalkCapacity.amount w t j := by
  dsimp [q,p,d,UWalkCapacity.amount]
  ring

theorem budget_short (w t j c : ℕ) (ht : t ≤ c) (hj : j ≤ c) :
    budget w t j ≤ 16384*(c+1)*(w+1) := by
  dsimp [budget]
  nlinarith

end NearCubicWires.RepairOrdinary.UWalkNumbers
