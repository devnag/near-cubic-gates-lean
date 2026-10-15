import Proof.Amplification.RecoveryTseitinReferenceBanks

/-! Compose demanded physical reference calls with abstract control and budget
carriers, avoiding reduction of the large fixed cold machine during joins. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences.Sequence
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stop : Machine 1062 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
def bankStates (s : Nat) : List (Fin 4)→Nat
  | []=>1
  | _::ks=>s+bankStates s ks
def bankMachine {s : Nat} (parts : Fin 4→Machine 1062 s) : (ks : List (Fin 4))→Machine 1062 (bankStates s ks)
  | []=>stop
  | k::ks=>Composition.machine (parts k) (bankMachine parts ks)
def banksBudget (cost : Fin 4→Nat) : List (Fin 4)→Nat
  | []=>0
  | k::ks=>cost k+1+banksBudget cost ks

theorem banks_run {s z : Nat} (parts : Fin 4→Machine 1062 s)
    (cost : Fin 4→Nat) (initial : Fin 4→Fin 262→List Bool) (refs : Fin 4→List Bool)
    (advance : ∀ {v : Nat} (k : Fin 4) (ambient : Configuration 1062 v),
      (∀ j,ambient.heads (bankSlots k j)=0) →
      (∀ j,ambient.tapes (bankSlots k j)=initial k j) →
      ∃ r,runFrom (parts k) (cost k) (Composition.restart ambient (parts k).start)=some r ∧
        r.final.tapes (referenceSlot k)=refs k ∧ r.final.heads (referenceSlot k)=0 ∧ r.steps≤cost k ∧
        (∀ l,k≠l → ∀ j,r.final.tapes (bankSlots l j)=ambient.tapes (bankSlots l j) ∧
          r.final.heads (bankSlots l j)=ambient.heads (bankSlots l j))) (ks : List (Fin 4)) (hn : ks.Nodup)
    (ambient : Configuration 1062 z)
    (hh : ∀ k∈ks,∀ j,ambient.heads (bankSlots k j)=0)
    (ht : ∀ k∈ks,∀ j,ambient.tapes (bankSlots k j)=initial k j) :
    ∃ r,runFrom (bankMachine parts ks) (banksBudget cost ks)
      (Composition.restart ambient (bankMachine parts ks).start)=some r ∧
      (∀ k∈ks,r.final.tapes (referenceSlot k)=
        refs k ∧ r.final.heads (referenceSlot k)=0) ∧
      (∀ l,l∉ks → ∀ j,r.final.tapes (bankSlots l j)=ambient.tapes (bankSlots l j) ∧
        r.final.heads (bankSlots l j)=ambient.heads (bankSlots l j)) ∧
      r.steps≤banksBudget cost ks := by
  induction ks generalizing z with
  | nil=>
    obtain ⟨r,hr,hf,hs⟩ := (Timed.refl stop (Composition.restart ambient stop.start)).run (by rfl)
    refine ⟨r,hr,by simp,?_,hs.le⟩
    intro l _ j
    rw [hf]
    exact ⟨rfl,rfl⟩
  | cons k ks ih=>
    have hn' := List.nodup_cons.mp hn
    obtain ⟨first,hf,ft,fh,fs,fkeep⟩ := advance k ambient
      (hh k (by simp)) (ht k (by simp))
    obtain ⟨last,hl,ldone,lkeep,ls⟩ := ih hn'.2 first.final
      (by
        intro l hl j
        rw [(fkeep l (by intro he; subst l; exact hn'.1 hl) j).2]
        exact hh l (by simp [hl]) j)
      (by
        intro l hl j
        rw [(fkeep l (by intro he; subst l; exact hn'.1 hl) j).1]
        exact ht l (by simp [hl]) j)
    have hwhole := Composition.run_join (parts k) (bankMachine parts ks) _ _ _ first last hf hl
    refine ⟨_,hwhole,?_,?_,?_⟩
    · intro l hl
      rcases List.mem_cons.mp hl with he|he
      · subst l
        have hk:=lkeep k hn'.1 0
        exact ⟨hk.1.trans ft,hk.2.trans fh⟩
      · exact ldone l he
    · intro l hl j
      have hne : k≠l := by intro he; subst l; exact hl (by simp)
      have hnot : l∉ks := by intro he; exact hl (by simp [he])
      exact ⟨(lkeep l hnot j).1.trans (fkeep l hne j).1,
        (lkeep l hnot j).2.trans (fkeep l hne j).2⟩
    · change first.steps+1+last.steps≤_
      exact Nat.add_le_add (Nat.add_le_add_right fs 1) ls

end NearCubicWires.RepairSource.RecoveryTseitinReferences.Sequence
