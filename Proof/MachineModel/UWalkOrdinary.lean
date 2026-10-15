import Proof.MachineModel.UWalkReady

/-! The accepted walk-numeric producer embedded after the actual initializer.
Only w20, t50, j58, and the witness-created width sentinel73 are active old
tapes. All fresh workspace is97..134; every inactive cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.UWalkOrdinary
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focus_run {u : ℕ} (slot : Fin 42 → Fin u) (hinj : Function.Injective slot)
    (w t j c : ℕ) (hw : 1 ≤ w) (ambientHeads : Fin u → ℕ) (ambientTapes : Fin u → List Bool)
    (hh : ∀ k,ambientHeads (slot k)=UWalkNumbers.heads k)
    (ht : ∀ k,ambientTapes (slot k)=UWalkNumbers.input w t j c k) :
    ∃ r,runFrom (RecoveryFocus.machine slot UWalkNumbers.machine) (UWalkNumbers.budget w t j)
      (RecoveryCalls.restarted (RecoveryFocus.machine slot UWalkNumbers.machine) ambientHeads ambientTapes)=some r ∧
      (∀ k,r.final.tapes (slot k)=UWalkNumbers.afterUnit w t j c k) ∧
      (∀ k,r.final.heads (slot k)=UWalkNumbers.heads k) ∧
      (∀ i,(∀ k,slot k≠i) → r.final.tapes i=ambientTapes i ∧ r.final.heads i=ambientHeads i) ∧
      r.steps ≤ UWalkNumbers.budget w t j := by
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := UWalkNumbers.total_run w t j c hw
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config slot hinj UWalkNumbers.machine
    ambientHeads ambientTapes (UWalkNumbers.budget w t j) _ base hb
  have he := UWitness.focus_config_eq slot hinj (UWalkNumbers.entry w t j c) ambientHeads ambientTapes hh ht
  rw [he] at hr
  refine ⟨r,hr,?_,?_,?_,hrs.trans_le hbs⟩
  · intro k
    simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ hinj,hbt]
  · intro k
    simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ hinj,hbh]
  · intro i hi
    have hn := UWitness.pick_other slot i hi
    simp [hf,RecoveryFocus.config,hn]

def slots (k : Fin 42) : Fin 135 :=
  if k.val=0 then 20 else if k.val=1 then 50 else if k.val=2 then 58
  else if k.val=3 then 73 else ⟨k.val+93,by omega⟩
theorem slot_value (k : Fin 42) : (slots k).val=
    if k.val=0 then 20 else if k.val=1 then 50 else if k.val=2 then 58
    else if k.val=3 then 73 else k.val+93 := by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slot_value,slot_value] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

noncomputable def machine := RecoveryFocus.machine slots UWalkNumbers.machine
noncomputable def entry (heads : Fin 135 → ℕ) (tapes : Fin 135 → List Bool) :=
  RecoveryCalls.restarted machine heads tapes
def Fresh (heads : Fin 135 → ℕ) (tapes : Fin 135 → List Bool) : Prop :=
  ∀ i,97 ≤ i.val → heads i=0 ∧ tapes i=[]

theorem entry_run (w t j c : ℕ) (hw : 1 ≤ w)
    (ambientHeads : Fin 135 → ℕ) (ambientTapes : Fin 135 → List Bool)
    (hh : ambientHeads 20=0 ∧ ambientHeads 50=1 ∧ ambientHeads 58=1 ∧ ambientHeads 73=1)
    (ht : ambientTapes 20=List.replicate w true ∧ ambientTapes 50=CapMachine.counter c t ∧
      ambientTapes 58=CompareMachine.word j ∧ ambientTapes 73=CompareMachine.word w)
    (hfresh : Fresh ambientHeads ambientTapes) :
    ∃ r,runFrom machine (UWalkNumbers.budget w t j) (entry ambientHeads ambientTapes)=some r ∧
      (∀ k,r.final.tapes (slots k)=UWalkNumbers.afterUnit w t j c k) ∧
      (∀ k,r.final.heads (slots k)=UWalkNumbers.heads k) ∧
      (∀ i,(∀ k,slots k≠i) → r.final.tapes i=ambientTapes i ∧ r.final.heads i=ambientHeads i) ∧
      r.steps ≤ UWalkNumbers.budget w t j := by
  have hheads : ∀ k,ambientHeads (slots k)=UWalkNumbers.heads k := by
    intro k
    by_cases h0 : k.val=0
    · have he : k=0 := Fin.ext h0
      subst k
      exact hh.1
    by_cases h1 : k.val=1
    · have he : k=1 := Fin.ext h1
      subst k
      exact hh.2.1
    by_cases h2 : k.val=2
    · have he : k=2 := Fin.ext h2
      subst k
      exact hh.2.2.1
    by_cases h3 : k.val=3
    · have he : k=3 := Fin.ext h3
      subst k
      exact hh.2.2.2
    have hge : 97 ≤ (slots k).val := by rw [slot_value]; simp [h0,h1,h2,h3]; omega
    simpa [UWalkNumbers.heads,UWalkNumbers.selected,h1,h2,h3] using (hfresh _ hge).1
  have htapes : ∀ k,ambientTapes (slots k)=UWalkNumbers.input w t j c k := by
    intro k
    by_cases h0 : k.val=0
    · have he : k=0 := Fin.ext h0
      subst k
      exact ht.1
    by_cases h1 : k.val=1
    · have he : k=1 := Fin.ext h1
      subst k
      exact ht.2.1
    by_cases h2 : k.val=2
    · have he : k=2 := Fin.ext h2
      subst k
      exact ht.2.2.1
    by_cases h3 : k.val=3
    · have he : k=3 := Fin.ext h3
      subst k
      exact ht.2.2.2
    have hge : 97 ≤ (slots k).val := by rw [slot_value]; simp [h0,h1,h2,h3]; omega
    simpa [UWalkNumbers.input,h0,h1,h2,h3] using (hfresh _ hge).2
  exact focus_run slots slots_injective w t j c hw ambientHeads ambientTapes hheads htapes

theorem output_fields (w t j c : ℕ) :
    UWalkNumbers.afterUnit w t j c 18=List.replicate (UWalkCapacity.amount w t j) true ∧
    UWalkNumbers.afterUnit w t j c 19=List.replicate (UWalkCapacity.amount w t j) false ∧
    UWalkNumbers.afterUnit w t j c 20=List.replicate (UWalkCapacity.amount w t j) false ∧
    UWalkNumbers.afterUnit w t j c 21=List.replicate (UWalkCapacity.amount w t j) false ∧
    UWalkNumbers.afterUnit w t j c 22=List.replicate (UWalkCapacity.amount w t j) false ∧
    UWalkNumbers.afterUnit w t j c 23=List.replicate (UWalkCapacity.amount w t j+1) false ∧
    UWalkNumbers.afterUnit w t j c 26=frame (binary w 0) ∧
    UWalkNumbers.afterUnit w t j c 30=frame (binary w 0) ∧
    UWalkNumbers.afterUnit w t j c 34=frame (binary w 0) ∧
    UWalkNumbers.afterUnit w t j c 39=frame (binary w 1) := by
  simp [UWalkNumbers.afterUnit,UWalkNumbers.afterOne,UWalkNumbers.afterZ3,UWalkNumbers.afterZ2,
    UWalkNumbers.afterZ1,UWalkNumbers.afterC,UWalkNumbers.cap_eq]

end NearCubicWires.RepairOrdinary.UWalkOrdinary
