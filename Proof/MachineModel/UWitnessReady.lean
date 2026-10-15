import Proof.MachineModel.UWitnessController

/-! Complete whole witness preparation from the literal witness frame,
physical width/B fields, and blank scratch. -/
namespace NearCubicWires.RepairOrdinary.UWitness
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (w B : ℕ) : 16*w+20+UWitnessChoices.budget w B ≤ budget w B := by
  dsimp [budget,UWitnessChoices.budget,UWitnessChoices.rawBudget,UWitnessChoices.loopBudget]
  nlinarith

theorem total_run (w B : ℕ) (witness : List Bool) (hb : B+1 < 2^w) :
    ∃ r,run machine (budget w B) (input w B witness)=some r ∧
      Outcome w B witness r.final ∧ r.steps ≤ 128*(B+1)*(w+1) := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := boot_run w B witness
  obtain ⟨n,hn,hboot⟩ := call_receipt sizes programs 0 next 0 1 (8*w+10) _ first hfirst (by simp [next])
  have he : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=fieldInput w B witness := by
    rw [hh,ht]
    rfl
  rw [he] at hboot
  obtain ⟨m,final,hm,hfield,hhalt,hout⟩ := field_tail w B witness hb
  have h := hboot.trans hfield
  change Timed machine (n+m) (initialConfiguration machine (input w B witness)) final at h
  obtain ⟨r,hr,hf,hrs⟩ := h.run hhalt
  have hcost : n+m ≤ budget w B := by have := budget_bound w B; omega
  have hmore := run_moreFuel machine (n+m) (budget w B-(n+m)) _ r hr
  rw [Nat.add_sub_of_le hcost] at hmore
  exact ⟨r,hmore,by rwa [hf],by change r.steps ≤ budget w B; omega⟩

theorem successful_prefix (w B : ℕ) (witness : List Bool) (hv : Valid w B witness) :
    ∃ m choices suffix,witness=binary w m++choices++suffix ∧ m ≤ B ∧ choices.length=B ∧
      m=mValue w witness ∧ choices=(witness.drop w).take B ∧ suffix=witness.drop (w+B) := by
  have hmword : witness.take w=binary w (mValue w witness) := by
    have hl : (witness.take w).length=w := by simp [List.length_take,Nat.min_eq_left hv.1]
    simpa [hl,mValue] using (BoundedCounter.binary_of_value (witness.take w)).symm
  refine ⟨mValue w witness,(witness.drop w).take B,witness.drop (w+B),?_,hv.2.1,?_,rfl,rfl,rfl⟩
  · rw [←hmword,←List.drop_drop]
    rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
  · simp only [List.length_take,List.length_drop]
    apply Nat.min_eq_left
    have := hv.2.2
    omega

end NearCubicWires.RepairOrdinary.UWitness
