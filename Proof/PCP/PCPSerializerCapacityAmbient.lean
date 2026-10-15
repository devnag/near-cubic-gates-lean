import Proof.PCP.PCPSerializerCapacityBounds

/-! General finite tape embedding of the cold capacity producer. All inactive
stream tapes and cursors remain exactly at their physical entry positions. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCapacity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focused_run {u : ℕ} (D C : ℕ) (slot : Fin (tapes D) → Fin u)
    (hi : Function.Injective slot) (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (ambientHeads : Fin u → ℕ) (ambientTapes : Fin u → List Bool)
    (hin : ∀ j,ambientTapes (slot j)=input D (pre++FieldList.stream fields++suffix) fields.length j)
    (hh : ∀ j,ambientHeads (slot j)=heads D pre.length j) :
    ∃ r,runFrom (RecoveryFocus.machine slot (machine D C))
      (coefficient D C*((FieldList.stream fields).length+1)^(D+1))
      ⟨(machine D C).start,ambientHeads,ambientTapes⟩=some r ∧
      r.steps ≤ coefficient D C*((FieldList.stream fields).length+1)^(D+1) ∧
      r.final.heads=ambientHeads ∧
      r.final.tapes (slot (old D 0))=pre++FieldList.stream fields++suffix ∧
      r.final.tapes (slot (old D 2))=CompareMachine.word fields.length ∧
      r.final.tapes (slot (old D 1))=List.replicate (FieldList.stream fields).length true ∧
      r.final.tapes (slot (capacitySlot D))=List.replicate (C*((FieldList.stream fields).length+1)^D) true ∧
      ∀ i,(∀ j,slot j≠i) → r.final.tapes i=ambientTapes i := by
  obtain ⟨base,hb,hbs,hbh,hsource,hcount,hB,hC⟩ := capacity_run D C pre fields suffix
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slot hi (machine D C) ambientHeads ambientTapes _ _ base hb
  have he : RecoveryFocus.config slot ambientHeads ambientTapes
      (entry D (machine D C).start (pre++FieldList.stream fields++suffix) pre.length fields.length)=
      (⟨(machine D C).start,ambientHeads,ambientTapes⟩ : Configuration u _) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp]
      | some j =>
        have hij := RecoveryFocus.slot_of_pick slot hp
        simpa only [RecoveryFocus.config,hp,entry] using (hh j).symm.trans (congrArg ambientHeads hij)
    · exact install_existing slot ambientTapes _ hin
  rw [he] at hr
  have hbnd := budget_bound D C (FieldList.stream fields).length
  have hmore := runFrom_moreFuel (RecoveryFocus.machine slot (machine D C)) _
    (coefficient D C*((FieldList.stream fields).length+1)^(D+1)-budget D C (FieldList.stream fields).length) _ r hr
  rw [Nat.add_sub_of_le hbnd] at hmore
  refine ⟨r,hmore,(hs.trans_le hbs).trans hbnd,?_,?_,?_,?_,?_,?_⟩
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [hf,RecoveryFocus.config,hp]
    | some j =>
      have hij := RecoveryFocus.slot_of_pick slot hp
      simpa only [hf,RecoveryFocus.config,hp,hbh] using (hh j).symm.trans (congrArg ambientHeads hij)
  · simpa only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hi] using hsource
  · simpa only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hi] using hcount
  · simpa only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hi] using hB
  · simpa only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hi] using hC
  · intro i hnone
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [hf,RecoveryFocus.config,hp]
    | some j => exact False.elim (hnone j (RecoveryFocus.slot_of_pick slot hp))

end NearCubicWires.RepairOrdinary.PCPSerializerCapacity
