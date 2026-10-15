import Proof.Circuits.DecompositionLayout

/-! Actual original-input capacity and native header/count preparation. The
two producers share the retained original source and use disjoint work. -/
namespace NearCubicWires.RepairOrdinary.DecompositionColdPrepare
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepare_run (D C a m : ℕ) (tail : List Bool) :
    ∃ r,run (machine D C) (budget D C a m tail) (input D (DecompositionInputCounts.word a m tail))=some r ∧
      r.final.tapes (headerSlot D 0)=frame (DecompositionInputCounts.word a m tail) ∧
      r.final.heads (headerSlot D 0)=0 ∧
      r.final.tapes (headerSlot D 1)=DecompositionInputCounts.word a m tail ∧
      r.final.heads (headerSlot D 1)=(RepairRepresentation.natWord a++RepairRepresentation.natWord m).length ∧
      (∀ j,r.final.tapes (headerSlot D (DecompositionInputDrivers.slots j))=DecompositionCountDrivers.output a m j) ∧
      (∀ j,r.final.heads (headerSlot D (DecompositionInputDrivers.slots j))=DecompositionCountPosition.loopHeads j) ∧
      r.final.tapes (capacitySlot D)=List.replicate (C*((frame (DecompositionInputCounts.word a m tail)).length+1)^D) true ∧
      r.final.heads (capacitySlot D)=0 ∧ r.steps ≤ budget D C a m tail := by
  obtain ⟨base,hbase,bh,b0,_,bC,bs⟩ := DecompositionCapacity.capacity_cold D C (DecompositionInputCounts.word a m tail)
  let prep := TapeEmbedding.receipt (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) base
  have hp := TapeEmbedding.run_embed (DecompositionCapacity.machine D C)
    (fun _ : Fin 34 => 0) (fun _ : Fin 34 => []) _ _ base hbase
  have oldT (i : Fin (PCPSerializerCapacity.tapes D)) : prep.final.tapes (old D i)=base.final.tapes i := by
    simp only [old,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldH (i : Fin (PCPSerializerCapacity.tapes D)) : prep.final.heads (old D i)=base.final.heads i := by
    simp only [old,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have pt (j : Fin 35) : prep.final.tapes (headerSlot D j)=DecompositionInputDrivers.input a m tail j := by
    rw [header_input]
    by_cases hj : j.val=0
    · rw [if_pos hj]
      have he : j=0 := Fin.ext hj
      subst j
      exact (oldT _).trans b0
    · simp only [headerSlot,hj,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have ph (j : Fin 35) : prep.final.heads (headerSlot D j)=0 := by
    by_cases hj : j.val=0
    · have he : j=0 := Fin.ext hj
      subst j
      rw [show prep.final.heads (headerSlot D 0)=base.final.heads (PCPSerializerCapacity.old D 0) from oldH _]
      rw [bh]
      rfl
    · simp only [headerSlot,hj,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  obtain ⟨body,hbody,bt0,bh0,bt1,bh1,btj,bhj,bodySteps⟩ := DecompositionInputDrivers.drivers_run a m tail
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config (headerSlot D) (headerSlot_injective D)
    DecompositionInputDrivers.machine prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config (headerSlot D) prep.final.heads prep.final.tapes
      (initialConfiguration DecompositionInputDrivers.machine (DecompositionInputDrivers.input a m tail))=
      Composition.restart prep.final (header D).start := by
    apply WilliamsSourceCrop.focus_same
    · exact ph
    · exact pt
  rw [he] at hcall
  have whole := Composition.run_join (first D C) (header D) _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 34 => 0)
      (fun _ : Fin 34 => []) (initialConfiguration (DecompositionCapacity.machine D C)
        (DecompositionCapacity.input D (frame (DecompositionInputCounts.word a m tail)) [])))=
      initialConfiguration (machine D C) (input D (DecompositionInputCounts.word a m tail)) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPSerializerCapacity.tapes D) (n:=34) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,initialConfiguration]
      · simp only [Composition.leftConfig,TapeEmbedding.config,Fin.addCases_right,initialConfiguration]
    · rfl
  rw [hin] at whole
  have ot (j : Fin 35) : called.final.tapes (headerSlot D j)=body.final.tapes j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (headerSlot D) (headerSlot_injective D)]
  have oh (j : Fin 35) : called.final.heads (headerSlot D j)=body.final.heads j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (headerSlot D) (headerSlot_injective D)]
  have noCapacity : RecoveryFocus.pick (headerSlot D) (capacitySlot D)=none := by
    have hn : ¬∃ j,headerSlot D j=capacitySlot D := by
      rintro ⟨j,hj⟩
      exact headerSlot_ne_capacity D j hj
    simp only [RecoveryFocus.pick,dif_neg hn]
  refine ⟨Composition.joinedReceipt prep called,whole,(ot 0).trans bt0,(oh 0).trans bh0,
    (ot 1).trans bt1,(oh 1).trans bh1,?_,?_,?_,?_,?_⟩
  · intro j; exact (ot _).trans (btj j)
  · intro j; exact (oh _).trans (bhj j)
  · change called.final.tapes (capacitySlot D)=_
    rw [cf]
    simp only [RecoveryFocus.config,noCapacity]
    exact (oldT _).trans bC
  · change called.final.heads (capacitySlot D)=0
    rw [cf]
    simp only [RecoveryFocus.config,noCapacity]
    rw [show prep.final.heads (capacitySlot D)=base.final.heads (PCPSerializerCapacity.capacitySlot D) from oldH _]
    rw [bh]
    exact PCPSerializerCapacity.power_heads D 0 _
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionColdPrepare
