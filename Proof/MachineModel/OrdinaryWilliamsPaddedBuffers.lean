import Proof.MachineModel.OrdinaryWilliamsPaddingBuffers

/-! From the external request alone, construct both exact-power source
buffers and retain the five physical crop drivers. The complete input,
dimension, arithmetic, header and padding work is included in the budget. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPaddedBuffers
open LocalBitMultitape RecoveryRootRound RepairRepresentation SignedSortKey SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev firstStates := WilliamsPreparation.firstStates+WilliamsPreparation.templateStates
def slots : Fin 14 → Fin 94 := ![61,1,87,71,12,89,49,13,5,47,90,91,92,93]
noncomputable def first : Machine 94 firstStates := TapeEmbedding.machine 5 WilliamsPreparation.machine
noncomputable def pad := RecoveryFocus.machine slots WilliamsPaddingBuffers.machine
noncomputable def machine := Composition.machine first pad
def input (r : RectangularProductRequest) : Fin 94 → List Bool :=
  fun i => if i=0 then frame (WilliamsMetadata.word r) else []
def Data {t s : ℕ} (r : RectangularProductRequest) (cfg : Configuration t s) (ht : 90 ≤ t) : Prop :=
  cfg.tapes ⟨87,by omega⟩=natWord (WilliamsPaddedRequest.dimension r.dimension)++rowMajorBitMatrix (WilliamsPaddedRequest.left r) ∧
  cfg.tapes ⟨89,by omega⟩=rowMajorBitMatrix (WilliamsPaddedRequest.right r) ∧
  cfg.tapes ⟨5,by omega⟩=UnaryTemplate.tape (natBitLength r.dimension) ∧
  cfg.tapes ⟨51,by omega⟩=UnaryTemplate.tape (natBitLength (WilliamsPaddedRequest.dimension r.dimension)-natBitLength r.dimension) ∧
  cfg.tapes ⟨12,by omega⟩=UnaryTemplate.tape r.dimension ∧
  cfg.tapes ⟨81,by omega⟩=UnaryTemplate.tape ((WilliamsPaddedRequest.dimension r.dimension-r.dimension)*natBitLength (WilliamsPaddedRequest.dimension r.dimension)) ∧
  cfg.tapes ⟨85,by omega⟩=UnaryTemplate.tape r.dimension

theorem pad_budget (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    WilliamsPaddingBuffers.budget r ≤ 20000*(r.dimension+1)^2 := by
  let u := r.dimension
  let c := rectangularInnerDimension u
  let v := WilliamsPaddedRequest.dimension u
  have hc : c ≤ u := WilliamsPaddedRequest.inner_le u
  have hv : v ≤ 1024*u := WilliamsPaddedRequest.dimension_le u hr
  have hwu : natBitLength u ≤ u+1 := Nat.add_le_add_right (Nat.log_le_self 2 u) 1
  have hwv : natBitLength v ≤ v+1 := Nat.add_le_add_right (Nat.log_le_self 2 v) 1
  have hvc : v*c ≤ (1024*u)*u := Nat.mul_le_mul hv hc
  change 4*u+3*natBitLength u+3*natBitLength v+4*v*c+12*c+40 ≤ _
  nlinarith

theorem buffers_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt 94 (firstStates+49),
      run machine (31000000*(r.dimension+1)^2) (input r)=some actual ∧
      Data r actual.final (by decide) ∧ actual.steps ≤ 31000000*(r.dimension+1)^2 := by
  obtain ⟨base,hb,hd,hh,hs⟩ := WilliamsPreparation.preparation_run r hr
  rcases hd with ⟨_,hword,orig,hdelta,hgap,hused,hpad,htail,hdup,hheader⟩
  rcases orig with ⟨hu,hc,_,hwu,_,_,hwv⟩
  have he := TapeEmbedding.run_embed WilliamsPreparation.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  have ah (i : Fin 94) : ambient.heads i=0 := by fin_cases i <;> first | exact hh _ | rfl
  obtain ⟨last,hl,hl2,hl5,hl4,hl8,hls⟩ := WilliamsPaddingBuffers.buffers_run r
  let entry := initialConfiguration WilliamsPaddingBuffers.machine (WilliamsPaddingEntry.input r)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry=Composition.restart ambient pad.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ah _
    · intro i; fin_cases i
      · exact hused
      · exact hword
      · exact hheader
      · exact hpad
      · exact hu
      · rfl
      · exact hdelta
      · exact hc
      · exact hwu
      · exact hwv
      all_goals rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) WilliamsPaddingBuffers.machine
    ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hfocus
  have hj := Composition.run_join first pad (30000000*(r.dimension+1)^2)
    (WilliamsPaddingBuffers.budget r) _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused he hfocus
  have hin : Composition.leftConfig 49
      (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
        (initialConfiguration WilliamsPreparation.machine (WilliamsPreparation.input r))) =
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hbnd : 30000000*(r.dimension+1)^2+1+WilliamsPaddingBuffers.budget r ≤ 31000000*(r.dimension+1)^2 := by
    have ht := pad_budget r hr
    nlinarith
  have hm := run_moreFuel machine _
    (31000000*(r.dimension+1)^2-(30000000*(r.dimension+1)^2+1+WilliamsPaddingBuffers.budget r))
    (input r) (Composition.joinedReceipt
      (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused) hj
  rw [Nat.add_sub_of_le hbnd] at hm
  have hpick (i : Fin 14) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  have other (i : Fin 94) (hi : RecoveryFocus.pick slots i=none) : focused.final.tapes i=ambient.tapes i := by
    rw [hff]; simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused,hm,?_,?_⟩
  · change Data r (Composition.rightConfig firstStates focused.final) (by decide)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · change focused.final.tapes (slots 2)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl2
    · change focused.final.tapes (slots 5)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl5
    · change focused.final.tapes (slots 8)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl8
    · exact (other 51 (by decide)).trans hgap
    · change focused.final.tapes (slots 4)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl4
    · exact (other 81 (by decide)).trans htail
    · exact (other 85 (by decide)).trans hdup
  · change base.steps+1+focused.steps ≤ _
    rw [hfs]
    omega

noncomputable def resetMachine := Rewind.machine machine
def resetInput (r : RectangularProductRequest) : Fin 95 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (94+1) => List Bool) (input r) (fun _ : Fin 1 => [])

theorem reset_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt 95 (firstStates+49+2),
      run resetMachine (64000000*(r.dimension+1)^2) (resetInput r)=some actual ∧
      Data r actual.final (by decide) ∧ (∀ i,actual.final.heads i=0) ∧
      actual.steps ≤ 64000000*(r.dimension+1)^2 := by
  obtain ⟨base,hb,hd,hs⟩ := buffers_run r hr
  obtain ⟨actual,ha,ht,hh,hsteps,_⟩ := Rewind.reset_run machine _ (input r) base hb
  have hbound : 2*base.steps+2 ≤ 64000000*(r.dimension+1)^2 := by nlinarith
  have hm := run_moreFuel resetMachine (2*base.steps+2)
    (64000000*(r.dimension+1)^2-(2*base.steps+2)) (resetInput r) actual ha
  rw [Nat.add_sub_of_le hbound] at hm
  rcases hd with ⟨h87,h89,h5,h51,h12,h81,h85⟩
  exact ⟨actual,hm,⟨(ht 87).trans h87,(ht 89).trans h89,(ht 5).trans h5,(ht 51).trans h51,
    (ht 12).trans h12,(ht 81).trans h81,(ht 85).trans h85⟩,hh,hsteps.trans_le hbound⟩

end NearCubicWires.RepairOrdinary.WilliamsPaddedBuffers
