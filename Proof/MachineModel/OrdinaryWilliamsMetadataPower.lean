import Proof.MachineModel.OrdinaryWilliamsPower

/-! The physical metadata producer supplies the factor for ten actual
unary multiplications. This enclosing program starts with the external
request alone and returns U, c and V=c^10 with all cursors restored. -/
namespace NearCubicWires.RepairOrdinary.WilliamsMetadataPower
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev metadataStates := WilliamsMetadata.headerStates+15+WilliamsMetadata.countStates+2
abbrev powerStates := 2+Fintype.card (RecoveryCalls.Control (WilliamsPower.sizes 10))
def slots (i : Fin 22) : Fin 36 := if i.val=0 then 13 else ⟨14+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega
noncomputable def metadata : Machine 36 metadataStates := TapeEmbedding.machine 21 WilliamsMetadata.resetMachine
noncomputable def power : Machine 36 powerStates := RecoveryFocus.machine slots (WilliamsPower.fullMachine 10 (by decide))
noncomputable def machine := Composition.machine metadata power
def input (r : RectangularProductRequest) : Fin 36 → List Bool :=
  fun i => if i=0 then frame (WilliamsMetadata.word r) else []
def Data {s : ℕ} (r : RectangularProductRequest) (cfg : Configuration 36 s) : Prop :=
  cfg.tapes 0=frame (WilliamsMetadata.word r) ∧ cfg.tapes 1=WilliamsMetadata.word r ∧
  cfg.tapes 3=List.replicate (natBitLength r.dimension) true ∧
  cfg.tapes 5=UnaryTemplate.tape (natBitLength r.dimension) ∧
  cfg.tapes 6=frame (binary (natBitLength r.dimension) r.dimension) ∧
  cfg.tapes 12=UnaryTemplate.tape r.dimension ∧
  cfg.tapes 13=UnaryTemplate.tape (rectangularInnerDimension r.dimension) ∧
  cfg.tapes 34=List.replicate (WilliamsPaddedRequest.dimension r.dimension) true

theorem power_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt 36 (metadataStates+powerStates),
      run machine (104000*(r.dimension+1)^2) (input r)=some actual ∧
      Data r actual.final ∧ (∀ i,actual.final.heads i=0) ∧
      actual.steps ≤ 104000*(r.dimension+1)^2 := by
  let c := rectangularInnerDimension r.dimension
  obtain ⟨base,hb,h0,h1,h3,h5,h6,h12,h13,hh,hs⟩ := WilliamsMetadata.reset_run r hr
  have he := TapeEmbedding.run_embed WilliamsMetadata.resetMachine (fun _ : Fin 21 => 0)
    (fun _ : Fin 21 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 21 => 0) (fun _ : Fin 21 => []) base.final
  have ah (i : Fin 36) : ambient.heads i=0 := by
    fin_cases i <;> first | exact hh _ | rfl
  obtain ⟨last,hl,hfactor,hout,hlh,hls⟩ := WilliamsPower.full_run 10 c (by decide)
    (WilliamsPaddedRequest.inner_positive r.dimension hr)
  have hzero : WilliamsPower.factor 10=(0 : Fin 22) := rfl
  rw [hzero] at hfactor
  let entry := initialConfiguration (WilliamsPower.fullMachine 10 (by decide)) (WilliamsPower.input 10 c)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient power.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ah _
    · intro i
      fin_cases i <;> first | exact h13 | rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective
    (WilliamsPower.fullMachine 10 (by decide)) ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hfocus
  have hj := Composition.run_join metadata power (258*(r.dimension+1)^2)
    (WilliamsPower.budget 10 c+2) _
    (TapeEmbedding.receipt (fun _ : Fin 21 => 0) (fun _ : Fin 21 => []) base) focused he hfocus
  have hin : Composition.leftConfig powerStates
      (TapeEmbedding.config (fun _ : Fin 21 => 0) (fun _ : Fin 21 => [])
        (initialConfiguration WilliamsMetadata.resetMachine (WilliamsMetadata.resetInput r))) =
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hbnd : 258*(r.dimension+1)^2+1+(WilliamsPower.budget 10 c+2) ≤ 104000*(r.dimension+1)^2 := by
    have hv := WilliamsPaddedRequest.dimension_le r.dimension hr
    change c^10 ≤ 1024*r.dimension at hv
    unfold WilliamsPower.budget WilliamsPower.stepBudget
    nlinarith
  have hm := run_moreFuel machine _
    (104000*(r.dimension+1)^2-(258*(r.dimension+1)^2+1+(WilliamsPower.budget 10 c+2)))
    (input r) (Composition.joinedReceipt
      (TapeEmbedding.receipt (fun _ : Fin 21 => 0) (fun _ : Fin 21 => []) base) focused) hj
  rw [Nat.add_sub_of_le hbnd] at hm
  have hpick (i : Fin 22) : RecoveryFocus.pick slots (slots i)=some i :=
    RecoveryFocus.pick_slot slots slots_injective i
  have other (i : Fin 36) (hi : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=ambient.tapes i := by rw [hff]; simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 21 => 0) (fun _ : Fin 21 => []) base) focused,hm,?_,?_,?_⟩
  · change Data r (Composition.rightConfig metadataStates focused.final)
    refine ⟨(other 0 (by decide)).trans h0,(other 1 (by decide)).trans h1,
      (other 3 (by decide)).trans h3,(other 5 (by decide)).trans h5,
      (other 6 (by decide)).trans h6,(other 12 (by decide)).trans h12,?_,?_⟩
    · change focused.final.tapes (slots 0)=_
      rw [hff]
      simpa only [RecoveryFocus.config,hpick,c] using hfactor
    · change focused.final.tapes (slots (WilliamsPower.outputTape 10 (by decide)))=_
      rw [hff]
      simpa only [RecoveryFocus.config,hpick,WilliamsPaddedRequest.dimension,c] using hout
  · intro i
    change focused.final.heads i=0
    rw [hff]
    simp only [RecoveryFocus.config]
    split <;> first | exact ah _ | exact hlh _
  · change base.steps+1+focused.steps ≤ _
    rw [hfs]
    omega

end NearCubicWires.RepairOrdinary.WilliamsMetadataPower
