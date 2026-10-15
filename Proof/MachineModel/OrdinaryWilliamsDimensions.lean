import Proof.MachineModel.OrdinaryMatrixDimensionBinary

/-! External canonical request to all three dimensions and the exact
binary supported dimension. Unary-to-binary work is quadratic in V;
V<=1024U therefore keeps the entire actual prefix within O(U^2). -/
namespace NearCubicWires.RepairOrdinary.WilliamsDimensions
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev firstStates := WilliamsMetadataPower.metadataStates+WilliamsMetadataPower.powerStates
def slots (i : Fin 10) : Fin 45 := if i.val=0 then 34 else ⟨35+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega
noncomputable def first : Machine 45 firstStates := TapeEmbedding.machine 9 WilliamsMetadataPower.machine
noncomputable def dimensions : Machine 45 31 := RecoveryFocus.machine slots MatrixDimensionBinary.resetMachine
noncomputable def machine := Composition.machine first dimensions
def input (r : RectangularProductRequest) : Fin 45 → List Bool :=
  fun i => if i=0 then frame (WilliamsMetadata.word r) else []
def Data {s : ℕ} (r : RectangularProductRequest) (cfg : Configuration 45 s) : Prop :=
  cfg.tapes 0=frame (WilliamsMetadata.word r) ∧ cfg.tapes 1=WilliamsMetadata.word r ∧
  cfg.tapes 3=List.replicate (natBitLength r.dimension) true ∧
  cfg.tapes 5=UnaryTemplate.tape (natBitLength r.dimension) ∧
  cfg.tapes 6=frame (binary (natBitLength r.dimension) r.dimension) ∧
  cfg.tapes 12=UnaryTemplate.tape r.dimension ∧
  cfg.tapes 13=UnaryTemplate.tape (rectangularInnerDimension r.dimension) ∧
  cfg.tapes 36=List.replicate (WilliamsPaddedRequest.dimension r.dimension) true ∧
  cfg.tapes 37=List.replicate (WilliamsPaddedRequest.dimension r.dimension) true ∧
  cfg.tapes 38=UnaryTemplate.tape (WilliamsPaddedRequest.dimension r.dimension) ∧
  cfg.tapes 40=frame (binary (natBitLength (WilliamsPaddedRequest.dimension r.dimension))
    (WilliamsPaddedRequest.dimension r.dimension)) ∧
  cfg.tapes 43=CompareMachine.word (natBitLength (WilliamsPaddedRequest.dimension r.dimension))

theorem dimensions_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt 45 (firstStates+31),
      run machine (17000000*(r.dimension+1)^2) (input r)=some actual ∧
      Data r actual.final ∧ (∀ i,actual.final.heads i=0) ∧
      actual.steps ≤ 17000000*(r.dimension+1)^2 := by
  let v := WilliamsPaddedRequest.dimension r.dimension
  obtain ⟨base,hb,hd,hh,hs⟩ := WilliamsMetadataPower.power_run r hr
  rcases hd with ⟨h0,h1,h3,h5,h6,h12,h13,h34⟩
  have he := TapeEmbedding.run_embed WilliamsMetadataPower.machine (fun _ : Fin 9 => 0)
    (fun _ : Fin 9 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) base.final
  have ah (i : Fin 45) : ambient.heads i=0 := by
    fin_cases i <;> first | exact hh _ | rfl
  have hvpos : 0<v := lt_of_lt_of_le (by omega : 0<r.dimension) (WilliamsPaddedRequest.dimension_ge r.dimension)
  obtain ⟨last,hl,hl1,hl2,hl3,hl5,hl8,hlh,hls⟩ := MatrixDimensionBinary.reset_run v hvpos
  let entry := initialConfiguration MatrixDimensionBinary.resetMachine (MatrixDimensionBinary.resetInput v)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient dimensions.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ah _
    · intro i; fin_cases i <;> first | exact h34 | rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective
    MatrixDimensionBinary.resetMachine ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hfocus
  have hj := Composition.run_join first dimensions (104000*(r.dimension+1)^2)
    (16*v^2+72*v+32) _
    (TapeEmbedding.receipt (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) base) focused he hfocus
  have hin : Composition.leftConfig 31
      (TapeEmbedding.config (fun _ : Fin 9 => 0) (fun _ : Fin 9 => [])
        (initialConfiguration WilliamsMetadataPower.machine (WilliamsMetadataPower.input r))) =
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hbnd : 104000*(r.dimension+1)^2+1+(16*v^2+72*v+32) ≤ 17000000*(r.dimension+1)^2 := by
    have hv : v ≤ 1024*r.dimension := WilliamsPaddedRequest.dimension_le r.dimension hr
    have hv2 := Nat.pow_le_pow_left hv 2
    nlinarith
  have hm := run_moreFuel machine _
    (17000000*(r.dimension+1)^2-(104000*(r.dimension+1)^2+1+(16*v^2+72*v+32)))
    (input r) (Composition.joinedReceipt
      (TapeEmbedding.receipt (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) base) focused) hj
  rw [Nat.add_sub_of_le hbnd] at hm
  have hpick (i : Fin 10) : RecoveryFocus.pick slots (slots i)=some i :=
    RecoveryFocus.pick_slot slots slots_injective i
  have other (i : Fin 45) (hi : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=ambient.tapes i := by rw [hff]; simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) base) focused,hm,?_,?_,?_⟩
  · change Data r (Composition.rightConfig firstStates focused.final)
    refine ⟨(other 0 (by decide)).trans h0,(other 1 (by decide)).trans h1,
      (other 3 (by decide)).trans h3,(other 5 (by decide)).trans h5,
      (other 6 (by decide)).trans h6,(other 12 (by decide)).trans h12,
      (other 13 (by decide)).trans h13,?_,?_,?_,?_,?_⟩
    · change focused.final.tapes (slots 1)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick,v] using hl1
    · change focused.final.tapes (slots 2)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick,v] using hl2
    · change focused.final.tapes (slots 3)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick,v] using hl3
    · change focused.final.tapes (slots 5)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick,v] using hl5
    · change focused.final.tapes (slots 8)=_
      rw [hff]; simpa only [RecoveryFocus.config,hpick,v] using hl8
  · intro i
    change focused.final.heads i=0
    rw [hff]
    simp only [RecoveryFocus.config]
    split <;> first | exact ah _ | exact hlh _
  · change base.steps+1+focused.steps ≤ _
    rw [hfs]
    omega

end NearCubicWires.RepairOrdinary.WilliamsDimensions
