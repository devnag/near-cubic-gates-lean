import Proof.MachineModel.OrdinaryWilliamsTemplates

/-! The complete external-request metadata and template producer. Every
dimension, product, difference, duplicate and source header comes from the
same input execution; only the original external framed request is given. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPreparation
open LocalBitMultitape RecoveryRootRound RepairRepresentation SignedSortKey SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev firstStates := WilliamsDimensions.firstStates+31
abbrev templateStates := Fintype.card (RecoveryCalls.Control WilliamsTemplates.sizes)
def slots (i : Fin 50) : Fin 89 :=
  if h : i.val<6 then (![12,13,38,5,43,40] : Fin 6 → Fin 89) ⟨i.val,h⟩ else ⟨39+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first : Machine 89 firstStates := TapeEmbedding.machine 44 WilliamsDimensions.machine
noncomputable def templates : Machine 89 templateStates := RecoveryFocus.machine slots WilliamsTemplates.machine
noncomputable def machine := Composition.machine first templates
def input (r : RectangularProductRequest) : Fin 89 → List Bool :=
  fun i => if i=0 then frame (WilliamsMetadata.word r) else []
def Data {s : ℕ} (r : RectangularProductRequest) (cfg : Configuration 89 s) : Prop :=
  cfg.tapes 0=frame (WilliamsMetadata.word r) ∧ cfg.tapes 1=WilliamsMetadata.word r ∧
  WilliamsTemplates.Data r.dimension (rectangularInnerDimension r.dimension)
    (WilliamsPaddedRequest.dimension r.dimension) (fun i => cfg.tapes (slots i))

theorem templates_budget (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    WilliamsTemplates.budget r.dimension (rectangularInnerDimension r.dimension)
      (WilliamsPaddedRequest.dimension r.dimension) ≤ 12000000*(r.dimension+1)^2 := by
  let u := r.dimension
  let c := rectangularInnerDimension u
  let v := WilliamsPaddedRequest.dimension u
  let w := natBitLength v
  have hc : c ≤ u := WilliamsPaddedRequest.inner_le u
  have hv : v ≤ 1024*u := WilliamsPaddedRequest.dimension_le u hr
  have hw : w ≤ v+1 := Nat.add_le_add_right (Nat.log_le_self 2 v) 1
  have hd : v-u ≤ v := Nat.sub_le _ _
  have huc : u*c ≤ u*u := Nat.mul_le_mul_left u hc
  have hdc : (v-u)*c ≤ v*u := Nat.mul_le_mul hd hc
  have hdw : (v-u)*w ≤ v*(v+1) := Nat.mul_le_mul hd hw
  have hvu : v*u ≤ (1024*u)*u := Nat.mul_le_mul_right u hv
  have hv2 := Nat.pow_le_pow_left hv 2
  change 8*u*c+8*(v-u)*c+8*(v-u)*w+14*u+20*(v-u)+2*v+12*w+138 ≤ _
  nlinarith

theorem preparation_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt 89 (firstStates+templateStates),
      run machine (30000000*(r.dimension+1)^2) (input r)=some actual ∧
      Data r actual.final ∧ (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ 30000000*(r.dimension+1)^2 := by
  let u := r.dimension
  let c := rectangularInnerDimension u
  let v := WilliamsPaddedRequest.dimension u
  obtain ⟨base,hb,hd,hh,hs⟩ := WilliamsDimensions.dimensions_run r hr
  rcases hd with ⟨h0,h1,_,h5,_,h12,h13,_,_,h38,h40,h43⟩
  have he := TapeEmbedding.run_embed WilliamsDimensions.machine (fun _ : Fin 44 => 0)
    (fun _ : Fin 44 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 44 => 0) (fun _ : Fin 44 => []) base.final
  have ah (i : Fin 89) : ambient.heads i=0 := by fin_cases i <;> first | exact hh _ | rfl
  obtain ⟨out,lastReady,hout⟩ := WilliamsTemplates.preparation_ready u c v (WilliamsPaddedRequest.dimension_ge u)
  obtain ⟨last,hl,hlt,hlh,hls⟩ := lastReady
  let entry := initialConfiguration WilliamsTemplates.machine (WilliamsTemplates.input u c v)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient templates.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact ah _
    · intro i
      fin_cases i <;> first | exact h12 | exact h13 | exact h38 | exact h5 | exact h43 | exact h40 | rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective
    WilliamsTemplates.machine ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hfocus
  have hj := Composition.run_join first templates (17000000*(u+1)^2)
    (WilliamsTemplates.budget u c v) _
    (TapeEmbedding.receipt (fun _ : Fin 44 => 0) (fun _ : Fin 44 => []) base) focused he hfocus
  have hin : Composition.leftConfig templateStates
      (TapeEmbedding.config (fun _ : Fin 44 => 0) (fun _ : Fin 44 => [])
        (initialConfiguration WilliamsDimensions.machine (WilliamsDimensions.input r))) =
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hbnd : 17000000*(u+1)^2+1+WilliamsTemplates.budget u c v ≤ 30000000*(u+1)^2 := by
    have ht : WilliamsTemplates.budget u c v ≤ 12000000*(u+1)^2 := templates_budget r hr
    nlinarith
  have hm := run_moreFuel machine _
    (30000000*(u+1)^2-(17000000*(u+1)^2+1+WilliamsTemplates.budget u c v))
    (input r) (Composition.joinedReceipt
      (TapeEmbedding.receipt (fun _ : Fin 44 => 0) (fun _ : Fin 44 => []) base) focused) hj
  rw [Nat.add_sub_of_le hbnd] at hm
  have other (i : Fin 89) (hi : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=ambient.tapes i := by rw [hff]; simp only [RecoveryFocus.config,hi]
  have projected : (fun i => focused.final.tapes (slots i))=out := by
    funext i
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    rw [hlt]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 44 => 0) (fun _ : Fin 44 => []) base) focused,hm,?_,?_,?_⟩
  · change Data r (Composition.rightConfig firstStates focused.final)
    refine ⟨(other 0 (by decide)).trans h0,(other 1 (by decide)).trans h1,?_⟩
    change WilliamsTemplates.Data u c v (fun i => focused.final.tapes (slots i))
    rw [projected]
    exact hout
  · intro i
    change focused.final.heads i=0
    rw [hff]
    simp only [RecoveryFocus.config]
    split <;> first | exact ah _ | exact hlh _
  · change base.steps+1+focused.steps ≤ _
    rw [hfs,hls]
    dsimp only [u] at hbnd ⊢
    omega

end NearCubicWires.RepairOrdinary.WilliamsPreparation
