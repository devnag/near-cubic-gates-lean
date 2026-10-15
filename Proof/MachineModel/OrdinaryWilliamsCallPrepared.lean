import Proof.MachineModel.OrdinaryWilliamsSourceEntry

/-! The ready positive source-call boundary is obtained by actual execution
from the external request. The only fresh bank consists of blank work tapes. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev prefixStates := WilliamsPaddedBuffers.firstStates+49+2
abbrev sourceStates (a : WilliamsAlgorithm) := (a.stateCount+2)+MatrixCropRows.stateCount
noncomputable def prefixMachine (a : WilliamsAlgorithm) : Machine (tapeCount a) prefixStates :=
  TapeEmbedding.machine a.tapeCount WilliamsPaddedBuffers.resetMachine
noncomputable def preparedMachine (a : WilliamsAlgorithm) := Composition.machine (prefixMachine a) (bootstrap a)
noncomputable def sourceMachine (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) (WilliamsSourceCrop.machine a)
def input (a : WilliamsAlgorithm) (r : RectangularProductRequest) : Fin (tapeCount a) → List Bool :=
  fun i => if i.val=0 then frame (WilliamsMetadata.word r) else []

def blankExtension {s : ℕ} (a : WilliamsAlgorithm) (cfg : Configuration 95 s) : Configuration (tapeCount a) s :=
  TapeEmbedding.config (fun _ : Fin a.tapeCount => 0) (fun _ : Fin a.tapeCount => []) cfg

theorem input_config (a : WilliamsAlgorithm) (r : RectangularProductRequest) :
    blankExtension a (initialConfiguration WilliamsPaddedBuffers.resetMachine (WilliamsPaddedBuffers.resetInput r)) =
      initialConfiguration (prefixMachine a) (input a r) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 95) (n := a.tapeCount) (fun j => ?_) (fun j => ?_) i
    · simp [blankExtension,TapeEmbedding.config,initialConfiguration]
    · simp [blankExtension,TapeEmbedding.config,initialConfiguration]
  · funext i
    refine Fin.addCases (m := 95) (n := a.tapeCount) (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> rfl
    · simp [blankExtension,TapeEmbedding.config,initialConfiguration,input]

theorem extension_core {s : ℕ} (a : WilliamsAlgorithm) (r : RectangularProductRequest)
    (cfg : Configuration 95 s) (hd : WilliamsPaddedBuffers.Data r cfg (by decide))
    (i : Fin (a.tapeCount+1)) :
    (blankExtension a cfg).tapes (coreSlot a i)=
      if i.val=0 then natWord (WilliamsPaddedRequest.dimension r.dimension)++rowMajorBitMatrix (WilliamsPaddedRequest.left r)
      else if i.val=1 then rowMajorBitMatrix (WilliamsPaddedRequest.right r) else [] := by
  rcases hd with ⟨h87,h89,_,_,_,_,_⟩
  unfold coreSlot
  split_ifs with h0 h1
  · exact h87
  · exact h89
  · have hn : ¬93+i.val<95 := by omega
    simp [blankExtension,TapeEmbedding.config,Fin.addCases,hn]

theorem extension_extra {s : ℕ} (a : WilliamsAlgorithm) (r : RectangularProductRequest)
    (cfg : Configuration 95 s) (hd : WilliamsPaddedBuffers.Data r cfg (by decide)) (i : Fin 6) :
    (blankExtension a cfg).tapes (extraSlot a i)=WilliamsSourceCrop.sentinelExtras r i := by
  rcases hd with ⟨_,_,h5,h51,h12,h81,h85⟩
  have hn : ¬94+a.tapeCount<95 := by have := a.threeTapes; omega
  fin_cases i
  · exact h5
  · simp [blankExtension,TapeEmbedding.config,Fin.addCases,extraSlot,WilliamsSourceCrop.sentinelExtras,hn]
  · exact h51
  · exact h12
  · exact h81
  · exact h85

theorem prepared_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt (tapeCount a) (prefixStates+2),
      run (preparedMachine a) (64000000*(r.dimension+1)^2+2) (input a r)=some actual ∧
      RecoveryFocus.config (slots a) actual.final.heads actual.final.tapes (WilliamsSourceCrop.sentinelInput a r hr)=
        Composition.restart actual.final (sourceMachine a).start ∧
      actual.steps ≤ 64000000*(r.dimension+1)^2+2 := by
  obtain ⟨base,hb,hd,hh,hs⟩ := WilliamsPaddedBuffers.reset_run r hr
  have he := TapeEmbedding.run_embed WilliamsPaddedBuffers.resetMachine (fun _ : Fin a.tapeCount => 0)
    (fun _ : Fin a.tapeCount => []) _ _ base hb
  let ambient := blankExtension a base.final
  have ah (i : Fin (tapeCount a)) : ambient.heads i=0 := by
    refine Fin.addCases (m := 95) (n := a.tapeCount) (fun j => ?_) (fun j => ?_) i
    · simpa [ambient,blankExtension,TapeEmbedding.config] using hh j
    · simp [ambient,blankExtension,TapeEmbedding.config]
  obtain ⟨boot,hboot,hbf,hbs⟩ := bootstrap_run a ambient.tapes
  have hi : Composition.restart ambient (bootstrap a).start=initialConfiguration (bootstrap a) ambient.tapes := by
    apply configuration_ext
    · rfl
    · exact funext ah
    · rfl
  have hboot' : runFrom (bootstrap a) 1 (Composition.restart ambient (bootstrap a).start)=some boot := by
    rw [hi]; exact hboot
  have hj := Composition.run_join (prefixMachine a) (bootstrap a) (64000000*(r.dimension+1)^2) 1 _
    (TapeEmbedding.receipt (fun _ : Fin a.tapeCount => 0) (fun _ : Fin a.tapeCount => []) base) boot he hboot'
  change runFrom (preparedMachine a) _ (Composition.leftConfig 2
    (blankExtension a (initialConfiguration WilliamsPaddedBuffers.resetMachine (WilliamsPaddedBuffers.resetInput r))))=_ at hj
  rw [input_config] at hj
  let actual := Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin a.tapeCount => 0) (fun _ : Fin a.tapeCount => []) base) boot
  refine ⟨actual,hj,?_,?_⟩
  · apply WilliamsSourceCrop.focus_same
    · intro i
      change boot.final.heads (slots a i)=_
      rw [hbf]
      refine Fin.addCases (m := a.tapeCount+1) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [slots_core,WilliamsSourceCrop.sentinel_core_heads]; exact heads_core a j
      · change heads a (slots a (WilliamsSourceCrop.extra a j))=_
        rw [slots_extra]
        exact (heads_extra a j).trans (WilliamsSourceCrop.sentinel_extra_heads a r hr j).symm
    · intro i
      change boot.final.tapes (slots a i)=_
      rw [hbf]
      refine Fin.addCases (m := a.tapeCount+1) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [slots_core,WilliamsSourceCrop.sentinel_core_tapes]; exact extension_core a r base.final hd j
      · change ambient.tapes (slots a (WilliamsSourceCrop.extra a j))=_
        rw [slots_extra]
        exact (extension_extra a r base.final hd j).trans (WilliamsSourceCrop.sentinel_extra_tapes a r hr j).symm
  · change base.steps+1+boot.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.WilliamsCall
