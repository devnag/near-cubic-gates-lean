import Proof.MachineModel.OrdinaryMatrixPacketReset
import Proof.MachineModel.OrdinaryMatrixPacketSchedulerBounds
import Proof.MachineModel.OrdinaryMatrixSchedulerTarget
import Proof.Foundations.OrdinaryTapeRenaming

/-! A fixed physical tape relabel puts the retained original request on
ordinary input tape zero. It moves no data and changes no execution cost. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketScheduler
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) (E : ℕ) := MatrixPacketHeader.tapes a E+1
instance (a : WilliamsAlgorithm) (E : ℕ) : NeZero (tapes a E) := ⟨by unfold tapes; omega⟩
noncomputable def rename (a : WilliamsAlgorithm) (E : ℕ) : Fin (tapes a E) ≃ Fin (tapes a E) :=
  Equiv.swap (MatrixPacketReset.original a E) 0

theorem singleton_add {m n : ℕ} (source : Fin m) (bits : List Bool) :
    Fin.addCases (motive := fun _ => List Bool) (fun i : Fin m => if i=source then bits else []) (fun _ : Fin n => [])=
      (fun i : Fin (m+n) => if i=source.castAdd n then bits else []) := by
  funext i
  refine Fin.addCases (m := m) (n := n) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left,Fin.castAdd_inj]
  · have hn : j.natAdd m≠source.castAdd n := by
      intro he
      have hv:=congrArg (fun k : Fin (m+n) => k.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      have h:=source.isLt
      omega
    simp only [Fin.addCases_right,if_neg hn]

theorem input_eq (a : WilliamsAlgorithm) (E : ℕ) (r : Request) :
    MatrixPacketReset.input a E r=(fun i => if i=MatrixPacketReset.original a E then physicalInput r else []) := by
  have h0 : MatrixPacketHeader.input a E r=
      (fun i => if i=MatrixPacketController.original a E then physicalInput r else []) :=
    singleton_add (n := 22) (MatrixPacketRestore.copySlots a E 0) (physicalInput r)
  have h1:=congrArg (fun f : Fin (MatrixPacketHeader.tapes a E) → List Bool =>
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin 1 => [])) h0
  exact h1.trans (singleton_add (n := 1) (MatrixPacketController.original a E) (physicalInput r))

theorem output_ne_original (a : WilliamsAlgorithm) (E : ℕ) :
    MatrixPacketReset.outputTape a E≠MatrixPacketReset.original a E := by
  intro he
  have hv:=congrArg (fun k : Fin (tapes a E) => k.val) he
  exact MatrixPacketRestoreControls.controls_outside a E 2 (MatrixPacketState.output a) (Fin.ext hv)

theorem renamed_fresh (a : WilliamsAlgorithm) (E : ℕ) :
    ((rename a E) (MatrixPacketReset.outputTape a E)).val≠0 := by
  intro hz
  have he : (rename a E) (MatrixPacketReset.outputTape a E)=0 := Fin.ext hz
  have hs : (rename a E) (MatrixPacketReset.original a E)=0 := Equiv.swap_apply_left _ _
  exact output_ne_original a E ((rename a E).injective (he.trans hs.symm))

noncomputable def program (a : WilliamsAlgorithm) (E C : ℕ) : Program where
  tapeCount := tapes a E
  stateCount := MatrixPacketPositive.states (MatrixPacketReset.machine a E C)
  twoTapes := by unfold tapes MatrixPacketHeader.tapes; omega
  machine := TapeRenaming.machine (rename a E) (MatrixPacketReset.machine a E C)
  outputTape := (rename a E) (MatrixPacketReset.outputTape a E)
  outputFresh := renamed_fresh a E

theorem input_rename (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :
    (MatrixPacketReset.input a E r) ∘ (rename a E).symm=(program a E C).inputTapes (word r) := by
  rw [input_eq]
  funext i
  have he : (rename a E).symm i=MatrixPacketReset.original a E ↔ i=0 := by
    rw [Equiv.symm_apply_eq]
    simp only [rename,Equiv.swap_apply_left]
  change (if (rename a E).symm i=MatrixPacketReset.original a E then physicalInput r else [])=
    if i.val=0 then frame (word r) else []
  simp only [he,Fin.ext_iff,Fin.val_zero,physicalInput]

theorem configuration_rename (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :
    TapeRenaming.config (rename a E) (initialConfiguration (MatrixPacketReset.machine a E C) (MatrixPacketReset.input a E r))=
      initialConfiguration (program a E C).machine ((program a E C).inputTapes (word r)) := by
  apply configuration_ext
  · rfl
  · rfl
  · exact input_rename a E C r

end NearCubicWires.RepairOrdinary.MatrixPacketScheduler
