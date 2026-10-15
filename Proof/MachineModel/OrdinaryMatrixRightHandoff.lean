import Proof.MachineModel.OrdinaryMatrixRightHandoffLayout

/-! One physical run from original cell/inner/id records through coordinate
swap, terminator, aggregate rewind, sorting, selection and zero padding. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightHandoff
open LocalBitMultitape SupplierPrinter
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (M U Used Capacity N : ℕ) :=
  (2*(N*(64*M+47)+3)+2)+1+512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2

theorem plane_run {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U)))
    (ho : ∀ inner,(order inner).Perm (List.finRange (U+U)))
    (hi : U+U ≤ 2^M) (hk : Used ≤ 2^M) (hcap : Used ≤ Capacity) (out : List Bool) :
    ∃ actual : ExecutionReceipt 23 (40+sortStates),
      runFrom machine (budget M U Used Capacity (MatrixRightInputs.original payload order).length)
        (input M (2*M) (MatrixRightInputs.original payload order) out U Used ((Capacity-Used)*U))=some actual ∧
      actual.final.tapes 19=out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload)) ∧
      actual.final.heads 19=(out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload))).length ∧
      actual.steps ≤ budget M U Used Capacity (MatrixRightInputs.original payload order).length := by
  let rs := MatrixRightInputs.original payload order
  let req := MatrixRightInputs.request M payload order
  let pad := (Capacity-Used)*U
  obtain ⟨fr,fc,fk,count,_,_,_,_,base,hbase,hbf,hbs⟩ :=
    MatrixCoordinateTranspose.reset_run M (2*M) rs [] [] [] [] (by omega) (by simp) (by simp) (by simp)
  have he := TapeEmbedding.run_embed MatrixCoordinateTranspose.resetMachine (heads out) (tapes out U Used pad) _ _ base hbase
  let first := TapeEmbedding.receipt (heads out) (tapes out U Used pad) base
  obtain ⟨sorted,hsort,hout,hhead,hsteps⟩ := MatrixRightInputs.plane_run M payload order ho hi hk hcap out
  have hh0 : base.final.heads 10=0 := by
    rw [hbf]
    exact MatrixCoordinateTranspose.reset_output_head M (2*M) count rs [] fr fc fk
  have ht0 : base.final.tapes 10=StablePartition.stream req.records := by
    rw [hbf,MatrixCoordinateTranspose.reset_output_tape]
    change MatrixCoordinateTranspose.output M (MatrixRightInputs.original payload order)++[false]=_
    rw [MatrixRightInputs.transposed_words]
    rfl
  let part := MatrixRightSort.input req out U Used pad
  have hentry : RecoveryFocus.config slots first.final.heads first.final.tapes part=
      Composition.restart first.final sortMachine.start := by
    apply WilliamsSourceCrop.focus_same
    · exact selected_heads base.final req out U Used pad hh0
    · exact selected_tapes base.final req out U Used pad ht0
  obtain ⟨last,hl,hlf,hls⟩ := RecoveryFocus.run_config slots (by decide) MatrixRightSort.machine
    first.final.heads first.final.tapes _ part sorted hsort
  rw [hentry] at hl
  have hj := Composition.run_join prefixMachine sortMachine (2*(rs.length*(64*M+47)+3)+2)
    (512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2)
    (TapeEmbedding.config (heads out) (tapes out U Used pad)
      (MatrixCoordinateTranspose.resetInput M (2*M) rs [] [] [] [])) first last he hl
  have hpick : RecoveryFocus.pick slots 19=some 7 := RecoveryFocus.pick_slot slots (by decide) 7
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_,?_⟩
  · change last.final.tapes 19=_
    rw [hlf]
    simp only [RecoveryFocus.config,hpick]
    exact hout
  · change last.final.heads 19=_
    rw [hlf]
    simp only [RecoveryFocus.config,hpick]
    exact hhead
  · change base.steps+1+last.steps ≤ _
    rw [hls]
    dsimp [budget,rs] at hbs ⊢
    omega

end NearCubicWires.RepairOrdinary.MatrixRightHandoff
