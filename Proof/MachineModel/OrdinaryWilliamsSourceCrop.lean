import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! Execute the selected corrected Williams program and crop that same
execution's literal output. Inputs are the actual padded source matrices
and dimension templates; producing them is the remaining wrapper prefix. -/
namespace NearCubicWires.RepairOrdinary.WilliamsSourceCrop
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
open SourceInterfaces WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) : ℕ :=
  2 * WilliamsReplay.budget a (WilliamsPaddedRequest.request r hr) +
    WilliamsCrop.budget r.dimension (WilliamsPaddedRequest.dimension r.dimension)
      (natBitLength (WilliamsPaddedRequest.dimension r.dimension)) + 3

theorem source_crop_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    let result := encodedNatCellTape (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right))
    ∃ actual : ExecutionReceipt (tapeCount a) ((a.stateCount + 2) + MatrixCropRows.stateCount),
      runFrom (machine a) (budget a r hr)
        (Composition.leftConfig MatrixCropRows.stateCount (sourceInput a r hr)) = some actual ∧
      actual.final.tapes (extra a 1) = result ∧ actual.final.heads (extra a 1) = result.length ∧
      actual.final.tapes (sourceTape a) = (WilliamsPaddedRequest.request r hr).output ∧
      actual.final.heads (sourceTape a) = r.dimension * (WilliamsPaddedRequest.dimension r.dimension *
        natBitLength (WilliamsPaddedRequest.dimension r.dimension)) ∧
      actual.steps ≤ budget a r hr := by
  dsimp only
  let req := WilliamsPaddedRequest.request r hr
  let sourceFuel := 2 * WilliamsReplay.budget a req + 2
  let cropFuel := WilliamsCrop.budget r.dimension (WilliamsPaddedRequest.dimension r.dimension)
    (natBitLength (WilliamsPaddedRequest.dimension r.dimension))
  obtain ⟨source, reset, _, hreset, hout, hh, _, _, hsteps, _⟩ := WilliamsReplay.source_run a req
  have he := TapeEmbedding.run_embed (WilliamsReplay.machine a) extraHeads (extraTapes r) sourceFuel _ reset hreset
  let ambient : Configuration (tapeCount a) (a.stateCount + 2) :=
    TapeEmbedding.config extraHeads (extraTapes r) reset.final
  obtain ⟨cropped, hc, hcf, hcs⟩ := WilliamsCrop.request_run r hr []
  obtain ⟨focused, hfocus, hff, hfs⟩ := RecoveryFocus.run_config (slot a) (slot_injective a)
    MatrixCropRows.machine ambient.heads ambient.tapes cropFuel (cropInput r hr) cropped hc
  have hjump := handoff a r hr reset.final hh hout
  have hjump' : RecoveryFocus.config (slot a) ambient.heads ambient.tapes (cropInput r hr) =
      Composition.restart ambient (cropProgram a).start := hjump
  have hfocus' : runFrom (cropProgram a) cropFuel
      (Composition.restart (TapeEmbedding.receipt extraHeads (extraTapes r) reset).final (cropProgram a).start) = some focused := by
    change runFrom (cropProgram a) cropFuel (Composition.restart ambient (cropProgram a).start) = _
    rw [← hjump']
    exact hfocus
  have hj := Composition.run_join (sourceProgram a) (cropProgram a) sourceFuel cropFuel _
    (TapeEmbedding.receipt extraHeads (extraTapes r) reset) focused he hfocus'
  let actual := Composition.joinedReceipt (TapeEmbedding.receipt extraHeads (extraTapes r) reset) focused
  have htime : sourceFuel + 1 + cropFuel = budget a r hr := by dsimp [sourceFuel, cropFuel, budget, req]; omega
  have hread (j : Fin 7) : RecoveryFocus.pick (slot a) (slot a j) = some j := RecoveryFocus.pick_slot _ (slot_injective a) j
  have houtSlot : extra a 1 = slot a 2 := rfl
  have hsourceSlot : sourceTape a = slot a 1 := rfl
  refine ⟨actual, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · change (Composition.rightConfig (a.stateCount + 2) focused.final).tapes (extra a 1) = _
    rw [hff, hcf, houtSlot]
    simp [Composition.rightConfig, RecoveryFocus.config, hread, MatrixCropRows.config, MatrixCropRow.config,
      MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, TapeEmbedding.config, Fin.addCases]
  · change (Composition.rightConfig (a.stateCount + 2) focused.final).heads (extra a 1) = _
    rw [hff, hcf, houtSlot]
    simp [Composition.rightConfig, RecoveryFocus.config, hread, MatrixCropRows.config, MatrixCropRow.config,
      MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, TapeEmbedding.config, Fin.addCases]
  · change (Composition.rightConfig (a.stateCount + 2) focused.final).tapes (sourceTape a) = _
    rw [hff, hcf, hsourceSlot]
    simp [Composition.rightConfig, RecoveryFocus.config, hread, MatrixCropRows.config, MatrixCropRow.config,
      MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, TapeEmbedding.config, Fin.addCases]
  · change (Composition.rightConfig (a.stateCount + 2) focused.final).heads (sourceTape a) = _
    rw [hff, hcf, hsourceSlot]
    simp [Composition.rightConfig, RecoveryFocus.config, hread, MatrixCropRows.config, MatrixCropRow.config,
      MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, TapeEmbedding.config, Fin.addCases]
  · change reset.steps + 1 + focused.steps ≤ _
    dsimp only [budget]
    rw [hfs]
    dsimp only [sourceFuel, cropFuel, req] at hsteps hcs
    omega

end NearCubicWires.RepairOrdinary.WilliamsSourceCrop
