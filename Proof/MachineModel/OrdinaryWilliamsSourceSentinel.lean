import Proof.MachineModel.OrdinaryWilliamsPaddedBuffers
import Proof.MachineModel.OrdinaryWilliamsSourceCropBudget

/-! The already executed source/crop parent on the physical sentinel
drivers produced by the external-input prefix. Its ordinary transition
count and literal integer output are unchanged. -/
namespace NearCubicWires.RepairOrdinary.WilliamsSourceCrop
open LocalBitMultitape RepairRepresentation ExecutableInterfaces SourceInterfaces WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sentinelCapacity (a : WilliamsAlgorithm) (r : RectangularProductRequest) : Fin (tapeCount a) → ℕ :=
  fun i => if i=extra a 3 ∨ i=extra a 5 then r.dimension+2 else 0
noncomputable def sentinelInput (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :=
  ZeroPadding.config (sentinelCapacity a r)
    (Composition.leftConfig MatrixCropRows.stateCount (sourceInput a r hr))

theorem sentinel_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt (tapeCount a) ((a.stateCount+2)+MatrixCropRows.stateCount),
      runFrom (machine a) (budget a r hr) (sentinelInput a r hr)=some actual ∧
      actual.final.tapes (extra a 1)=encodedNatCellTape (natBitLength r.dimension)
        (rowMajorNatMatrix (integerMatrixProduct r.left r.right)) ∧ actual.steps ≤ budget a r hr := by
  obtain ⟨base,hb,ho,_,_,_,hs⟩ := source_crop_run a r hr
  obtain ⟨actual,ha,hf,ht,_⟩ := ZeroPadding.run_config (machine a) (sentinelCapacity a r) _ _ base hb
  refine ⟨actual,ha,?_,ht.trans_le hs⟩
  rw [hf]
  simpa [ZeroPadding.config,sentinelCapacity,extra,Fin.ext_iff,ZeroPadding.pad] using ho

def sentinelExtras (r : RectangularProductRequest) : Fin 6 → List Bool :=
  let v := WilliamsPaddedRequest.dimension r.dimension
  let w := natBitLength v
  let lo := natBitLength r.dimension
  ![UnaryTemplate.tape lo,[],UnaryTemplate.tape (w-lo),UnaryTemplate.tape r.dimension,
    UnaryTemplate.tape ((v-r.dimension)*w),UnaryTemplate.tape r.dimension]

theorem sentinel_extra_heads (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension)
    (i : Fin 6) : (sentinelInput a r hr).heads (extra a i)=extraHeads i := by
  have hn (k : ℕ) : ¬ a.tapeCount+1+k ≤ a.tapeCount := by omega
  simp [sentinelInput,ZeroPadding.config,Composition.leftConfig,sourceInput,TapeEmbedding.config,extra,Fin.addCases,hn]

theorem sentinel_extra_tapes (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension)
    (i : Fin 6) : (sentinelInput a r hr).tapes (extra a i)=sentinelExtras r i := by
  have hn (k : ℕ) : ¬ a.tapeCount+1+k ≤ a.tapeCount := by omega
  fin_cases i <;> simp [sentinelInput,ZeroPadding.config,Composition.leftConfig,sourceInput,TapeEmbedding.config,
    extra,Fin.addCases,sentinelCapacity,Fin.ext_iff,extraTapes,sentinelExtras,ZeroPadding.pad,
    RepairSource.VerifierDecoding.CompareMachine.word,UnaryTemplate.tape,hn]

end NearCubicWires.RepairOrdinary.WilliamsSourceCrop
