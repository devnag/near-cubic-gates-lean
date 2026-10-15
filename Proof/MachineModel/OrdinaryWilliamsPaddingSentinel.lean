import Proof.MachineModel.OrdinaryMatrixNaturalCursor

/-! Literal pad/serialize call on the sentinel-terminated row-count driver
produced by the preparation controller. The extra terminal blank is carried
through the same real execution; the source machine and its ABI are unchanged. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPadding
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sentinelInput (r : RectangularProductRequest) (pre suffix : List Bool) : Configuration 8 25 :=
  let u := r.dimension
  let c := rectangularInnerDimension u
  let v := WilliamsPaddedRequest.dimension u
  ⟨joinedMachine.start,![1,pre.length,(natWord v).length,1,1,0,1,1],
    ![UnaryTemplate.tape (u*c),pre++rowMajorBitMatrix r.left++rowMajorBitMatrix r.right++suffix,
      natWord v,UnaryTemplate.tape ((v-u)*c),UnaryTemplate.tape u,[],UnaryTemplate.tape (v-u),
      UnaryTemplate.tape c]⟩
def sentinelCapacity (r : RectangularProductRequest) : Fin 8 → ℕ :=
  ![0,0,0,0,0,0,0,rectangularInnerDimension r.dimension+2]

theorem sentinel_run (r : RectangularProductRequest) (pre suffix : List Bool) :
    let v := WilliamsPaddedRequest.dimension r.dimension
    let c := rectangularInnerDimension r.dimension
    ∃ actual : ExecutionReceipt 8 25,
      runFrom joinedMachine (4*v*c+12*c+13) (sentinelInput r pre suffix)=some actual ∧
      actual.final.tapes 2=natWord v++rowMajorBitMatrix (WilliamsPaddedRequest.left r) ∧
      actual.final.tapes 5=rowMajorBitMatrix (WilliamsPaddedRequest.right r) ∧
      actual.steps ≤ 4*v*c+12*c+13 := by
  dsimp only
  obtain ⟨base,hb,h2,h5,_,hs⟩ := joined_run r pre suffix
  obtain ⟨actual,hr,hf,ht,_⟩ := ZeroPadding.run_config joinedMachine (sentinelCapacity r) _ _ base hb
  have hi : ZeroPadding.config (sentinelCapacity r)
      (Composition.leftConfig MatrixPadRows.stateCount (input r pre suffix))=sentinelInput r pre suffix := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,Composition.leftConfig,input,TapeEmbedding.config,
        rightHeads,MatrixPadRow.config,MatrixRawBlock.config,Fin.addCases,sentinelInput]
    · funext i; fin_cases i <;> simp [ZeroPadding.config,Composition.leftConfig,input,TapeEmbedding.config,
        rightTapes,MatrixPadRow.config,MatrixRawBlock.config,Fin.addCases,sentinelInput,sentinelCapacity,
        ZeroPadding.pad,RepairSource.VerifierDecoding.CompareMachine.word,UnaryTemplate.tape]
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,ht.trans_le hs⟩
  · rw [hf]
    simpa [ZeroPadding.config,sentinelCapacity,ZeroPadding.pad] using h2
  · rw [hf]
    simpa [ZeroPadding.config,sentinelCapacity,ZeroPadding.pad] using h5

end NearCubicWires.RepairOrdinary.WilliamsPadding
