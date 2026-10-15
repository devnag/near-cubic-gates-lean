import Proof.MachineModel.OrdinaryWilliamsTotal

/-! The required local Williams ceiling wrapper, with no prepared-data or
additional source premise. Its ordinary program and runtime are the actual
canonical zero/positive computation proved in WilliamsCall.total_run. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def program (a : WilliamsAlgorithm) : Program where
  tapeCount := tapeCount a
  stateCount := Fintype.card (RecoveryCalls.Control (sizes a))
  twoTapes := by unfold tapeCount; omega
  machine := totalMachine a
  outputTape := outputTape a
  outputFresh := by simp [outputTape,extraSlot]

theorem literal_input (a : WilliamsAlgorithm) (r : RectangularProductRequest) :
    (program a).inputTapes (natWord r.dimension++rowMajorBitMatrix r.left++rowMajorBitMatrix r.right)=input a r := by
  funext i
  simp only [Program.inputTapes,input,WilliamsMetadata.word,WilliamsPayloadCount.payload,List.append_assoc]

noncomputable def realization (a : WilliamsAlgorithm) : WilliamsCeilRealization a where
  coefficient := coefficient a
  logExponent := a.logExponent+1
  coefficientPositive := by unfold coefficient positiveCoefficient; omega
  sourceExponentPaid := by omega
  wrapper := {
    program := program a
    realizes := by
      intro r
      obtain ⟨actual,ha,ho⟩ := total_run a r
      refine ⟨actual,?_,ho⟩
      change run (totalMachine a) (budget a r) ((program a).inputTapes _)=some actual
      rw [literal_input]
      exact ha }

end NearCubicWires.RepairOrdinary.WilliamsCall
