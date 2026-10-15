import Proof.MachineModel.OrdinaryWilliamsCallPrepared

/-! Actual positive-dimension external-input computation: physical metadata,
padding, supplied source execution, replay and crop on the same buffers. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positiveMachine (a : WilliamsAlgorithm) := Composition.machine (preparedMachine a) (sourceMachine a)
def positiveBudget (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :=
  64000000*(r.dimension+1)^2+3+WilliamsSourceCrop.budget a r hr

theorem positive_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    ∃ actual : ExecutionReceipt (tapeCount a) ((prefixStates+2)+sourceStates a),
      run (positiveMachine a) (positiveBudget a r hr) (input a r)=some actual ∧
      actual.final.tapes (outputTape a)=encodedNatCellTape (natBitLength r.dimension)
        (rowMajorNatMatrix (integerMatrixProduct r.left r.right)) ∧ actual.steps ≤ positiveBudget a r hr := by
  obtain ⟨prepared,hp,hi,hps⟩ := prepared_run a r hr
  obtain ⟨source,hs,ho,hss⟩ := WilliamsSourceCrop.sentinel_run a r hr
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a)
    (WilliamsSourceCrop.machine a) prepared.final.heads prepared.final.tapes _ _ source hs
  rw [hi] at hf
  have hj := Composition.run_join (preparedMachine a) (sourceMachine a)
    (64000000*(r.dimension+1)^2+2) (WilliamsSourceCrop.budget a r hr) _ prepared focused hp hf
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_⟩
  · change focused.final.tapes (outputTape a)=_
    have hout : outputTape a=slots a (WilliamsSourceCrop.extra a 1) := (slots_extra a 1).symm
    rw [hff,hout]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)] using ho
  · change prepared.steps+1+focused.steps ≤ _
    rw [hfs]
    unfold positiveBudget
    omega

def positiveCoefficient (a : WilliamsAlgorithm) := 64000003+WilliamsSourceCrop.coefficient a

theorem positive_budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    positiveBudget a r hr ≤ positiveCoefficient a*(r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1) := by
  have hc := WilliamsSourceCrop.whole_budget a r hr
  have hl : 1 ≤ (logScale r.dimension+1)^(a.logExponent+1) := Nat.one_le_pow _ _ (by omega)
  have hsq : 1 ≤ (r.dimension+1)^2 := by nlinarith
  have hbase : (r.dimension+1)^2 ≤ (r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1) := by nlinarith
  have hterm : 1 ≤ (r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1) := hsq.trans hbase
  unfold positiveBudget positiveCoefficient
  nlinarith

end NearCubicWires.RepairOrdinary.WilliamsCall
