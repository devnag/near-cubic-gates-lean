import Proof.Amplification.RecoveryOuterRowReadChecked

/-! Retention at the successful outer-row boundary: the original outer
stream advances once, its prior count stays fixed, and the inner driver is
unchanged while its lookup scratch is reused. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem leaf_retains (x : State) (bits : List Bool) : Retains (leafOutput x bits).outer x.outer := by
  unfold leafOutput
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem row_retains (x : State) (bits innerBits : List Bool) : Retains (rowOutput x bits innerBits).outer x.outer := by
  unfold rowOutput
  split
  · exact retains_trans _ (structured x bits).outer x.outer (leaf_retains (structured x bits) innerBits)
      (structure_retained x.outer bits)
  · exact structure_retained x.outer bits

theorem row_inner_driver (x : State) (bits innerBits : List Bool) :
    (rowOutput x bits innerBits).total=x.total ∧ (rowOutput x bits innerBits).capacity=x.capacity := by
  unfold rowOutput
  split
  · unfold leafOutput
    split <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem read_output_retained (x : State) (outerBits innerBits input : List Bool)
    (hi : 4*x.outer.base.state.bits.length ≤ input.length) :
    (readRowOutput x outerBits innerBits input).outer.base.source=x.outer.base.source ∧
    (readRowOutput x outerBits innerBits input).outer.base.pos=x.outer.base.pos+8*x.outer.base.state.bits.length ∧
    (readRowOutput x outerBits innerBits input).outer.total=x.outer.total ∧
    (readRowOutput x outerBits innerBits input).outer.copyCapacity=x.outer.copyCapacity ∧
    (readRowOutput x outerBits innerBits input).outer.lookupCapacity=x.outer.lookupCapacity ∧
    (readRowOutput x outerBits innerBits input).outer.base.state.bits.length=x.outer.base.state.bits.length ∧
    (readRowOutput x outerBits innerBits input).outer.base.extra=x.outer.base.extra ∧
    (readRowOutput x outerBits innerBits input).total=x.total ∧
    (readRowOutput x outerBits innerBits input).capacity=x.capacity := by
  have h := row_retains (readState x input) outerBits innerBits
  have hj := row_inner_driver (readState x input) outerBits innerBits
  exact ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2,
    (congrArg List.length h.1).trans (afterRead_width x.outer.base input hi),h.2.2.1,hj.1,hj.2⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
