import Proof.Amplification.RecoveryMarkerHandoffWhole

/-! The actual copies produce the literal existing nested-checker entry
invariant. The retained valuation, table contents, counts and cursors are
the same as before the copies. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_prepared (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre)
    (words : Fin 3→List Bool) (hw : ∀ j,(words j).length=x.inner.base.state.bits.length) :
    RecoveryNestedTable.Prepared (output x words) limit word innerBits outerBits innerPre outerPre := by
  have hin : (output x words).inner.Valid word innerBits := by
    refine ⟨⟨hx.innerValid.1.1,?_,hx.innerValid.1.2.2⟩,hx.innerValid.2⟩
    have he := hx.innerValid.1.2.1
    exact ⟨he.source,he.row,he.counter,hw 2,(hw 1).le,he.cap,he.prefixBound,he.reset⟩
  have hout : (output x words).outer.Valid word outerBits innerBits := by
    refine ⟨hx.outerValid.1,?_⟩
    exact (hw 0).trans hx.copiedWidth.symm
  exact ⟨hin,hout,hx.innerZero,hx.outerZero,hx.innerBound,hx.outerBound,hx.copiedCount,
    hx.copiedWidth,hx.innerSource,hx.innerPos,hx.outerSource,hx.outerPos,hx.innerCapacity,hx.outerCapacity⟩

theorem prepared_bounds (x : CheckState) (limit : Nat)
    (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : RecoveryNestedTable.Prepared x limit word innerBits outerBits innerPre outerPre) :
    (∀ j,(oldWord x j).length ≤ x.inner.base.state.bits.length) ∧
      2*x.inner.base.state.bits.length+1 ≤ x.inner.copyCapacity ∧
      4*x.inner.base.state.bits.length+3 ≤ x.inner.base.state.capacity := by
  refine ⟨?_,hx.innerValid.2.2.2.2.1,?_⟩
  · intro j
    fin_cases j
    · exact (hx.outerValid.2.trans hx.copiedWidth).le
    · exact hx.innerValid.1.2.1.committed
    · exact hx.innerValid.1.2.1.count.le
  · have hr := hx.innerValid.1.2.1.reset
    change 8192*(x.inner.base.state.bits.length+1)^2+1 ≤ x.inner.base.state.capacity at hr
    nlinarith only [hr]

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
