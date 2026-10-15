import Proof.Amplification.RecoveryNestedTableSemantics

namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outer_run (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word innerBits outerBits innerPre outerPre)
    (ha : innerAnswer x word innerBits=true) :
    ∃ r,runFrom RecoveryOuterRoot.wholeMachine
        (RecoveryOuterRoot.wholeBudget x.outer.data.outer.base.state.bits.length limit x.outer.total)
        (x.outer.cfg RecoveryOuterRoot.wholeMachine.start)=some r ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[answer x word innerBits outerBits] := by
  obtain ⟨rows,rest,hp,_,_⟩ := inner_accepted x word innerBits ha
  have hw : x.outer.data.inner.row.width=x.inner.base.state.bits.length :=
    hx.outerValid.1.2.2.1.2.1.trans hx.copiedWidth
  have hparsed : readMany (readRow x.outer.data.inner.row.width) x.outer.data.total innerBits=some (rows,rest) := by
    rw [hw,hx.copiedCount]; exact hp
  have hbound : x.outer.data.total ≤ limit := by rw [hx.copiedCount]; exact hx.innerBound
  have hrun := RecoveryOuterRoot.whole_root_run limit word outerBits innerBits outerPre rows rest x.outer
    hx.outerValid hx.outerZero hx.outerBound hbound hparsed hx.outerSource hx.outerPos hx.outerCapacity
  obtain ⟨r,hr,_,hh,ht,_⟩ := hrun
  have he := congrArg (fun b : Bool=>[b]) (answer_of_inner x word innerBits outerBits rows rest hp ha).symm
  exact ⟨r,hr,hh,ht.trans he⟩

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
