import Proof.Amplification.RecoveryRowLeafAmbient

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leafReturned (x : Children) (word : List Bool)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) : Children :=
  {x with
    base := {x.base with
      state := out.state
      extra := out.extra
      kind := RecoveryRowKind.after x.base.kind
      flags := RecoveryRowLeaf.kindFlags x.base.kind}}

theorem leafReturned_right (x : Children) (word : List Bool)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) :
    (leafReturned x word out).base.right=x.base.right := by
  change ![frame x.base.code,frame x.base.count,x.base.source,
    RepairSource.VerifierDecoding.CompareMachine.word out.state.bits.length,[x.base.valid]]=_
  rw [out.width]
  rfl

theorem leafReturned_tapes (x : Children) (word : List Bool)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) :
    leafAmbient x (RecoveryRowLeaf.tapes (RecoveryClauseEvaluation.tapes out.state out.extra)
      (RecoveryRowKind.after x.base.kind) (RecoveryRowLeaf.kindFlags x.base.kind))=(leafReturned x word out).tapes := by
  change leafAmbient x (leafReturned x word out).base.left=(leafReturned x word out).tapes
  unfold leafAmbient Children.tapes cfg Data.cfg
  rw [leafReturned_right]
  rfl

theorem leafReturned_valid (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word) :
    (leafReturned x word out).Valid word bits := by
  have hkind : (RecoveryRowKind.after x.base.kind).length≤out.state.bits.length := by
    rw [out.width]
    simpa [RecoveryRowKind.after,RecoveryLiteralTag.predWord] using hx.1.2.2.1
  refine ⟨⟨out.stateValid,out.extraValid,hkind,?_,?_⟩,?_,hx.2.2.1,hx.2.2.2.1,?_,hx.2.2.2.2.2⟩
  · change x.base.code.length≤out.state.bits.length
    rw [out.width]
    exact hx.1.2.2.2.1
  · change x.base.count.length≤out.state.bits.length
    rw [out.width]
    exact hx.1.2.2.2.2
  · change RecoveryRowLookupTable.Inv out.state.bits.length ⟨x.bank,bits⟩
    rw [out.width]
    exact hx.2.1
  · change 2*out.state.bits.length+1≤x.copyCapacity
    rw [out.width]
    exact hx.2.2.2.2.1

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
