import Proof.Amplification.RecoveryRowStructureFlags

/-! Typed return for classification of the padded unpair tag on physical
backing tape17. Its allocated length is retained, so later unpair calls see
an actual bounded scratch tape rather than a fresh blank-tape assumption. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagState (s : State) (word : List Bool) : State := {s with backing:=Function.update s.backing 16 word}
def setTag (d : Data) (word : List Bool) : Data := {d with state:=tagState d.state word}

theorem unpair_tag_store (s : State) (word : List Bool) :
    RecoveryReusableUnpair.input s.bits s.capacity (Function.update s.backing 16 word)=
      Function.update (RecoveryReusableUnpair.input s.bits s.capacity s.backing) 17 word := by
  unfold RecoveryReusableUnpair.input
  rw [bank_update_left,bank_update_left,bank_update_right]
  rfl

theorem state_tag_store (s : State) (word : List Bool) :
    (tagState s word).tapes=Function.update s.tapes 17 word := by
  change Fin.addCases (m:=24) (n:=4) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=23) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryReusableUnpair.input s.bits s.capacity (Function.update s.backing 16 word)) (fun _=>[s.flag]))
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) s.fields (fun _=>[s.result]))=_
  rw [unpair_tag_store,bank_update_left,bank_update_left]
  rfl

theorem clause_tag_store (s : State) (e : RecoveryClauseEvaluation.Extra) (word : List Bool) :
    RecoveryClauseEvaluation.tapes (tagState s word) e=
      Function.update (RecoveryClauseEvaluation.tapes s e) 17 word := by
  change Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool) (tagState s word).tapes (e.tapes s)=_
  rw [state_tag_store,bank_update_left]
  rfl

theorem left_tag_store (d : Data) (word : List Bool) :
    (setTag d word).left=Function.update d.left 17 word := by
  change Fin.addCases (m:=42) (n:=4) (motive:=fun _=>List Bool)
    (RecoveryClauseEvaluation.tapes (tagState d.state word) d.extra) (RecoveryRowLeaf.extra d.kind d.flags)=_
  rw [clause_tag_store,bank_update_left]
  rfl

theorem row_tag_store (d : Data) (word : List Bool) :
    ((setTag d word).cfg (0 : Fin 1)).tapes=Function.update (d.cfg (0 : Fin 1)).tapes 17 word := by
  change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (setTag d word).left d.right=_
  rw [left_tag_store,bank_update_left]
  rfl

theorem cfg_tag_store (d : Data) (capacity : Nat) (word : List Bool) :
    (cfg (setTag d word) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes 17 word := by
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    ((setTag d word).cfg (0 : Fin 1)).tapes (fun _=>List.replicate capacity false)=_
  rw [row_tag_store,bank_update_left]
  rfl

theorem tagState_valid (s : State) (word : List Bool) (hs : s.Valid)
    (hw : word.length≤RecoveryReusableUnpair.capacity s.bits) : (tagState s word).Valid := by
  refine ⟨?_,hs.2⟩
  intro i
  by_cases hi : i=16
  · subst i; simpa only [tagState,Function.update_self] using hw
  · simpa only [tagState,Function.update_of_ne hi] using hs.1 i

theorem setTag_valid (d : Data) (tag word : List Bool) (hd : d.Valid word)
    (ht : tag.length≤RecoveryReusableUnpair.capacity d.state.bits) : (setTag d tag).Valid word := by
  refine ⟨tagState_valid d.state tag hd.1 ht,?_,hd.2.2⟩
  exact ⟨hd.2.1.source,hd.2.1.row,hd.2.1.counter,hd.2.1.count,
    hd.2.1.committed,hd.2.1.cap,hd.2.1.prefixBound,hd.2.1.reset⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
