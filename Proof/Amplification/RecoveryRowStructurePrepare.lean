import Proof.Amplification.RecoveryRowStructureTagCompare

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepareMachine := Composition.machine codeMachine tagCompareMachine
def prepareTime (d : Data) := codeTime d+1+(8*d.code.length+20)
def prepared (d : Data) := tagCompared (codeOutput d) (RecoveryFixedUnpair.leftWord d.code)

theorem prepare_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) (hk : d.kind.length=d.state.bits.length)
    (hc : 2*d.code.length+1≤capacity) (hr : 4*d.code.length+3≤d.state.capacity) :
    ∃ r,runFrom prepareMachine (prepareTime d) (cfg d capacity prepareMachine.start)=some r ∧
      r.final=cfg (prepared d) capacity r.final.control ∧ r.steps=prepareTime d ∧
      (prepared d).Valid word ∧
      (prepared d).flags 0=decide ((Nat.unpair (value d.code)).1=value d.kind) := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := code_run d capacity word hd hw hc hr
  have hlen : (RecoveryFixedUnpair.leftWord d.code).length=d.code.length := (RecoveryFixedUnpair.word_lengths d.code).1
  have hkind : (RecoveryFixedUnpair.leftWord d.code).length=(codeOutput d).kind.length :=
    hlen.trans (hw.trans hk.symm)
  have hreset : 2*(RecoveryFixedUnpair.leftWord d.code).length+3≤(codeOutput d).state.capacity := by
    rw [hlen]
    change 2*d.code.length+3≤ max d.state.capacity (RecoveryReusableUnpair.capacity d.code+1)
    exact (by omega : 2*d.code.length+3≤d.state.capacity).trans (Nat.le_max_left _ _)
  obtain ⟨last,hr1,hf1,hs1,hv1,hflag⟩ := tag_compare_run (codeOutput d) capacity
    (RecoveryReusableUnpair.capacity d.code) (RecoveryFixedUnpair.leftWord d.code) word hv0 hkind hreset
    (code_tag d capacity hw)
  have hstart : Composition.restart first.final tagCompareMachine.start=cfg (codeOutput d) capacity tagCompareMachine.start := by
    rw [hf0]
    rfl
  have hnext : runFrom tagCompareMachine (8*d.code.length+20)
      (Composition.restart first.final tagCompareMachine.start)=some last := by
    rw [hstart]
    simpa only [hlen] using hr1
  have hall := Composition.run_join codeMachine tagCompareMachine (codeTime d) (8*d.code.length+20)
    _ first last hr0 hnext
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv1,?_⟩
  · change Composition.rightConfig _ last.final=cfg (prepared d) capacity _
    rw [hf1]
    rfl
  · change first.steps+1+last.steps=prepareTime d
    rw [hs0,hs1,hlen]
    rfl
  · change (tagCompared (codeOutput d) (RecoveryFixedUnpair.leftWord d.code)).flags 0=_
    rw [hflag,(code_values d).1]
    rfl

theorem prepared_tag (d : Data) (capacity : Nat) (hw : d.code.length=d.state.bits.length) :
    (cfg (prepared d) capacity (0 : Fin 1)).tapes 17=
      ZeroPadding.pad (RecoveryReusableUnpair.capacity d.code) (frame (RecoveryFixedUnpair.leftWord d.code)) :=
  code_tag d capacity hw

theorem prepared_kind (d : Data) : (prepared d).kind=d.kind := rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
