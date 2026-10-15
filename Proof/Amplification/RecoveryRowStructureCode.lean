import Proof.Amplification.RecoveryRowStructureCore

/-! Whole structural-row code preparation: paid copy of the parsed code,
followed by the existing reusable unpair call on that exact word. The source
cursor and clause payload remain in their actual retained configuration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def codeMachine := Composition.machine copyMachine decodeMachine
def codeTime (d : Data) := 8*d.code.length+9+RecoveryDecodeStep.time d.code
def codeOutput (d : Data) := decoded (copied d) d.code

theorem code_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) (hc : 2*d.code.length+1≤capacity)
    (hr : 4*d.code.length+3≤d.state.capacity) :
    ∃ r,runFrom codeMachine (codeTime d) (cfg d capacity codeMachine.start)=some r ∧
      r.final=cfg (codeOutput d) capacity r.final.control ∧ r.steps=codeTime d ∧
      (codeOutput d).Valid word := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := copy_run d capacity word hd hw hc hr
  obtain ⟨last,hr1,hf1,hs1,hv1⟩ := decode_run (copied d) capacity d.code word hv0 hw
    (by simp [copied,setField])
  have hstart : Composition.restart first.final decodeMachine.start=cfg (copied d) capacity decodeMachine.start := by
    rw [hf0]
    rfl
  have hnext : runFrom decodeMachine (RecoveryDecodeStep.time d.code)
      (Composition.restart first.final decodeMachine.start)=some last := by rw [hstart]; exact hr1
  have hall := Composition.run_join copyMachine decodeMachine (8*d.code.length+8)
    (RecoveryDecodeStep.time d.code) _ first last hr0 hnext
  have htime : (8*d.code.length+8)+1+RecoveryDecodeStep.time d.code=codeTime d := by unfold codeTime; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv1⟩
  · change Composition.rightConfig _ last.final=cfg (codeOutput d) capacity _
    rw [hf1]
    rfl
  · change first.steps+1+last.steps=codeTime d
    rw [hs0,hs1]
    exact htime

theorem code_child (d : Data) (capacity : Nat) :
    (cfg (codeOutput d) capacity (0 : Fin 1)).tapes 24=frame (RecoveryChildSelection.word false d.code) := by
  change (RecoveryLiteralDecode.decodedState (copied d).state 0 d.code).fields 0=_
  simp [RecoveryLiteralDecode.decodedState]

theorem code_tag (d : Data) (capacity : Nat) (hw : d.code.length=d.state.bits.length) :
    (cfg (codeOutput d) capacity (0 : Fin 1)).tapes 17=
      ZeroPadding.pad (RecoveryReusableUnpair.capacity d.code) (frame (RecoveryFixedUnpair.leftWord d.code)) := by
  have h := RecoveryLiteralDecode.output_tag (copied d).state 0 d.code
  rw [RecoveryLiteralDecode.decoded_output (copied d).state 0 d.code hw] at h
  exact h

theorem code_values (d : Data) :
    value (RecoveryFixedUnpair.leftWord d.code)=(Nat.unpair (value d.code)).1 ∧
    value (RecoveryChildSelection.word false d.code)=(Nat.unpair (value d.code)).2 :=
  RecoveryLiteralDecode.literal_values d.code

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
