import Proof.Amplification.RecoveryRowStructureSmallCases

/-! The paired-row branch executes a second unpair on the retained right
component of the original code. Its two actual output words are the keys
for the two prior-row lookups. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairWord (d : Data) := RecoveryChildSelection.word false d.code
def leftChild (d : Data) := RecoveryFixedUnpair.leftWord (pairWord d)
def rightChild (d : Data) := RecoveryChildSelection.word false (pairWord d)
def childrenDecoded (d : Data) := decoded (frontOutput d) (pairWord d)

theorem front_field (d : Data) : (frontOutput d).state.fields 0=frame (pairWord d) := by
  unfold frontOutput
  split <;> exact code_child d 0

theorem children_decode_run (d : Data) (capacity : Nat) (word : List Bool)
    (hd : d.Valid word) (hw : d.code.length=d.state.bits.length) :
    ∃ r,runFrom decodeMachine (RecoveryDecodeStep.time (pairWord d))
        (cfg (frontOutput d) capacity decodeMachine.start)=some r ∧
      r.final=cfg (childrenDecoded d) capacity r.final.control ∧
      r.steps=RecoveryDecodeStep.time (pairWord d) ∧ (childrenDecoded d).Valid word := by
  exact decode_run (frontOutput d) capacity (pairWord d) word (front_output_valid d word hd hw)
    ((RecoveryChildSelection.word_length false d.code).trans (hw.trans (congrArg List.length (front_retained d).2.2.2.1).symm)) (front_field d)

theorem children_decoded_left (d : Data) (capacity : Nat) (hw : d.code.length=d.state.bits.length) :
    (cfg (childrenDecoded d) capacity (0 : Fin 1)).tapes 17=
      ZeroPadding.pad (RecoveryReusableUnpair.capacity (pairWord d)) (frame (leftChild d)) := by
  have h := RecoveryLiteralDecode.output_tag (frontOutput d).state 0 (pairWord d)
  have hlen : (pairWord d).length=(frontOutput d).state.bits.length :=
    (RecoveryChildSelection.word_length false d.code).trans (hw.trans (congrArg List.length (front_retained d).2.2.2.1).symm)
  rw [RecoveryLiteralDecode.decoded_output (frontOutput d).state 0 (pairWord d) hlen] at h
  exact h

theorem children_decoded_right (d : Data) : (childrenDecoded d).state.fields 0=frame (rightChild d) := by
  change (RecoveryLiteralDecode.decodedState (frontOutput d).state 0 (pairWord d)).fields 0=_
  simp [RecoveryLiteralDecode.decodedState,rightChild]

theorem children_values (d : Data) :
    value (leftChild d)=(Nat.unpair (Nat.unpair (value d.code)).2).1 ∧
      value (rightChild d)=(Nat.unpair (Nat.unpair (value d.code)).2).2 := by
  have h := RecoveryLiteralDecode.literal_values (pairWord d)
  have hp : value (pairWord d)=(Nat.unpair (value d.code)).2 := (code_values d).2
  rw [hp] at h
  exact h

theorem children_widths (d : Data) :
    (leftChild d).length=d.code.length ∧ (rightChild d).length=d.code.length := by
  exact ⟨(RecoveryFixedUnpair.word_lengths (pairWord d)).1.trans (RecoveryChildSelection.word_length false d.code),
    (RecoveryChildSelection.word_length false (pairWord d)).trans (RecoveryChildSelection.word_length false d.code)⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
