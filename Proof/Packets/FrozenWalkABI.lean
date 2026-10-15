import Proof.Packets.WalkSeedBinary

/-! Exact label widths of the frozen powered walk. A base label has four
physical bits even though its arithmetic branch uses only three of them. -/
set_option autoImplicit false
set_option warningAsError true
namespace Theorem25Completion.FrozenWalkABI
open NearCubicWires NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey

def labelBits (label : Fin 16):=binary 4 label.val

theorem labelBits_length (label : Fin 16) : (labelBits label).length=4 := binary_length _ _

theorem labelBits_value (label : Fin 16) : RadixSemantics.value (labelBits label)=label.val :=
  binary_value 4 label.val label.isLt

theorem labelBits_branch (label : Fin 16) :
    labelBits label=binary 3 (duplicatedMargulisLabel label).val++[decide (8≤label.val)] := by
  fin_cases label <;>rfl

theorem label_cardinality : Fintype.card PoweredMargulisLabel=2^160 := by
  rw [card_poweredMargulisLabel]
  norm_num

def seedLabelWidth (denominator : Nat):=160*(canonicalWalkLength denominator-1)

theorem seedLabelWidth_eq (denominator : Nat) :
    seedLabelWidth denominator=320*Nat.clog 2 (denominator+1) := by
  unfold seedLabelWidth canonicalWalkLength
  omega

end Theorem25Completion.FrozenWalkABI
