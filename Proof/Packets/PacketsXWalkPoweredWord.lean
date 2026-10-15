import Proof.Packets.FrozenWalkABI

/-! The physical order of the forty base labels is exactly the frozen
little-endian mixed-radix equivalence, not merely a bijection with its samples. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkPoweredWord
open NearCubicWires NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey

def word : {n : Nat}→(Fin n→Fin 16)→List Bool
  | 0,_=>[]
  | _+1,labels=>FrozenWalkABI.labelBits (labels 0)++word (Fin.tail labels)

theorem length {n : Nat} (labels : Fin n→Fin 16) : (word labels).length=4*n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [word,List.length_append,FrozenWalkABI.labelBits_length,ih]
    omega

theorem radix_tail {n : Nat} (labels : Fin (n+1)→Fin 16) :
    (finFunctionFinEquiv labels).val=(labels 0).val+16*(finFunctionFinEquiv (Fin.tail labels)).val := by
  simp only [finFunctionFinEquiv_apply,Fin.sum_univ_succ,Fin.val_zero,pow_zero,Nat.mul_one,
    Fin.val_succ,pow_succ,Fin.tail]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem value {n : Nat} (labels : Fin n→Fin 16) :
    RadixSemantics.value (word labels)=(finFunctionFinEquiv labels).val := by
  induction n with
  | zero=>simp [word,RadixSemantics.value]
  | succ n ih=>
    rw [word,RadixSemantics.value_append,FrozenWalkABI.labelBits_value,
      FrozenWalkABI.labelBits_length,ih,radix_tail]
    rfl

theorem binary_eq {n : Nat} (labels : Fin n→Fin 16) :
    word labels=binary (4*n) (finFunctionFinEquiv labels).val := by
  have h:=BoundedCounter.binary_of_value (word labels)
  rw [length,value] at h
  exact h.symm

theorem powered_binary (label : PoweredMargulisLabel) :
    word label=binary 160 (poweredMargulisLabelFinEquiv label).val := by
  simpa only [poweredMargulisLabelFinEquiv,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using binary_eq label

end Theorem25Completion.WalkPoweredWord
