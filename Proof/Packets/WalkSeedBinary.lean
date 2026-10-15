import Proof.Packets.ToeplitzSeedBits
import Proof.MachineModel.OrdinaryBoundedCounter

/-! Exact little-endian words of the frozen Toeplitz encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedBinary
open NearCubicWires NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open Completion.ToeplitzSeedBits

theorem binary_split (a b n : Nat) :
    binary (a+b) n=binary a n++binary b (n/2^a) := by
  induction a generalizing n with
  | zero => simp [binary]
  | succ a ih =>
    simp only [Nat.succ_add,binary,ih,List.cons_append]
    rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm 2]

theorem binary_ofFn (width n : Nat) :
    binary width n=List.ofFn (fun i : Fin width=>decide (n/2^i.val%2=1)) := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih =>
    rw [binary,List.ofFn_succ,ih]
    congr 1
    · simpa using Bool.beq_eq_decide_eq (n%2) 1
    · apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ,pow_succ,Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm 2]

theorem bit_mod (n : Nat) :
    decide (((n%2 : Nat) : ZMod 2)=1)=decide (n%2=1) := by
  have h : n%2<2 := Nat.mod_lt _ (by decide)
  rcases (by omega : n%2=0 ∨ n%2=1) with h | h <;> simp [h]

def vertexWord (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :=
  binary (toeplitzWalkSideBits rank) v.2.val++binary (toeplitzWalkSideBits rank) v.1.val

theorem vertexWord_length (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    (vertexWord rank v).length=2*toeplitzWalkSideBits rank := by
  simp only [vertexWord,List.length_append,binary_length]
  omega

theorem vertexWord_binary (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    vertexWord rank v=binary (2*toeplitzWalkSideBits rank) (vertexCode rank v) := by
  have h:=BoundedCounter.binary_of_value (vertexWord rank v)
  rw [vertexWord_length] at h
  have hv : RadixSemantics.value (vertexWord rank v)=vertexCode rank v := by
    rw [vertexWord,RadixSemantics.value_append,binary_length,
      binary_value _ _ (ZMod.val_lt v.2),binary_value _ _ (ZMod.val_lt v.1)]
    rfl
  rw [hv] at h
  exact h.symm

theorem lower_word (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.1.1 i=1))=
      binary rank (seedCode rank v) := by
  rw [binary_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [lower_value,bit_mod]

theorem upper_word (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    List.ofFn (fun i : Fin (rank-1)=>decide ((toeplitzWalkEncoding rank v).1.1.2 i=1))=
      binary (rank-1) (seedCode rank v/2^rank) := by
  rw [binary_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [upper_value,bit_mod,Nat.div_div_eq_div_mul,←pow_add]

theorem translation_word (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) :
    List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.2 i=1))=
      binary rank (seedCode rank v/2^(rank+(rank-1))) := by
  rw [binary_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [translation_value,bit_mod,Nat.div_div_eq_div_mul,←pow_add]

end Theorem25Completion.WalkSeedBinary
