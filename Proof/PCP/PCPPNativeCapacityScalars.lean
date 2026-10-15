import Proof.PCP.PCPPNativeDescriptorBounds
import Proof.PCP.PCPPNativeNodeReadBounds
import Proof.PCP.PCPPNativeProjectionReadBounds
import Proof.Amplification.RecoveryProjectionWidthBudget

/-! Uniform native scalar bounds at the actual node/query consumers. C
dominates a common measured envelope, including paired projection decoding;
the reusable emitters then cost linearly in the physically supplied C. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacity
open SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem linear (W C : ℕ) (hC : 4096*(W+1)^2 ≤ C) : 64*(W+1) ≤ C := by
  have hp : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
  omega

theorem classify (tag : Fin 5) (a b W C : ℕ) (hW : 4 ≤ W)
    (ha : a ≤ W) (hb : b ≤ W) (hC : 4096*(W+1)^2 ≤ C) :
    PCPPNativeNodeClassify.budget tag a b ≤ C := by
  have h := PCPPNativeNodeRead.budget_bound tag.val a b
  have ht := tag.isLt
  have hp : (tag.val+a+b+1)^2 ≤ (3*(W+1))^2 := Nat.pow_le_pow_left (by omega) 2
  have h1 : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold PCPPNativeNodeClassify.budget
  nlinarith

theorem address (base index W C : ℕ) (hs : base+index ≤ W) (hC : 4096*(W+1)^2 ≤ C) :
    PCPPNativeAddressAppend.budget base index+1 ≤ C := by
  have h := PCPPNativeAddressAppend.budget_bound base index
  have hp := Nat.pow_le_pow_left (show base+index+1 ≤ W+1 by omega) 2
  have h1 : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  omega
theorem sum (base index W C : ℕ) (hs : base+index ≤ W) (hC : 4096*(W+1)^2 ≤ C) :
    PCPPNativeSumAppend.budget base index+1 ≤ C := by
  have h := PCPPNativeSumAppend.budget_bound base index
  have hp := Nat.pow_le_pow_left (show base+index+1 ≤ W+1 by omega) 2
  have h1 : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  omega
theorem reusable_address (base index C : ℕ) (h : PCPPNativeAddressAppend.budget base index+1 ≤ C) :
    PCPPNativeAddressReusable.budget base index C ≤ 4*C+5 := by
  unfold PCPPNativeAddressReusable.budget
  omega
theorem reusable_sum (base index C : ℕ) (h : PCPPNativeSumAppend.budget base index+1 ≤ C) :
    PCPPNativeSumReusable.budget base index C ≤ 4*C+5 := by
  unfold PCPPNativeSumReusable.budget
  omega

theorem projection_prefix {r : ℕ} (skipped : List (List Bool)) (p : ProjectedRandomBit r)
    (W C : ℕ) (hW : 4 ≤ W) (hlen : skipped.length ≤ W)
    (hstream : (FieldList.stream skipped).length ≤ W)
    (hbits : (projectionCode p).bits.length ≤ W) (hindex : PCPPNativeProjectionTyped.index p ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) : projectionPrefixBudget skipped p ≤ 11*C := by
  have hc := classify 1 skipped.length 0 W C hW hlen (by omega) hC
  have hr := PCPPNativeProjectionRead.budget_bound (projectionCode p).bits
    (PCPPNativeProjectionTyped.kind p).val (PCPPNativeProjectionTyped.index p)
    (PCPPNativeProjectionTyped.decoded p)
  have hk := (PCPPNativeProjectionTyped.kind p).isLt
  have hs : ((PCPPNativeProjectionTyped.kind p).val+PCPPNativeProjectionTyped.index p+
      (projectionCode p).bits.length+1)^2 ≤ (3*(W+1))^2 := Nat.pow_le_pow_left (by omega) 2
  have hp : PCPPNativeProjectionRead.budget (projectionCode p).bits ≤ 9*C := by nlinarith
  have hl := linear W C hC
  unfold projectionPrefixBudget PCPPNativeProjectionLookup.budget
  omega

theorem input_emit (negative : Bool) (index position C : ℕ)
    (hindex : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hposition : PCPPNativeSumAppend.budget 0 position+1 ≤ C) :
    PCPPNativeInput.budget negative index position C ≤ 8*C+40 := by
  have hi := reusable_sum 0 index C hindex
  have hp := reusable_sum 0 position C hposition
  cases negative <;>
    simp only [PCPPNativeInput.budget,PCPPNativeInput.frontBudget,PCPPNativeInput.targetBudget,
      PCPPNativeInput.firstBits,PCPPNativeInput.betweenBits,PCPPNativeInput.lastBits,
      PCPPNativeInput.target,Bool.false_eq_true,ite_false,ite_true,List.length_append] <;>
    norm_num [natWord,natBitLength] <;> omega

end NearCubicWires.RepairOrdinary.PCPPNativeCapacity
