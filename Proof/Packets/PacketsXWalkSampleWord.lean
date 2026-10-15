import Proof.Packets.PacketsXWalkPoweredWord

/-! Exact bit order of a positive walk sample. All transition labels occupy
the low bits, followed by the second and then first start coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSampleWord
open NearCubicWires NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey

def labelsWord : {n : Nat}→(Fin n→PoweredMargulisLabel)→List Bool
  | 0,_=>[]
  | _+1,labels=>WalkPoweredWord.word (labels 0)++labelsWord (Fin.tail labels)

theorem labels_length {n : Nat} (labels : Fin n→PoweredMargulisLabel) :
    (labelsWord labels).length=160*n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [labelsWord,List.length_append,WalkPoweredWord.length,ih]
    omega

theorem radix_tail {m n : Nat} (labels : Fin (n+1)→Fin m) :
    (finFunctionFinEquiv labels).val=(labels 0).val+m*(finFunctionFinEquiv (Fin.tail labels)).val := by
  simp only [finFunctionFinEquiv_apply,Fin.sum_univ_succ,Fin.val_zero,pow_zero,Nat.mul_one,
    Fin.val_succ,pow_succ,Fin.tail]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem labels_value {n : Nat} (labels : Fin n→PoweredMargulisLabel) :
    RadixSemantics.value (labelsWord labels)=(poweredMargulisLabelsFinEquiv n labels).val := by
  induction n with
  | zero=>simp only [labelsWord,RadixSemantics.value,poweredMargulisLabelsFinEquiv,
      Equiv.trans_apply,finFunctionFinEquiv_apply,Fin.sum_univ_zero]
  | succ n ih=>
    rw [labelsWord,RadixSemantics.value_append,WalkPoweredWord.length]
    rw [WalkPoweredWord.powered_binary, binary_value _ _ (by
      have h:=(poweredMargulisLabelFinEquiv (labels 0)).isLt
      simpa only [FrozenWalkABI.label_cardinality] using h),ih]
    change _=(finFunctionFinEquiv (fun i=>poweredMargulisLabelFinEquiv (labels i))).val
    rw [radix_tail]
    simp only [FrozenWalkABI.label_cardinality]
    rfl

def word {n : Nat} (rank : Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)):=
  labelsWord (sampleTransitionLabels sample)++WalkSeedBinary.vertexWord rank sample.start

theorem length {n : Nat} (rank : Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)) :
    (word rank sample).length=160*n+2*toeplitzWalkSideBits rank := by
  rw [word,List.length_append,labels_length,WalkSeedBinary.vertexWord_length]

theorem value {n : Nat} (rank : Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)) :
    RadixSemantics.value (word rank sample)=
      (positiveWalkSampleFinEquiv (2^toeplitzWalkSideBits rank) n sample).val := by
  rw [word,RadixSemantics.value_append,labels_value,labels_length,
    WalkSeedBinary.vertexWord,RadixSemantics.value_append,binary_length,
    binary_value _ _ (ZMod.val_lt sample.start.2),binary_value _ _ (ZMod.val_lt sample.start.1)]
  have hp : 2^(160*n)=Fintype.card PoweredMargulisLabel^n := by
    rw [FrozenWalkABI.label_cardinality,pow_mul]
  rw [hp]
  simp only [positiveWalkSampleFinEquiv,Equiv.trans_apply,finCongr_apply,Fin.val_cast,
    Equiv.prodCongr_apply,finProdFinEquiv_apply_val,positiveSampleEquiv,margulisVertexFinEquiv,
    Equiv.coe_fn_mk,Prod.map_fst,Prod.map_snd,
    ]
  have h1:=Completion.ToeplitzSeedBits.finEquiv_symm_val sample.start.1
  have h2:=Completion.ToeplitzSeedBits.finEquiv_symm_val sample.start.2
  change _ = _ + _ * (((ZMod.finEquiv _).symm sample.start.2).val+
    2^toeplitzWalkSideBits rank*((ZMod.finEquiv _).symm sample.start.1).val)
  rw [h1,h2]

theorem binary_eq {n : Nat} (rank : Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)) :
    word rank sample=binary (160*n+2*toeplitzWalkSideBits rank)
      (positiveWalkSampleFinEquiv (2^toeplitzWalkSideBits rank) n sample).val := by
  have h:=BoundedCounter.binary_of_value (word rank sample)
  rw [length,value] at h
  exact h.symm

end Theorem25Completion.WalkSampleWord
