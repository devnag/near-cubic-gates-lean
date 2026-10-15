import Proof.Amplification.RecoveryRowRootWhole

/-! Successful structural checking already leaves the singleton-kind bit
on tape44. The outer table can branch on it without another classifier. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem children_flags (x : Children) (pair bits : List Bool) :
    (childrenOutput x pair bits).base.flags=x.base.flags := by
  unfold childrenOutput leftOutput
  split
  · unfold rightOutput
    split <;> rfl
  · rfl

theorem structure_leaf_flag (x : Children) (bits : List Bool)
    (ha : (structureOutput x bits).base.valid=true) :
    (structureOutput x bits).base.flags 1=decide (value x.base.kind=1) := by
  cases hf : (frontOutput x.base).valid
  · simp only [structureOutput,hf,Bool.false_eq_true,if_false] at ha
    exact False.elim (Bool.noConfusion (hf.symm.trans ha))
  · have hflags := front_success_flags x.base hf
    cases hz : (frontOutput x.base).flags 0
    · cases ho : (frontOutput x.base).flags 1
      · simp only [structureOutput,hf,if_true,hz,ho,Bool.false_eq_true,if_false]
        rw [children_flags]
        exact hflags 1
      · simp only [structureOutput,hf,if_true,hz,ho,Bool.false_eq_true,if_false] at ha ⊢
        have hc : value (frontOutput x.base).count=1 := (of_decide_eq_true ha).2
        change (oneOutput (frontOutput x.base) (pairWord x.base)).flags 1=_
        have hkind : value x.base.kind=1 := of_decide_eq_true ((hflags 1).symm.trans ho)
        simp [oneOutput,countClassified,payloadCompared,setValid,setCount,setFlag,hc,hkind]
    · simp only [structureOutput,hf,if_true,hz] at ha ⊢
      have hc : value (frontOutput x.base).count=0 := (of_decide_eq_true ha).2
      have hkind : value x.base.kind=0 := of_decide_eq_true ((hflags 0).symm.trans hz)
      change (zeroOutput (frontOutput x.base)).flags 1=_
      simp [zeroOutput,countClassified,codePredicted,setValid,setCode,setCount,setFlag,hc,hkind]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
