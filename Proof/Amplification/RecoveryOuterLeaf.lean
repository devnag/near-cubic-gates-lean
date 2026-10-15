import Proof.Amplification.RecoveryOuterLeafResult

namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def entry : Machine 84 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
noncomputable def leafMachine := RecoveryGatedSequence.machine entry checkedMachine 44
def leafCost (x : State) := checkedCost x+2
def leafOutput (x : State) (bits : List Bool) := if x.outer.base.flags 1 then checked x bits else x
def predicate (rows : List Row) (code : Nat) := rows.any (fun row=>decide (code=row.code))
def answer (x : State) (rows : List Row) :=
  if RadixSemantics.value x.outer.base.kind=1 then predicate rows (RadixSemantics.value x.outer.base.state.bits) else true

theorem leaf_run (x : State) (word outerBits innerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (rows,rest))
    (hg : x.outer.base.valid=true)
    (hk : x.outer.base.flags 1=decide (RadixSemantics.value x.outer.base.kind=1)) :
    ∃ r,runFrom leafMachine (leafCost x) (x.cfg leafMachine.start)=some r ∧
      r.final=(leafOutput x innerBits).cfg r.final.control ∧ r.steps ≤ leafCost x ∧
      (leafOutput x innerBits).Valid word outerBits innerBits ∧
      (leafOutput x innerBits).outer.base.valid=answer x rows := by
  obtain ⟨first,hr0,hf0,_⟩ := (Timed.refl entry (x.cfg entry.start)).run (by rfl)
  have hh0 : first.final.heads 44=0 := by rw [hf0]; rfl
  have ht0 : first.final.tapes 44=[x.outer.base.flags 1] := by rw [hf0]; rfl
  cases ha : x.outer.base.flags 1
  · rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.reject_run entry checkedMachine 44 0 _ first hr0 hh0 ht0
    have hl : 0+1 ≤ leafCost x := by unfold leafCost; omega
    have hm := runFrom_moreFuel leafMachine 1 (leafCost x-1) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    have hkind : RadixSemantics.value x.outer.base.kind≠1 := by
      have h := hk.symm.trans ha
      exact of_decide_eq_false h
    refine ⟨r,hm,?_,hb.trans hl,?_,?_⟩
    · apply configuration_ext
      · rfl
      · rw [hf,hf0]; simp only [leafOutput,ha,Bool.false_eq_true,if_false]; rfl
      · rw [hf,hf0]; simp only [leafOutput,ha,Bool.false_eq_true,if_false]; rfl
    · simpa only [leafOutput,ha,Bool.false_eq_true,if_false] using hx
    · simpa only [leafOutput,ha,Bool.false_eq_true,if_false,answer,if_neg hkind] using hg
  · rw [ha] at ht0
    obtain ⟨last,hr1,hf1,hb1,hv,ht⟩ := checked_run x word outerBits innerBits rows rest hx hp
    have hnext : RecoveryCalls.restarted checkedMachine first.final.heads first.final.tapes=x.cfg checkedMachine.start := by
      rw [hf0]; rfl
    rw [←hnext] at hr1
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.accept_run entry checkedMachine 44 0 (checkedCost x)
      _ first last hr0 hh0 ht0 hr1
    have hkind : RadixSemantics.value x.outer.base.kind=1 := of_decide_eq_true (hk.symm.trans ha)
    simp only [Nat.zero_add] at hr hb
    refine ⟨r,hr,?_,hb,?_,?_⟩
    · apply configuration_ext
      · rfl
      · rw [hf,hf1]; simp only [leafOutput,ha,if_true]; rfl
      · rw [hf,hf1]; simp only [leafOutput,ha,if_true]; rfl
    · simpa only [leafOutput,ha,if_true] using hv
    · simpa only [leafOutput,ha,if_true,answer,if_pos hkind,predicate] using ht

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
