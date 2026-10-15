import Proof.Amplification.RecoveryPrefixAssignmentTapes

/-! One executed assignment selector: compare the binary prefix bound, then
conditionally scan the actual committed word, otherwise keep the table bit.
Both physical branches preserve the retained count and committed word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 2→Nat := ![9,Fintype.card (RecoveryCalls.Control RecoveryCommittedBit.graphSizes)+2]
noncomputable def programs : (j : Fin 2) → Machine 8 (sizes j)
  | ⟨0,_⟩=>compareMachine
  | ⟨1,_⟩=>bitMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 8→Bool) : Option (Fin 2) :=
  if j.val=0 then if bits 2 then none else some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def cost (d : Data) := 4*d.count.length+2*RecoveryCommittedBit.rawCost d.index d.committed+12
def selected (d : Data) : Bool :=
  if value d.index<value d.count then (value d.committed).testBit (value d.index) else d.result

theorem assignment_run (d : Data) (hw : d.count.length=d.index.length)
    (hsmall : 2*d.count.length+3≤d.capacity)
    (hcap : RecoveryCommittedBit.rawCost d.index d.committed≤d.capacity) :
    ∃ r,runFrom machine (cost d) (d.cfg machine.start)=some r ∧ r.steps≤cost d ∧
      ∃ result : Data,result.count=d.count ∧ result.committed=d.committed ∧
        result.index.length=d.index.length ∧ result.capacity=d.capacity ∧ result.result=selected d ∧
        r.final=result.cfg (RecoveryCalls.controlCode sizes none) := by
  obtain ⟨r0,hr0,hf0,_⟩ := compare_run d hw hsmall
  by_cases h : value d.count≤value d.index
  · obtain ⟨n0,hn0,h0⟩ := stop_receipt sizes programs 0 next 0 _ _ r0 hr0 (by
      rw [hf0]
      simp [next,Data.cfg,Data.compared,Configuration.scanned,readTapeBit,List.getD,h])
    rw [hf0] at h0
    change Timed machine n0 (d.cfg machine.start)
      (d.compared.cfg (RecoveryCalls.controlCode sizes none)) at h0
    obtain ⟨r,hr,hf,ht⟩ := h0.run (by simp [machine,RecoveryCalls.machine,Data.cfg])
    have hn : n0≤cost d := by unfold cost; omega
    have hm := runFrom_moreFuel machine n0 (cost d-n0) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,d.compared,rfl,rfl,rfl,rfl,?_,hf⟩
    simp [Data.compared,selected,Nat.not_lt.mpr h]
  · obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ r0 hr0 (by
      rw [hf0]
      simp [next,Data.cfg,Data.compared,Configuration.scanned,readTapeBit,List.getD,h])
    rw [hf0] at h0
    change Timed machine n0 (d.cfg machine.start)
      (d.compared.cfg (RecoveryCalls.code sizes 1 bitMachine.start)) at h0
    obtain ⟨r1,hr1,_,index,flag,hi,hf1⟩ := bit_run d.compared (by
      change 2*d.index.length+1≤d.capacity
      omega) hcap
    obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 1 _ _ r1 hr1 (by rfl)
    rw [hf1] at h1
    change Timed machine n1 (d.compared.cfg (RecoveryCalls.code sizes 1 bitMachine.start))
      ((d.compared.picked index flag).cfg (RecoveryCalls.controlCode sizes none)) at h1
    have hall := h0.trans h1
    have hn : n0+n1≤cost d := by
      change n1≤2*RecoveryCommittedBit.rawCost d.index d.committed+2+1 at hn1
      unfold cost
      omega
    obtain ⟨r,hr,hf,ht⟩ := hall.run (by simp [machine,RecoveryCalls.machine,Data.cfg])
    have hm := runFrom_moreFuel machine (n0+n1) (cost d-(n0+n1)) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,d.compared.picked index flag,rfl,rfl,hi,rfl,?_,hf⟩
    simp [Data.compared,Data.picked,selected,Nat.lt_of_not_ge h]

end NearCubicWires.RepairOrdinary.RecoveryPrefixAssignment
