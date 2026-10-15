import Proof.PCP.PCPPNativeCanonicalWalkState

namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counted (x : State) : State := {x with count:=x.count+1}
def marked (x : State) : State := {x with stack:=x.stack++[true]}
def countMachine : Machine 29 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=28 then some true else none,
    fun i=>if i=28 then .right else .stay⟩ else none
def markMachine : Machine 29 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=26 then some true else none,
    fun i=>if i=26 then .right else .stay⟩ else none

theorem count_run (x : State) :
    ∃ r,runFrom countMachine 1 (x.cfg 0)=some r ∧
      r.final=(counted x).cfg 1 ∧ r.steps=1 := by
  have h:step countMachine (x.cfg 0)=some ((counted x).cfg 1):=by
    simp only [step,countMachine,State.cfg]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i
      fin_cases i <;> try rfl
      change writeTapeBit (List.replicate x.count true) x.count true=List.replicate (x.count+1) true
      simpa only [List.length_replicate,List.replicate_succ'] using
        Streaming.write_append (List.replicate x.count true) true
  exact (Timed.single (by rfl) h).run (by rfl)

theorem mark_run (x : State) :
    ∃ r,runFrom markMachine 1 (x.cfg 0)=some r ∧
      r.final=(marked x).cfg 1 ∧ r.steps=1 := by
  have h:step markMachine (x.cfg 0)=some ((marked x).cfg 1):=by
    simp only [step,markMachine,State.cfg]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> try rfl
      change x.stack.length+1=(x.stack++[true]).length
      simp only [List.length_append,List.length_singleton]
    · funext i
      fin_cases i <;> try rfl
      change writeTapeBit (ZeroPadding.pad x.capacity x.stack) x.stack.length true=
        ZeroPadding.pad x.capacity (x.stack++[true])
      rw [ZeroPadding.write_pad,Streaming.write_append]
  exact (Timed.single (by rfl) h).run (by rfl)

theorem core_cold_valid (x : State) (hC:x.capacity=RecoveryReusableUnpair.capacity x.core.bits)
    (hs:x.stack.length≤x.capacity) :
    (x.withCore (PCPPNativeCanonicalTree.stepped x.core)).Valid := by
  refine ⟨PCPPNativeCanonicalTree.stepped_valid x.core,?_,?_,hs⟩
  · dsimp only [State.withCore]
    rw [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,PCPPNativeCanonicalTree.stepped_width]
    exact hC
  · change x.capacity+1≤(PCPPNativeCanonicalTree.stepped x.core).reset
    rw [hC]
    unfold PCPPNativeCanonicalTree.stepped
    split <;> dsimp [PCPPNativeCanonicalTree.decoded,PCPPNativeCanonicalTree.classified]
    · exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

theorem counted_valid (x : State) (hx:x.Valid) : (counted x).Valid := hx
theorem leaf_valid (x : State) (hx:x.Valid) : (leaf x).Valid := hx
theorem marked_valid (x : State) (hx:x.Valid) (hs:x.stack.length+1≤x.capacity) :
    (marked x).Valid := by
  refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
  simpa only [marked,List.length_append,List.length_singleton] using hs

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
