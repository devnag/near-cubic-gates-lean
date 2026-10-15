import Proof.PCP.PCPPNativeCanonicalWalkPush

namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def restacked (x : State) (pre : List Bool) : State := {x with stack:=pre}
def peekSlots : Fin 1→Fin 29 := fun _=>26
theorem peek_injective : Function.Injective peekSlots := by decide
noncomputable def peekMachine := RecoveryFocus.machine peekSlots PCPPNativeCanonicalStack.peek

private theorem peek_transport (x : State) (pre : List Bool) (q : Fin 4)
    (base : ExecutionReceipt 1 4)
    (hb:runFrom PCPPNativeCanonicalStack.peek 2
      (PCPPNativeCanonicalStack.oneCfg 0 (ZeroPadding.pad x.capacity x.stack) x.stack.length)=some base)
    (hf:base.final=PCPPNativeCanonicalStack.oneCfg q (ZeroPadding.pad x.capacity pre) pre.length)
    (hs:base.steps=2) :
    ∃ r,runFrom peekMachine 2 (x.cfg peekMachine.start)=some r ∧
      r.final=(restacked x pre).cfg q ∧ r.steps=2 := by
  obtain ⟨r,hr,hq,hsteps,rh,rt,ro⟩:=RecoveryFocus.dock peekSlots peek_injective PCPPNativeCanonicalStack.peek
    2 x.heads x.tapes _ (by intro j;fin_cases j;rfl) (by intro j;fin_cases j;rfl) base hb
  refine ⟨r,hr,?_,hsteps.trans hs⟩
  apply configuration_ext
  · exact hq.trans (by rw [hf];rfl)
  · funext i
    fin_cases i
    case «26»=>exact (rh 0).trans (by rw [hf];rfl)
    all_goals
      rw [(ro _ (by intro j;fin_cases j;decide)).1]
      rfl
  · funext i
    fin_cases i
    case «26»=>exact (rt 0).trans (by rw [hf];rfl)
    all_goals
      rw [(ro _ (by intro j;fin_cases j;decide)).2]
      rfl

theorem peek_some (x : State) (pre : List Bool) (hstack:x.stack=pre++[true])
    (hC:x.stack.length≤x.capacity) :
    ∃ r,runFrom peekMachine 2 (x.cfg peekMachine.start)=some r ∧
      r.final=(restacked x pre).cfg 2 ∧ r.steps=2 := by
  have hC':pre.length+1≤x.capacity:=by simpa only [hstack,List.length_append,List.length_singleton] using hC
  obtain ⟨base,hb,hf,hs⟩:=PCPPNativeCanonicalStack.peek_some pre x.capacity hC'
  apply peek_transport x pre 2 base _ hf hs
  simpa only [hstack,List.length_append,List.length_singleton] using hb

theorem peek_empty (x : State) (hstack:x.stack=[false]) :
    ∃ r,runFrom peekMachine 2 (x.cfg peekMachine.start)=some r ∧
      r.final=x.cfg 3 ∧ r.steps=2 := by
  obtain ⟨base,hb,hf,hs⟩:=PCPPNativeCanonicalStack.peek_empty x.capacity
  obtain ⟨r,hr,rf,rs⟩:=peek_transport x [false] 3 base
    (by simpa only [hstack,List.length_singleton] using hb) hf hs
  have he:restacked x [false]=x:=by cases x;simp_all [restacked]
  exact ⟨r,hr,by rw [he] at rf;exact rf,rs⟩

theorem restacked_valid (x : State) (pre : List Bool) (hx:x.Valid)
    (hs:pre.length≤x.capacity) : (restacked x pre).Valid := ⟨hx.1,hx.2.1,hx.2.2.1,hs⟩

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
