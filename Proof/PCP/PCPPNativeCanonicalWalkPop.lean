import Proof.PCP.PCPPNativeCanonicalWalkPeek

/-! Restore the saved right child directly over the current same-width
decoder input. Stack and output cursors remain at their actual boundaries. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def restored (x : State) (bits pre : List Bool) : State :=
  {x with core:={x.core with bits:=bits},stack:=pre}
def popSlots : Fin 3→Fin 29 := ![26,0,22]
theorem pop_injective : Function.Injective popSlots := by decide
noncomputable def popMachine := RecoveryFocus.machine popSlots PCPPNativeCanonicalStack.popMachine

theorem restored_other (x : State) (bits pre : List Bool) (hw:bits.length=x.core.bits.length)
    (i : Fin 29) (h0:i≠0) (h26:i≠26) : (restored x bits pre).tapes i=x.tapes i := by
  have hc:RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity x.core.bits:=by
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
  dsimp only [State.tapes,restored,PCPPNativeCanonicalTree.Data.tapes,RecoveryReusableUnpair.input]
  rw [hc]
  fin_cases i
  case «0»=>exact False.elim (h0 rfl)
  case «26»=>exact False.elim (h26 rfl)
  all_goals rfl

theorem pop_run (x : State) (bits pre : List Bool) (hx:x.Valid)
    (hw:bits.length=x.core.bits.length) (hstack:x.stack=pre++(frame bits).reverse) :
    ∃ r,runFrom popMachine (4*bits.length+6) (x.cfg popMachine.start)=some r ∧
      r.final=(restored x bits pre).cfg r.final.control ∧ r.steps=4*bits.length+6 := by
  have hC:pre.length+2*bits.length+1≤x.capacity:=by
    have h:=hx.2.2.2
    simpa only [hstack,List.length_append,List.length_reverse,frame_length,Nat.add_assoc] using h
  have hR:2*bits.length+2≤x.core.reset:=by
    have hc:=PCPPNativeCanonicalTree.capacity_frame x.core.bits
    rw [hw]
    have he:=hx.2.1
    have hr:=hx.2.2.1
    omega
  obtain ⟨base,hb,bt,bh,bs⟩:=PCPPNativeCanonicalStack.pop_padded bits pre (frame x.core.bits)
    x.capacity x.core.reset (by rw [frame_length,hw]) hC hR
  have hh:∀ j,x.heads (popSlots j)=(![pre.length+(frame bits).length,0,0] : Fin 3→ℕ) j:=by
    intro j;fin_cases j
    · change x.stack.length=pre.length+(frame bits).length
      simp only [hstack,List.length_append,List.length_reverse]
    · rfl
    · rfl
  have hi:∀ j,x.tapes (popSlots j)=
      (![ZeroPadding.pad x.capacity (pre++(frame bits).reverse),frame x.core.bits,
        List.replicate x.core.reset false] : Fin 3→List Bool) j:=by
    intro j;fin_cases j
    · change ZeroPadding.pad x.capacity x.stack=_
      rw [hstack]
      rfl
    · rfl
    · rfl
  obtain ⟨r,hr,_,hs,rh,rt,ro⟩:=RecoveryFocus.dock popSlots pop_injective PCPPNativeCanonicalStack.popMachine
    _ x.heads x.tapes _ hh hi base hb
  refine ⟨r,hr,?_,hs.trans bs⟩
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i
    case «26»=>exact (rh 0).trans (by rw [bh];rfl)
    case «0»=>exact (rh 1).trans (by rw [bh];rfl)
    case «22»=>exact (rh 2).trans (by rw [bh];rfl)
    all_goals
      rw [(ro _ (by intro j;fin_cases j <;> decide)).1]
      rfl
  · funext i
    fin_cases i
    case «26»=>exact (rt 0).trans (by rw [bt];rfl)
    case «0»=>exact (rt 1).trans (by rw [bt];rfl)
    case «22»=>exact (rt 2).trans (by rw [bt];rfl)
    all_goals
      rw [(ro _ (by intro j;fin_cases j <;> decide)).2]
      exact (restored_other x bits pre hw _ (by decide) (by decide)).symm

theorem restored_valid (x : State) (bits pre : List Bool) (hx:x.Valid)
    (hw:bits.length=x.core.bits.length) (hs:pre.length≤x.capacity) :
    (restored x bits pre).Valid := by
  refine ⟨?_,?_,hx.2.2.1,hs⟩
  · intro i
    change (x.core.backing i).length≤RecoveryReusableUnpair.capacity bits
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
    exact hx.1 i
  · change x.capacity=RecoveryReusableUnpair.capacity bits
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
    exact hx.2.1

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
