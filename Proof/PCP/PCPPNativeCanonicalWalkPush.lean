import Proof.PCP.PCPPNativeCanonicalWalkMark

namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pushed (x : State) (bits : List Bool) : State :=
  {x with stack:=x.stack++(frame bits).reverse}
def pushSlots : Fin 3→Fin 29 := ![18,26,22]
theorem push_injective : Function.Injective pushSlots := by decide
noncomputable def pushMachine := RecoveryFocus.machine pushSlots PCPStackPush.machine

theorem push_run (x : State) (bits : List Bool) (hx:x.Valid)
    (hw:bits.length=x.core.bits.length)
    (hsrc:x.core.tapes 18=ZeroPadding.pad x.capacity (frame bits)) :
    ∃ r,runFrom pushMachine (4*bits.length+3) (x.cfg pushMachine.start)=some r ∧
      r.final=(pushed x bits).cfg r.final.control ∧ r.steps=4*bits.length+3 := by
  have hR:2*bits.length+1≤x.core.reset:=by
    rw [hw]
    exact (PCPPNativeCanonicalTree.capacity_frame x.core.bits).trans (by
      rw [←hx.2.1]
      exact (Nat.le_succ _).trans hx.2.2.1)
  obtain ⟨base,hb,hbf,hbs⟩:=PCPStackReady.push_run bits x.stack x.capacity x.core.reset
  let caps:Fin 3→ℕ:=![x.capacity,0,0]
  obtain ⟨localRun,hl,hlf,hls,_⟩:=ZeroPadding.run_config PCPStackPush.machine caps _ _ base hb
  have hh:∀ j,x.heads (pushSlots j)=
      (ZeroPadding.config caps (PCPStackReady.pushInput bits x.stack x.capacity x.core.reset)).heads j:=by
    intro j;fin_cases j <;> rfl
  have hi:∀ j,x.tapes (pushSlots j)=
      (ZeroPadding.config caps (PCPStackReady.pushInput bits x.stack x.capacity x.core.reset)).tapes j:=by
    intro j;fin_cases j
    · exact hsrc
    · exact (ZeroPadding.pad_zero _).symm
    · exact (ZeroPadding.pad_zero _).symm
  obtain ⟨r,hr,_,hs,rh,rt,ro⟩:=RecoveryFocus.dock pushSlots push_injective PCPStackPush.machine
    _ x.heads x.tapes _ hh hi localRun hl
  have lh:localRun.final.heads=![0,(x.stack++(frame bits).reverse).length,0]:=by rw [hlf,hbf];rfl
  have lt:localRun.final.tapes=![ZeroPadding.pad x.capacity (frame bits),
      ZeroPadding.pad x.capacity (x.stack++(frame bits).reverse),List.replicate x.core.reset false]:=by
    rw [hlf,hbf]
    funext i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad 0 (List.replicate (max x.core.reset (2*bits.length+1)) false)=_
      rw [ZeroPadding.pad_zero,Nat.max_eq_left hR]
      rfl
  refine ⟨r,hr,?_,hs.trans (hls.trans hbs)⟩
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi18:i=18
    · subst i;exact (rh 0).trans (by rw [lh];rfl)
    by_cases hi26:i=26
    · subst i;exact (rh 1).trans (by rw [lh];rfl)
    by_cases hi22:i=22
    · subst i;exact (rh 2).trans (by rw [lh];rfl)
    have hother:=ro i (by intro j;fin_cases j <;> simp [pushSlots,Ne.symm hi18,Ne.symm hi26,Ne.symm hi22])
    rw [hother.1]
    simp only [State.cfg,State.heads,pushed]
    have hv:i.val≠26:=by intro he;exact hi26 (Fin.ext he)
    simp only [if_neg hv]
  · funext i
    by_cases hi18:i=18
    · subst i;exact (rt 0).trans (by rw [lt];exact hsrc.symm)
    by_cases hi26:i=26
    · subst i;exact (rt 1).trans (by rw [lt];rfl)
    by_cases hi22:i=22
    · subst i;exact (rt 2).trans (by rw [lt];rfl)
    have hother:=ro i (by intro j;fin_cases j <;> simp [pushSlots,Ne.symm hi18,Ne.symm hi26,Ne.symm hi22])
    rw [hother.2]
    fin_cases i <;> first | rfl | exact False.elim (hi26 rfl)

theorem pushed_valid (x : State) (bits : List Bool) (hx:x.Valid)
    (hs:x.stack.length+2*bits.length+1≤x.capacity) : (pushed x bits).Valid := by
  refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
  simpa only [pushed,List.length_append,List.length_reverse,frame_length,Nat.add_assoc] using hs

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
