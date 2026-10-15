import Proof.Amplification.RecoveryBankPair

/-! One actual transition copies the right bank's answer into the left
bank's result cell. Both heads and the original right answer are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBankPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine {t : Nat} (dst src : Fin t) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    some ⟨1,fun i=>if i=dst then some (scanned src) else none,fun _=>.stay⟩ else none

theorem flag_run {t : Nat} (dst src : Fin t) (heads : Fin t → Nat) (tapes : Fin t → List Bool)
    (old bit : Bool) (hd : heads dst=0) (hs : heads src=0)
    (ht : tapes dst=[old]) (hb : tapes src=[bit]) :
    ∃ r,runFrom (flagMachine dst src) 1 ⟨0,heads,tapes⟩=some r ∧ r.steps=1 ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update tapes dst [bit] := by
  have h : step (flagMachine dst src) ⟨0,heads,tapes⟩=
      some (⟨1,heads,Function.update tapes dst [bit]⟩ : Configuration t 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=dst
      · subst i
        simp [applyAction,Configuration.scanned,hd,hs,ht,hb,readTapeBit,writeTapeBit]
      · simp [applyAction,hi]
  obtain ⟨r,hr,hf,hsteps⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,hsteps,?_,?_⟩
  · rw [hf]
  · rw [hf]

noncomputable def rightReturn {t u s : Nat} (p : Machine u s) (leftSlot : Fin t) (rightSlot : Fin u) :=
  Composition.machine (rightMachine (t:=t) p) (flagMachine (leftSlot.castAdd u) (rightSlot.natAdd t))

theorem right_return_run {t u s : Nat} (p : Machine u s) (leftSlot : Fin t) (rightSlot : Fin u)
    (budget : Nat) (lh : Fin t → Nat) (lt : Fin t → List Bool)
    (rh : Fin u → Nat) (rt : Fin u → List Bool) (old bit : Bool)
    (hlh : lh leftSlot=0) (hlt : lt leftSlot=[old])
    (base : ExecutionReceipt u s)
    (hr : runFrom p budget ⟨p.start,rh,rt⟩=some base)
    (hbh : base.final.heads rightSlot=0) (hbt : base.final.tapes rightSlot=[bit]) :
    ∃ r,runFrom (rightReturn p leftSlot rightSlot) (budget+1+1)
        (cfg lh lt rh rt (rightReturn p leftSlot rightSlot).start)=some r ∧
      r.steps ≤ budget+1+1 ∧ r.final.heads (leftSlot.castAdd u)=0 ∧
      r.final.tapes (leftSlot.castAdd u)=[bit] := by
  obtain ⟨first,hr0,hs0,hf0⟩ := right_run p budget ⟨p.start,rh,rt⟩ base hr lh lt
  have hd : first.final.heads (leftSlot.castAdd u)=0 := by rw [hf0]; simpa only [cfg,Fin.addCases_left] using hlh
  have hs : first.final.heads (rightSlot.natAdd t)=0 := by rw [hf0]; simpa only [cfg,Fin.addCases_right] using hbh
  have ht : first.final.tapes (leftSlot.castAdd u)=[old] := by rw [hf0]; simpa only [cfg,Fin.addCases_left] using hlt
  have hb : first.final.tapes (rightSlot.natAdd t)=[bit] := by rw [hf0]; simpa only [cfg,Fin.addCases_right] using hbt
  obtain ⟨last,hr1,hs1,hh1,ht1⟩ := flag_run (leftSlot.castAdd u) (rightSlot.natAdd t)
    first.final.heads first.final.tapes old bit hd hs ht hb
  have h := Composition.run_join (rightMachine (t:=t) p)
    (flagMachine (leftSlot.castAdd u) (rightSlot.natAdd t)) budget 1 _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,h,?_,?_,?_⟩
  · change first.steps+1+last.steps ≤ budget+1+1
    rw [hs0,hs1]
    have hb := runFrom_steps_le p budget _ base hr
    omega
  · change last.final.heads (leftSlot.castAdd u)=0
    rw [hh1]; exact hd
  · change last.final.tapes (leftSlot.castAdd u)=[bit]
    rw [ht1,Function.update_self]

end NearCubicWires.RepairOrdinary.RecoveryBankPair
