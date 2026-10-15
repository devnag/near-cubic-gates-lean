import Proof.PCP.PCPOuter

namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focused_run {u : ℕ} (slot : Fin 133 → Fin u) (inj : Function.Injective slot)
    (a b c d sa sb sc sd : List Bool) (h : Fin u → ℕ) (t : Fin u → List Bool)
    (hh : ∀ j,h (slot j)=0) (ht : ∀ j,t (slot j)=input a b c d sa sb sc sd j) :
    ∃ r,runFrom (RecoveryFocus.machine slot machine) (budget (size a b c d))
      ⟨machine.start,h,t⟩=some r ∧
      r.final.tapes (slot 82)=(PCPTraversal.code (fields a b c d)).bits ∧
      r.final.heads (slot 82)=0 ∧
      r.final.tapes (slot 81)=ZeroPadding.pad (PCPPairReusable.capacity (2*size a b c d+4))
        (frame (PCPTraversal.code (fields a b c d)).bits) ∧
      (∀ j : Fin 4,r.final.tapes (slot (j.castAdd 129))=t (slot (j.castAdd 129))) ∧
      (∀ i,(∀ j,slot j≠i) → r.final.heads i=h i ∧ r.final.tapes i=t i) ∧
      r.steps≤budget (size a b c d) := by
  obtain ⟨base,hb,b82,bh,b81,bi,bs⟩ := outer_run a b c d sa sb sc sd
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slot inj machine h t _ _ base hb
  rw [focused_existing slot h t _ hh ht] at hr
  have sh (j : Fin 133) : r.final.heads (slot j)=base.final.heads j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot inj]
  have st (j : Fin 133) : r.final.tapes (slot j)=base.final.tapes j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot inj]
  refine ⟨r,hr,(st 82).trans b82,(sh 82).trans bh,(st 81).trans b81,?_,?_,?_⟩
  · intro j
    rw [st,bi,ht]
  · intro i hi
    have hp : RecoveryFocus.pick slot i=none := by
      classical
      unfold RecoveryFocus.pick
      exact dif_neg (by rintro ⟨j,hj⟩; exact hi j hj)
    simp only [rf,RecoveryFocus.config,hp]
    exact ⟨True.intro,True.intro⟩
  · omega

end NearCubicWires.RepairOrdinary.PCPOuter
