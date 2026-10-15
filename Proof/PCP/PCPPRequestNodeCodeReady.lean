import Proof.PCP.PCPPRequestNodeCodeStage

namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stage_ready (tapes : Fin 234 → List Bool) (bank : Fin 3)
    (left right : Fin 234) (hl : left.val < offset bank) (hr : right.val < offset bank)
    (hne : left≠right) (a b pa pb : ℕ)
    (ha : tapes left=frame a.bits++List.replicate pa false)
    (hb : tapes right=frame b.bits++List.replicate pb false)
    (hf : ∀ i,offset bank ≤ i.val → i.val < offset bank+76 → tapes i=[]) :
    ∃ out,ClockJoin.ReadyRun (cons bank left right) (PCPPRequestTaggedCons.budget a b) tapes out ∧
      (∃ padding,out (outputSlot bank)=frame (Nat.pair 1 (Nat.pair a b)).bits++List.replicate padding false) ∧
      out (rawSlot bank)=(Nat.pair 1 (Nat.pair a b)).bits ∧
      (∀ i,left≠i → right≠i → (i.val < offset bank ∨ offset bank+76 ≤ i.val) → out i=tapes i) := by
  obtain ⟨r,hrun,rs,rh,rf,rr,rkeep⟩ := stage_run
    (⟨0,fun _ => 0,tapes⟩ : Configuration 234 1) bank left right hl hr hne a b pa pb ha hb
    (fun _ => rfl) hf
  exact ⟨r.final.tapes,⟨r,hrun,rfl,rh,rs⟩,rf,rr,rkeep⟩

noncomputable def unary := Composition.machine (Composition.machine printer (cons 1 1 3)) (cons 2 0 146)
def unaryBudget (a b : ℕ) :=
  4+1+PCPPRequestTaggedCons.budget b 0+1+PCPPRequestTaggedCons.budget a (middle b 0 false)

theorem unary_run (a b c pa pb pc : ℕ) :
    ∃ out,ClockJoin.ReadyRun unary (unaryBudget a b) (input a b c false pa pb pc) out ∧
      (∃ padding,out 222=frame (result a b c false).bits++List.replicate padding false) ∧
      out 232=(result a b c false).bits := by
  obtain ⟨printed,hp,pzero,pkeep⟩ := printer_run a b c false pa pb pc
  have pfresh (i : Fin 234) (hi : 6 ≤ i.val) : printed i=[] := by
    have h0 : i≠0 := by intro h; subst i; contradiction
    have h1 : i≠1 := by intro h; subst i; contradiction
    have h2 : i≠2 := by intro h; subst i; contradiction
    have h3 : i≠3 := by intro h; subst i; contradiction
    have h4 : i≠4 := by intro h; subst i; contradiction
    have h5 : i≠5 := by intro h; subst i; contradiction
    rw [pkeep i h3 h4]
    simp [input,h0,h1,h2,h5]
  obtain ⟨second,hs,⟨padding,st⟩,_,skeep⟩ := stage_ready printed 1 1 3
    (by decide) (by decide) (by decide) b 0 pb 0
    (by rw [pkeep 1 (by decide) (by decide)]; rfl)
    (by simpa only [List.replicate_zero,List.append_nil] using pzero)
    (by intro i hi _; exact pfresh i (by change 82 ≤ i.val at hi; omega))
  obtain ⟨last,hl,lf,lr,_⟩ := stage_ready second 2 0 146
    (by decide) (by decide) (by decide) a (middle b 0 false) pa padding
    (by rw [skeep 0 (by decide) (by decide) (by decide),pkeep 0 (by decide) (by decide)]; rfl)
    st
    (by
      intro i hi _
      have hib : 158 ≤ i.val := hi
      have h1 : (1 : Fin 234)≠i := by intro h; subst i; contradiction
      have h3 : (3 : Fin 234)≠i := by intro h; subst i; contradiction
      rw [skeep i h1 h3 (Or.inr hib)]
      exact pfresh i (by omega))
  exact ⟨last,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hp hs) hl,lf,lr⟩

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
