import Proof.PCP.PCPPRequestNodeCodeReady

namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def binary := Composition.machine
  (Composition.machine (Composition.machine printer (cons 0 2 3)) (cons 1 1 70)) (cons 2 0 146)
def binaryBudget (a b c : ℕ) :=
  4+1+PCPPRequestTaggedCons.budget c 0+1+
    PCPPRequestTaggedCons.budget b (Nat.pair 1 (Nat.pair c 0))+1+
    PCPPRequestTaggedCons.budget a (middle b c true)

theorem binary_run (a b c pa pb pc : ℕ) :
    ∃ out,ClockJoin.ReadyRun binary (binaryBudget a b c) (input a b c true pa pb pc) out ∧
      (∃ padding,out 222=frame (result a b c true).bits++List.replicate padding false) ∧
      out 232=(result a b c true).bits := by
  obtain ⟨printed,hp,pzero,pkeep⟩ := printer_run a b c true pa pb pc
  have pfresh (i : Fin 234) (hi : 6 ≤ i.val) : printed i=[] := by
    have h0 : i≠0 := by intro h; subst i; contradiction
    have h1 : i≠1 := by intro h; subst i; contradiction
    have h2 : i≠2 := by intro h; subst i; contradiction
    have h3 : i≠3 := by intro h; subst i; contradiction
    have h4 : i≠4 := by intro h; subst i; contradiction
    have h5 : i≠5 := by intro h; subst i; contradiction
    rw [pkeep i h3 h4]
    simp [input,h0,h1,h2,h5]
  obtain ⟨first,hf,⟨padding1,ft⟩,_,fkeep⟩ := stage_ready printed 0 2 3
    (by decide) (by decide) (by decide) c 0 pc 0
    (by rw [pkeep 2 (by decide) (by decide)]; rfl)
    (by simpa only [List.replicate_zero,List.append_nil] using pzero)
    (by intro i hi _; exact pfresh i hi)
  obtain ⟨second,hs,⟨padding2,st⟩,_,skeep⟩ := stage_ready first 1 1 70
    (by decide) (by decide) (by decide) b (Nat.pair 1 (Nat.pair c 0)) pb padding1
    (by rw [fkeep 1 (by decide) (by decide) (by decide),pkeep 1 (by decide) (by decide)]; rfl)
    ft
    (by
      intro i hi _
      have hib : 82 ≤ i.val := hi
      have h2 : (2 : Fin 234)≠i := by intro h; subst i; contradiction
      have h3 : (3 : Fin 234)≠i := by intro h; subst i; contradiction
      rw [fkeep i h2 h3 (Or.inr hib)]
      exact pfresh i (by omega))
  obtain ⟨last,hl,lf,lr,_⟩ := stage_ready second 2 0 146
    (by decide) (by decide) (by decide) a (middle b c true) pa padding2
    (by rw [skeep 0 (by decide) (by decide) (by decide),
      fkeep 0 (by decide) (by decide) (by decide),pkeep 0 (by decide) (by decide)]; rfl)
    st
    (by
      intro i hi _
      have hib : 158 ≤ i.val := hi
      have h1 : (1 : Fin 234)≠i := by intro h; subst i; contradiction
      have h2 : (2 : Fin 234)≠i := by intro h; subst i; contradiction
      have h3 : (3 : Fin 234)≠i := by intro h; subst i; contradiction
      have h70 : (70 : Fin 234)≠i := by intro h; subst i; contradiction
      rw [skeep i h1 h70 (Or.inr hib),fkeep i h2 h3 (Or.inr (by change 82 ≤ i.val; omega))]
      exact pfresh i (by omega))
  exact ⟨last,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hp hf) hs) hl,lf,lr⟩

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
