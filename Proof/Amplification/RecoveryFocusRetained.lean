import Proof.Amplification.RecoveryClauseEvaluationInvariant

/-! Unselected tape contents survive every actual focused run, including a
malformed-input return whose selected workspace has no successful shape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFocus
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem step_other {t u s : Nat} (slot : Fin t→Fin u) (p : Machine t s)
    (i : Fin u) (hi : ∀ j,slot j≠i) (c d : Configuration u s)
    (hs : step (machine slot p) c=some d) : d.tapes i=c.tapes i := by
  have hp : pick slot i=none := by
    classical
    simp [pick,show ¬∃ j,slot j=i by simpa using hi]
  change ((p.rule c.control (c.scanned ∘ slot)).map (action slot)).map (applyAction c)=some d at hs
  cases ha : p.rule c.control (c.scanned ∘ slot) with
  | none => simp [ha] at hs
  | some a =>
    simp only [ha,Option.map_some,Option.some.injEq] at hs
    rw [← hs]
    simp [applyAction,action,hp]

theorem prefix_other {t u s n space : Nat} (slot : Fin t→Fin u) (p : Machine t s)
    (i : Fin u) (hi : ∀ j,slot j≠i) {c d : Configuration u s}
    (h : Prefix (machine slot p) space n c d) : d.tapes i=c.tapes i := by
  induction h with
  | refl => rfl
  | step hc hn hs tail ih => exact ih.trans (step_other slot p i hi _ _ hs)

theorem run_other {t u s : Nat} (slot : Fin t→Fin u) (p : Machine t s)
    (i : Fin u) (hi : ∀ j,slot j≠i) (fuel : Nat) (c : Configuration u s)
    (r : ExecutionReceipt u s) (hr : runFrom (machine slot p) fuel c=some r) :
    r.final.tapes i=c.tapes i := by
  obtain ⟨h,_⟩ := prefix_of_run (machine slot p) fuel c r hr
  exact prefix_other slot p i hi h

end NearCubicWires.RepairOrdinary.RecoveryFocus

namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution

theorem ready_of_run {t s : Nat} (p : Machine t s) (fuel : Nat) (input : Fin t→List Bool)
    (r : ExecutionReceipt t s) (hr : run p fuel input=some r) (hh : ∀ i,r.final.heads i=0) :
    ReadyRun p r.steps input r.final.tapes := by
  obtain ⟨hp,hhalt⟩ := prefix_of_run p fuel _ r hr
  have h : Timed p r.steps (initialConfiguration p input) r.final := ⟨r.peakTapeCells,hp⟩
  obtain ⟨out,hrun,hf,hs⟩ := h.run hhalt
  exact ⟨out,hrun,by rw [hf],by intro i; rw [hf]; exact hh i,hs⟩

end NearCubicWires.RepairOrdinary.RecoveryRootRound
