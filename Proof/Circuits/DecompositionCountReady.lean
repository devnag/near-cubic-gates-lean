import Proof.Circuits.DecompositionCountProduct
import Proof.Circuits.DecompositionCountPosition

/-! Complete count preparation at the literal native-reader head positions.
Two executed moves bracket the checked copies and product. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCountReady
open LocalBitMultitape DecompositionCountPosition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := Composition.machine (move retreat) DecompositionCountDrivers.machine
noncomputable def machine := Composition.machine first (move advance)
def budget (a m : ℕ) := DecompositionCountDrivers.budget a m+4
noncomputable def entry (a m : ℕ) :=
  (⟨machine.start,nativeHeads,DecompositionCountDrivers.input a m⟩ : Configuration 14 _)

theorem counts_run (a m : ℕ) :
    ∃ r,runFrom machine (budget a m) (entry a m)=some r ∧
      r.final.heads=loopHeads ∧ r.final.tapes=DecompositionCountDrivers.output a m ∧
      r.steps ≤ budget a m := by
  obtain ⟨firstR,hfirst,ff,fs⟩ := retreat_run (DecompositionCountDrivers.input a m)
  obtain ⟨body,hbody,bt,bh,bs⟩ := DecompositionCountDrivers.counts_ready a m
  have hb : Composition.restart firstR.final DecompositionCountDrivers.machine.start=
      initialConfiguration DecompositionCountDrivers.machine (DecompositionCountDrivers.input a m) := by
    rw [ff]
    rfl
  have hb' : runFrom DecompositionCountDrivers.machine (DecompositionCountDrivers.budget a m)
      (Composition.restart firstR.final DecompositionCountDrivers.machine.start)=some body := by
    rw [hb]
    exact hbody
  have hmid := Composition.run_join (move retreat) DecompositionCountDrivers.machine
    _ _ _ firstR body hfirst hb'
  obtain ⟨last,hl,lf,ls⟩ := advance_run (DecompositionCountDrivers.output a m)
  have he : Composition.restart (Composition.joinedReceipt firstR body).final (move advance).start=
      initialConfiguration (move advance) (DecompositionCountDrivers.output a m) := by
    apply configuration_ext
    · rfl
    · funext i; exact bh i
    · exact bt
  have hl' : runFrom (move advance) 1
      (Composition.restart (Composition.joinedReceipt firstR body).final (move advance).start)=some last := by
    rw [he]
    exact hl
  have whole := Composition.run_join first (move advance) _ _ _
    (Composition.joinedReceipt firstR body) last hmid hl'
  have htime : (1+1+DecompositionCountDrivers.budget a m)+1+1=budget a m := by
    unfold budget
    omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt firstR body) last,whole,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
  · change last.final.tapes=_
    rw [lf]
  · change firstR.steps+1+body.steps+1+last.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionCountReady
