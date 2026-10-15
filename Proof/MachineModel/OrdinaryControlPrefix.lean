import Proof.Foundations.OrdinaryExecutionPrefix

/-! Actual finite execution prefixes transported into a larger controller.
The radix loop needs this boundary because a body halt is followed by a real
return transition in the enclosing controller. No time is assigned to a
semantic function: prefixes are extracted from interpreter receipts. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Prefix.enlarge {t s small large n : ℕ} {p : Machine t s}
    {c d : Configuration t s} (h : Prefix p small n c d) (hl : small ≤ large) :
    Prefix p large n c d := by
  induction h with
  | refl c hc => exact Prefix.refl c (hc.trans hl)
  | step hc hn hs _ ih => exact Prefix.step (hc.trans hl) hn hs ih

theorem prefix_of_run {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) :
    Prefix p r.peakTapeCells r.steps c r.final ∧ p.halted r.final.control = true := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · next hc => cases hr; exact ⟨Prefix.refl _ (Nat.le_refl _), hc⟩
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · next hc => cases hr; exact ⟨Prefix.refl _ (Nat.le_refl _), hc⟩
    · next hc =>
      have hnot : p.halted c.control = false := by simpa using hc
      cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst r
          obtain ⟨hp, hh⟩ := ih d tail ht
          exact ⟨Prefix.step (Nat.le_max_left _ _) hnot hs (hp.enlarge (Nat.le_max_right _ _)), hh⟩

def controlConfig {t s u : ℕ} (f : Fin s → Fin u) (c : Configuration t s) : Configuration t u where
  control := f c.control
  heads := c.heads
  tapes := c.tapes

theorem Prefix.mapControl {t s u space n : ℕ} {p : Machine t s} {q : Machine t u}
    (f : Fin s → Fin u)
    (hn : ∀ c : Configuration t s, p.halted c.control = false → q.halted (f c.control) = false)
    (hs : ∀ c d : Configuration t s, p.halted c.control = false →
      LocalBitMultitape.step p c = some d →
        LocalBitMultitape.step q (controlConfig f c) = some (controlConfig f d))
    {c d : Configuration t s} (h : Prefix p space n c d) :
    Prefix q space n (controlConfig f c) (controlConfig f d) := by
  induction h with
  | refl c hc => exact Prefix.refl _ hc
  | @step n c d e hc hnot hstep _ ih =>
    exact Prefix.step hc (hn c hnot) (hs c d hnot hstep) ih

end NearCubicWires.RepairOrdinary
