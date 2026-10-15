import Proof.CaseAnalysis.FinalCompareDockField
import Proof.Hierarchy.CompetitorThresholdDecision

/-! **Decision tail, stage 2a-iii — the comparator, docked.**

Paper C.10 (~4103): validity passes only if the first estimated average is at
most `2*zeta` and every second moment at most `1+zeta`; C.10.1: accept only if
`mu~ >= theta_acc`. `CompetitorThresholdDecision.threshold_run` is the one
physical comparator all three tests specialise (`lower := false` with
`meanThreshold`/`momentThreshold`; `lower := true` with `acceptanceThreshold`,
which is literally `midpoint`). It runs on its own `Fin 67` bank from heads `0`
and leaves its verdict at `readTapeBit (out 65) 0`.

Here it is docked into an arbitrary larger bank by an injective slot map. Heads
outside the block are untouched (`dockH_existing`), tapes outside the block are
untouched (`install_other`), and the verdict is read off `install_slot`. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorThresholdDecision
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairOrdinary.RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The comparator as a docked `Step`.** Given the comparator's input already
laid on the block `cmpSlots`, with block heads at `0`, one run leaves the block
heads at `0`, the rest of the bank untouched, and the verdict bit on slot `65`. -/
theorem compare_step {u : ℕ} (lower : Bool) (b p n d : ℕ) (q : ℚ)
    (hp : p < 2^b) (hn : n < 2^b) (hd : d < 2^b) (hdpos : 0 < d)
    (hq : 0 ≤ q) (hqnum : numerator q < 2^b) (hqden : q.den < 2^b)
    (cmpSlots : Fin 67 → Fin u) (hi : Function.Injective cmpSlots)
    (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (cmpSlots j) = 0)
    (hA : ∀ j, A (cmpSlots j) = input lower b p n d q j) :
    ∃ out : Fin 67 → List Bool,
      Step (RecoveryFocus.machine cmpSlots CompetitorRationalDecision.machine)
        (2000*(b+1)^2) H A H (install cmpSlots A out) ∧
      (readTapeBit (out 65) 0 = true ↔ passes lower p n d q) := by
  obtain ⟨out, hrun, hiff⟩ := threshold_run lower b p n d q hp hn hd hdpos hq hqnum hqden
  have hstep := (step_of_clock hrun).dock cmpSlots hi H A hH hA
  rw [dockH_existing cmpSlots H (fun _ => 0) hH] at hstep
  exact ⟨out, hstep, hiff⟩

/-- The verdict bit, read off the docked bank. -/
theorem compare_flag {u : ℕ} (cmpSlots : Fin 67 → Fin u) (hi : Function.Injective cmpSlots)
    (A : Fin u → List Bool) (out : Fin 67 → List Bool) :
    install cmpSlots A out (cmpSlots 65) = out 65 :=
  install_slot cmpSlots hi A out 65

/-- Tapes outside the comparator block are untouched. -/
theorem compare_other {u : ℕ} (cmpSlots : Fin 67 → Fin u)
    (A : Fin u → List Bool) (out : Fin 67 → List Bool) (i : Fin u)
    (hi : ∀ j, cmpSlots j ≠ i) :
    install cmpSlots A out i = A i :=
  install_other cmpSlots A out i hi

end NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp
