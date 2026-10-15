import Proof.CaseAnalysis.FinalCompareDock
import Proof.Amplification.RecoveryRootRoundTapes
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.ClockNormalize
import Proof.MachineModel.Runs
import Proof.MachineModel.Layout

/-! **Decision tail, stage 2a-i — the two constant stages, as `Step`s.**

The comparator (`CompetitorThresholdDecision.threshold_run`) wants its threshold
`numerator q`, `q.den`, the literal `0`, and a unary width driver as framed words
on fixed tapes. `HierarchyFixedWord.word_ready` writes any literal list from
blanks; `ClockNormalize.normalize_run` widens a `binary` word. Both are stated as
ready-runs with heads returning to `0`; here they become docked `Step`s so the
whole tail can be sequenced by `Step.seq`. No new machine, no new constant. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch HierarchyFixedWord ClockNormalize

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clock_of_root {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p n input output) : ClockJoin.ReadyRun p n input output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  exact ⟨r, hr, ht, hh, hs.le⟩

theorem step_of_root {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p n input output) :
    Step p n (fun _ => 0) input (fun _ => 0) output :=
  Step.of_ready h

/-- The clock-join (bounded-time) ready-run is also a `Step`; same proof as
`Step.of_ready` with the budget inequality taken as given. -/
theorem step_of_clock {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n input output) :
    Step p n (fun _ => 0) input (fun _ => 0) output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, ?_, ht, hs⟩
  · change runFrom p n (initialConfiguration p input) = some r at hr
    exact hr
  · funext i; exact hh i

/-- **Literal word.** From two blank tapes, tape 0 receives `bits`. -/
theorem word_step (bits : List Bool) :
    Step (HierarchyFixedWord.machine bits) (2*bits.length+2) (fun _ => 0) (fun _ => [])
      (fun _ => 0) ![bits, List.replicate bits.length false] :=
  step_of_root (word_ready bits)

/-- The normalizer's exit bank. -/
def normalizeOut (width : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  ![List.replicate width true, frame bits, frame (resize width bits),
    [decide (bits.length ≤ width)], List.replicate (2*width+1) false]

/-- **Widening.** `frame bits` on tape 1 becomes `frame (resize width bits)` on tape 2. -/
theorem normalize_step (width : ℕ) (bits : List Bool) :
    Step ClockNormalize.machine (4*width+4) (fun _ => 0) (ClockNormalize.input width bits)
      (fun _ => 0) (normalizeOut width bits) := by
  obtain ⟨r, hr, h0, h1, h2, h3, h4, hh, hs⟩ := normalize_run width bits
  refine Step.of_ready ⟨r, hr, ?_, hh, hs⟩
  funext i
  fin_cases i <;> simp [normalizeOut, h0, h1, h2, h3, h4]

end NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
