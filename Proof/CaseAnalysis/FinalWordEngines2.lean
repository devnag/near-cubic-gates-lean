import Proof.CaseAnalysis.FinalWordEngines
import Proof.PCP.ProjectionNormalizationCounter
import Proof.MachineModel.ClockScalarFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines2

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines (dockH_all_zero)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairSource hiding frame
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The sentinel counter, docked (engine 5) -/

theorem counterInput_eq (n : ℕ) :
    ProjectionNormalization.Counter.input n =
      (![List.replicate n true, [], [], []] : Fin 4 → List Bool) := rfl

/-- **The unary-to-sentinel counter, docked.**  The unary input on `slots 0`
is RESTORED, the sentinel word lands on `slots 2`; `slots 1` and `slots 3`
are the two private scratch tapes. -/
theorem counter_dock {m : ℕ} (n : ℕ) (slots : Fin 4 → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate n true)
    (h1 : A (slots 1) = []) (h2 : A (slots 2) = []) (h3 : A (slots 3) = []) :
    ∃ H' A', Step (RecoveryFocus.machine slots ProjectionNormalization.Counter.machine)
        (ProjectionNormalization.Counter.budget n) H A H' A' ∧ (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate n true ∧ A' (slots 2) = CompareMachine.word n ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, t0, t2, hheads, hsteps⟩ := ProjectionNormalization.Counter.counter_run n
  rw [counterInput_eq] at hrun
  have hstep : Step ProjectionNormalization.Counter.machine
      (ProjectionNormalization.Counter.budget n) (fun _ => 0)
      ![List.replicate n true, [], [], []] (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, le_of_eq hsteps⟩
  have hA : ∀ j : Fin 4,
      A (slots j) = (![List.replicate n true, [], [], []] : Fin 4 → List Bool) j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A rc.final.tapes 0).trans t0
  · exact (install_slot slots hinj A rc.final.tapes 2).trans t2
  · intro i hi
    exact install_other slots A rc.final.tapes i hi

/-! ## §2 The width normalizer, docked (engine 6) -/

theorem normalizeInput_eq (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits =
      (![List.replicate width true, frame bits, [], [], []] : Fin 5 → List Bool) := by
  funext i
  fin_cases i <;> rfl

/-- **The width normalizer, docked.**  The unary driver on `slots 0` and the
framed source on `slots 1` are both RESTORED; the source re-encoded at the
driver's width lands on `slots 2`; `slots 3` and `slots 4` are the two
private scratch tapes. -/
theorem normalize_dock {m : ℕ} (width : ℕ) (bits : List Bool) (hbits : bits.length ≤ width)
    (slots : Fin 5 → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate width true) (h1 : A (slots 1) = frame bits)
    (h2 : A (slots 2) = []) (h3 : A (slots 3) = []) (h4 : A (slots 4) = []) :
    ∃ H' A', Step (RecoveryFocus.machine slots ClockNormalize.machine) (4*width+4) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate width true ∧ A' (slots 1) = frame bits ∧
      A' (slots 2) = frame (binary width (value bits)) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, t0, t1, t2, _t3, _t4, hheads, hsteps⟩ :=
    ClockScalarFields.scalar_run width bits hbits
  rw [normalizeInput_eq] at hrun
  have hstep : Step ClockNormalize.machine (4 * width + 4) (fun _ => 0)
      ![List.replicate width true, frame bits, [], [], []] (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, le_of_eq hsteps⟩
  have hA : ∀ j : Fin 5,
      A (slots j) =
        (![List.replicate width true, frame bits, [], [], []] : Fin 5 → List Bool) j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A rc.final.tapes 0).trans t0
  · exact (install_slot slots hinj A rc.final.tapes 1).trans t1
  · exact (install_slot slots hinj A rc.final.tapes 2).trans t2
  · intro i hi
    exact install_other slots A rc.final.tapes i hi

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines2
