import Proof.CaseAnalysis.FinalDimensionWords

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Heads stay at zero under docking -/

theorem dockH_all_zero {t m : ℕ} (slots : Fin t → Fin m) (H : Fin m → ℕ)
    (hH : ∀ i, H i = 0) : ∀ i, dockH slots H (fun _ => 0) i = 0 := by
  intro i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp only [dockH, hp]; exact hH i
  | some j => simp only [dockH, hp]

/-! ## §2 The unary sum, and the copier it contains -/

theorem sum_dock {m : ℕ} (r s : ℕ) (slots : Fin 4 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate r true)
    (h1 : A (slots 1) = List.replicate s true)
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots ClockUnarySum.machine) (2 * (r + s) + 6) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate r true ∧
      A' (slots 1) = List.replicate s true ∧
      A' (slots 2) = List.replicate (r + s) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, htapes, hheads, hsteps⟩ := ClockUnarySum.sum_ready r s
  have hstep : Step ClockUnarySum.machine (2 * (r + s) + 6) (fun _ => 0)
      ![List.replicate r true, List.replicate s true, [], []] (fun _ => 0)
      ![List.replicate r true, List.replicate s true, List.replicate (r + s) true,
        List.replicate (r + s + 2) false] :=
    ⟨rc, hrun, funext hheads, htapes, hsteps⟩
  have hA : ∀ j : Fin 4,
      A (slots j) = (![List.replicate r true, List.replicate s true, [], []] : Fin 4 → List Bool) j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_, ?_⟩
  · exact install_slot slots hinj A _ 0
  · exact install_slot slots hinj A _ 1
  · exact install_slot slots hinj A _ 2
  · intro i hi
    exact install_other slots A _ i hi

/-- **The unary copier.**  `sum_dock` at `s = 0`: the second input slot is the
empty tape and stays empty, so a single blank slot serves every copy. -/
theorem copy_dock {m : ℕ} (r : ℕ) (slots : Fin 4 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate r true)
    (h1 : A (slots 1) = [])
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots ClockUnarySum.machine) (2 * (r + 0) + 6) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate r true ∧
      A' (slots 1) = [] ∧
      A' (slots 2) = List.replicate r true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H', A', hstep, hzero, p0, p1, p2, prest⟩ :=
    sum_dock r 0 slots hinj H A hH h0 (by simpa using h1) h2 h3
  refine ⟨H', A', hstep, hzero, p0, by simpa using p1, by simpa using p2, prest⟩

/-! ## §3 The unary product -/

theorem productInput_eq (d e : ℕ) :
    (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      ![List.replicate d true, false :: List.replicate e true, []] (fun _ : Fin 1 => [])) =
      (![List.replicate d true, CompareMachine.word e, [], []] : Fin 4 → List Bool) := by
  funext i
  fin_cases i <;> rfl

/-- **The unary product, docked.**  The multiplicand slot and the
`CompareMachine.word` slot are both RESTORED, so bank tape `90` can be the
second input and comes out unchanged. -/
theorem product_dock {m : ℕ} (d e : ℕ) (slots : Fin 4 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate d true)
    (h1 : A (slots 1) = CompareMachine.word e)
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots ClockUnaryProduct.machine)
        (2 * (d * (2 * e + 3) + 2) + 2) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate d true ∧
      A' (slots 1) = CompareMachine.word e ∧
      A' (slots 2) = List.replicate (d * e) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, t0, t1, t2, _t3, hheads, hsteps⟩ := ClockUnaryProduct.product_run d e
  rw [productInput_eq] at hrun
  have hstep : Step ClockUnaryProduct.machine (2 * (d * (2 * e + 3) + 2) + 2) (fun _ => 0)
      ![List.replicate d true, CompareMachine.word e, [], []] (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, le_of_eq hsteps⟩
  have hA : ∀ j : Fin 4,
      A (slots j) =
        (![List.replicate d true, CompareMachine.word e, [], []] : Fin 4 → List Bool) j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A rc.final.tapes 0).trans t0
  · exact (install_slot slots hinj A rc.final.tapes 1).trans t1
  · exact (install_slot slots hinj A rc.final.tapes 2).trans t2
  · intro i hi
    exact install_other slots A rc.final.tapes i hi

/-! ## §4 The fixed-word writer -/

/-- **Any fixed word, docked.**  Both slots start empty; the word lands on
`slots 0` and `slots 1` is the single private scratch tape. -/
theorem fixedWord_dock {m : ℕ} (bits : List Bool) (slots : Fin 2 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = [])
    (h1 : A (slots 1) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots (HierarchyFixedWord.machine bits))
        (2 * bits.length + 2) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = bits ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  have hstep : Step (HierarchyFixedWord.machine bits) (2 * bits.length + 2) (fun _ => 0)
      (fun _ => []) (fun _ => 0) ![bits, List.replicate bits.length false] :=
    Step.of_ready (HierarchyFixedWord.word_ready bits)
  have hA : ∀ j : Fin 2, A (slots j) = (fun _ : Fin 2 => ([] : List Bool)) j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_⟩
  · exact install_slot slots hinj A _ 0
  · intro i hi
    exact install_other slots A _ i hi

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines
