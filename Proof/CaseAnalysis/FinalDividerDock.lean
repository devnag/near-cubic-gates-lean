import Proof.CaseAnalysis.FinalWordEngines
import Proof.MachineModel.OrdinaryMatrixBucketDivide

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10DividerDock

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines (dockH_all_zero product_dock)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The unary floor divider, docked -/

theorem divideInput_eq (n d : ℕ) :
    MatrixBucketDivide.resetInput n d =
      (![List.replicate n true, UnaryTemplate.tape d, [], []] : Fin 4 → List Bool) := by
  funext i
  fin_cases i <;> rfl

/-- **The unary floor division, docked.**  The dividend slot and the
`UnaryTemplate.tape` divisor slot are both RESTORED, `slots 2` carries
`List.replicate (n / d) true`, `slots 3` is the single private scratch tape,
every head is zero on entry and exit, and every tape outside the slot map is
untouched. -/
theorem divide_dock {m : ℕ} (n d : ℕ) (hd : 0 < d) (slots : Fin 4 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate n true)
    (h1 : A (slots 1) = UnaryTemplate.tape d)
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots MatrixBucketDivide.machine) (8 * n + 6) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate n true ∧
      A' (slots 1) = UnaryTemplate.tape d ∧
      A' (slots 2) = List.replicate (n / d) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, t0, t1, t2, hheads, hsteps⟩ := MatrixBucketDivide.divide_run n d hd
  rw [divideInput_eq] at hrun
  have hstep : Step MatrixBucketDivide.machine (8 * n + 6) (fun _ => 0)
      (![List.replicate n true, UnaryTemplate.tape d, [], []] : Fin 4 → List Bool)
      (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, hsteps⟩
  have hA : ∀ j : Fin 4,
      A (slots j) =
        (![List.replicate n true, UnaryTemplate.tape d, [], []] : Fin 4 → List Bool) j := by
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

/-! ## §2 `rowAnswer * denominator / rowDenominator`, on one tape -/

/-- The multiplier's four slots inside the seven-slot answer window. -/
def prodIdx : Fin 4 → Fin 7 := ![0, 1, 2, 3]

/-- The divider's four slots inside the same window: the product's output slot
`2` is the dividend, and the divisor, quotient and scratch are fresh. -/
def divIdx : Fin 4 → Fin 7 := ![2, 4, 5, 6]

theorem prodIdx_injective : Function.Injective prodIdx := by decide
theorem divIdx_injective : Function.Injective divIdx := by decide
theorem prodIdx_ne_four : ∀ j : Fin 4, prodIdx j ≠ (4 : Fin 7) := by decide
theorem prodIdx_ne_five : ∀ j : Fin 4, prodIdx j ≠ (5 : Fin 7) := by decide
theorem prodIdx_ne_six : ∀ j : Fin 4, prodIdx j ≠ (6 : Fin 7) := by decide
theorem divIdx_ne_zero : ∀ j : Fin 4, divIdx j ≠ (0 : Fin 7) := by decide
theorem divIdx_ne_one : ∀ j : Fin 4, divIdx j ≠ (1 : Fin 7) := by decide

noncomputable def answerMachine {m : ℕ} (slots : Fin 7 → Fin m) :=
  Composition.machine
    (RecoveryFocus.machine (fun j => slots (prodIdx j)) ClockUnaryProduct.machine)
    (RecoveryFocus.machine (fun j => slots (divIdx j)) MatrixBucketDivide.machine)

/-- **`answer`'s arithmetic, realised.**  One `Step` of one machine takes
`List.replicate a true`, `CompareMachine.word b` and `UnaryTemplate.tape c` to
`List.replicate (a * b / c) true` -- the floor quotient
`rowAnswer * denominator / rowDenominator` of `answer`
(`Proof/CaseAnalysis/FinalSupplierWidth.lean`) -- with the three operand slots
restored, all heads zero on entry and exit, and every tape outside the window
untouched.  `slots 3` and `slots 6` are the two private scratch tapes. -/
theorem answer_dock {m : ℕ} (a b c : ℕ) (hc : 0 < c) (slots : Fin 7 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate a true)
    (h1 : A (slots 1) = CompareMachine.word b)
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = [])
    (h4 : A (slots 4) = UnaryTemplate.tape c)
    (h5 : A (slots 5) = [])
    (h6 : A (slots 6) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (answerMachine slots)
        (2 * (a * (2 * b + 3) + 2) + 2 + 1 + (8 * (a * b) + 6)) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate a true ∧
      A' (slots 1) = CompareMachine.word b ∧
      A' (slots 4) = UnaryTemplate.tape c ∧
      A' (slots 5) = List.replicate (a * b / c) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H₁, A₁, hstep₁, hzero₁, q0, q1, q2, qrest⟩ :=
    product_dock a b (fun j => slots (prodIdx j)) (hinj.comp prodIdx_injective) H A hH
      h0 h1 h2 h3
  have hq4 : A₁ (slots 4) = UnaryTemplate.tape c :=
    (qrest (slots 4) (fun j => hinj.ne (prodIdx_ne_four j))).trans h4
  have hq5 : A₁ (slots 5) = [] :=
    (qrest (slots 5) (fun j => hinj.ne (prodIdx_ne_five j))).trans h5
  have hq6 : A₁ (slots 6) = [] :=
    (qrest (slots 6) (fun j => hinj.ne (prodIdx_ne_six j))).trans h6
  obtain ⟨H₂, A₂, hstep₂, hzero₂, r0, r1, r2, rrest⟩ :=
    divide_dock (a * b) c hc (fun j => slots (divIdx j)) (hinj.comp divIdx_injective) H₁ A₁
      hzero₁ q2 hq4 hq5 hq6
  refine ⟨H₂, A₂, hstep₁.seq hstep₂, hzero₂, ?_, ?_, r1, r2, ?_⟩
  · exact (rrest (slots 0) (fun j => hinj.ne (divIdx_ne_zero j))).trans q0
  · exact (rrest (slots 1) (fun j => hinj.ne (divIdx_ne_one j))).trans q1
  · intro i hi
    exact (rrest i (fun j => hi (divIdx j))).trans (qrest i (fun j => hi (prodIdx j)))

end NearCubicWires.RepairOrdinary.CloseoutFinalC10DividerDock
