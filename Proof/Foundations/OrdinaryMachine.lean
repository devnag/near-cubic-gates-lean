import Proof.Foundations.LocalBitMultitapeCore
import StatementSupport

/-!
The shared ordinary-machine boundary for the source-correspondence repair.
Every execution statement is about the finite local interpreter. Framing,
output allocation and later head resets are charged by actual programs.
The legacy `Machine.descriptionBits` annotation supplies no size evidence.
-/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem frame_length (bs : List Bool) :
    (frame bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => simp [frame]
  | cons b bs ih => simp [frame, ih]; omega

/-- A composable result must also give the actual final head positions;
    restarting a machine with heads at zero is not a free operation. -/
structure RewoundWordFunction (Request : Type)
    (input output : Request → List Bool) (budget : Request → ℕ)
    extends WordFunction Request input output budget where
  headsReset : ∀ r receipt,
    run program.machine (budget r) (program.inputTapes (input r)) = some receipt →
      ∀ tape, receipt.final.heads tape = 0

@[ext] theorem configuration_ext {t s : ℕ} {a b : Configuration t s}
    (hc : a.control = b.control) (hh : a.heads = b.heads)
    (ht : a.tapes = b.tapes) : a = b := by
  cases a; cases b; cases hc; cases hh; cases ht; rfl

theorem runFrom_moreFuel {t s : ℕ} (machine : Machine t s)
    (fuel extra : ℕ) (configuration : Configuration t s)
    (receipt : ExecutionReceipt t s)
    (hrun : runFrom machine fuel configuration = some receipt) :
    runFrom machine (fuel + extra) configuration = some receipt := by
  induction fuel generalizing configuration receipt with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        cases extra <;> simp [runFrom, h]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        simp [Nat.succ_add, runFrom, h]
    · next h =>
        split at hrun
        · contradiction
        · next next hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                have hmore := ih next suffix htail
                simp [Nat.succ_add, runFrom, h, hs, hmore]

theorem run_moreFuel {t s : ℕ} (machine : Machine t s)
    (fuel extra : ℕ) (input : Fin t → List Bool)
    (receipt : ExecutionReceipt t s)
    (hrun : run machine fuel input = some receipt) :
    run machine (fuel + extra) input = some receipt :=
  runFrom_moreFuel machine fuel extra _ receipt hrun

def WordFunction.enlargeBudget {Request : Type}
    {input output : Request → List Bool} {budget larger : Request → ℕ}
    (f : WordFunction Request input output budget)
    (h : ∀ r, budget r ≤ larger r) : WordFunction Request input output larger where
  program := f.program
  realizes := by
    intro r
    obtain ⟨receipt, hrun, hout⟩ := f.realizes r
    refine ⟨receipt, ?_, hout⟩
    have hmore := run_moreFuel f.program.machine (budget r)
      (larger r - budget r) _ receipt hrun
    simpa only [Nat.add_sub_of_le (h r)] using hmore

end NearCubicWires.RepairOrdinary
