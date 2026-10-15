import Proof.Amplification.RecoverySubtract

/-! The restoring radix-4 invariant used by the actual ordinary unpair loop.
Every round uses shifts, comparison and one bounded subtraction. Neither the
number of rounds nor any arithmetic loop depends on the numeric query value. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.RestoringRoot
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  root : Nat
  remainder : Nat
  deriving DecidableEq

def Good (state : State) (value : Nat) : Prop :=
  state.root ^ 2 + state.remainder = value ∧ state.remainder < 2 * state.root + 1

def digitStep (state : State) (digit : Fin 4) : State :=
  let shifted := 4 * state.remainder + digit.val
  let trial := 4 * state.root + 1
  if shifted < trial then ⟨2 * state.root, shifted⟩
  else ⟨2 * state.root + 1, shifted - trial⟩

theorem digitStep_good (state : State) (value : Nat) (digit : Fin 4)
    (hgood : Good state value) : Good (digitStep state digit) (4 * value + digit.val) := by
  obtain ⟨heq, hrem⟩ := hgood
  have hd := digit.isLt
  dsimp only [digitStep, Good]
  split
  · next h => constructor <;> dsimp <;> nlinarith
  · next h =>
    have hsub : 4 * state.remainder + digit.val - (4 * state.root + 1) + (4 * state.root + 1) =
        4 * state.remainder + digit.val := Nat.sub_add_cancel (by omega)
    constructor <;> dsimp <;> nlinarith

def execute (digits : List (Fin 4)) (initial : State) : State := digits.foldl digitStep initial
def value (digits : List (Fin 4)) (initial : Nat) : Nat := digits.foldl (fun n digit => 4 * n + digit.val) initial

theorem execute_good (digits : List (Fin 4)) (initial : State) (initialValue : Nat)
    (hgood : Good initial initialValue) : Good (execute digits initial) (value digits initialValue) := by
  induction digits generalizing initial initialValue with
  | nil => exact hgood
  | cons digit digits ih => exact ih _ _ (digitStep_good initial initialValue digit hgood)

def zero : State := ⟨0, 0⟩

theorem execute_zero_good (digits : List (Fin 4)) : Good (execute digits zero) (value digits 0) :=
  execute_good digits zero 0 (by simp [Good, zero])

theorem root_eq_sqrt {state : State} {n : Nat} (hgood : Good state n) : state.root = Nat.sqrt n := by
  apply Nat.eq_sqrt'.mpr
  constructor <;> obtain ⟨heq, hrem⟩ := hgood <;> nlinarith

def finish (state : State) : Nat × Nat :=
  if state.remainder < state.root then (state.remainder, state.root)
  else (state.root, state.remainder - state.root)

theorem finish_eq_unpair {state : State} {n : Nat} (hgood : Good state n) : finish state = Nat.unpair n := by
  have hroot := root_eq_sqrt hgood
  have hrem : state.remainder = n - state.root * state.root := by
    have h := hgood.1
    simp only [pow_two] at h
    omega
  simp only [finish, Nat.unpair, ← hroot, ← hrem]

theorem execute_unpair (digits : List (Fin 4)) :
    finish (execute digits zero) = Nat.unpair (value digits 0) := finish_eq_unpair (execute_zero_good digits)

theorem digitStep_width {state : State} {n width : Nat} (digit : Fin 4)
    (hgood : Good state n) (hn : n < 2 ^ width) :
    4 * state.remainder + digit.val < 2 ^ (width + 3) ∧
    4 * state.root + 1 < 2 ^ (width + 3) ∧
    2 * state.root + 1 < 2 ^ (width + 3) ∧
    (digitStep state digit).root < 2 ^ (width + 3) ∧
    (digitStep state digit).remainder < 2 ^ (width + 3) := by
  have hr : state.remainder ≤ n := by have h := hgood.1; omega
  have hq : state.root ≤ n := by have h := hgood.1; nlinarith
  have hd := digit.isLt
  have hp : 2 ^ (width + 3) = 8 * 2 ^ width := by rw [pow_add]; ring
  have hshift : 4 * state.remainder + digit.val < 2 ^ (width + 3) := by rw [hp]; omega
  have htrial : 4 * state.root + 1 < 2 ^ (width + 3) := by rw [hp]; omega
  have hdouble : 2 * state.root + 1 < 2 ^ (width + 3) := by rw [hp]; omega
  refine ⟨hshift, htrial, hdouble, ?_, ?_⟩
  · dsimp only [digitStep]
    split <;> dsimp <;> omega
  · dsimp only [digitStep]
    split <;> dsimp <;> omega

end NearCubicWires.RepairSource.RecoveryOracle.RestoringRoot
