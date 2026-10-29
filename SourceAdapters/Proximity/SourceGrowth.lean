import SourceAdapters.Proximity.PolynomialBounds

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual source word controls the number of
coin rows, all source request budgets, and all arithmetic width demands. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Published.CW19Proximity
open Growth

def sourceMeasure (S : SourceCircuit) : ℕ := (sourceCircuitWord S).length

theorem requestCap_bounded (q a : ℕ) :
    Bounded sourceMeasure (fun S => requestCap q a (sourceMeasure S)) :=
  (bounded_const _).mul (bounded_size.add (bounded_const 2))

theorem callBudgetCap_bounded (q a K e : ℕ) :
    Bounded sourceMeasure (fun S => callBudgetCap q a K e (sourceMeasure S)) :=
  (bounded_const K).mul (((requestCap_bounded q a).add (bounded_const 1)).pow e)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q) (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 (sourceMeasure S + 2))

include hr

theorem random_bounded : Bounded sourceMeasure (fun S => (V S).randomBits) :=
  ((bounded_const a).mul (bounded_size.add (bounded_const 2))).mono (random_linear V a hr)

theorem coins_bounded : Bounded sourceMeasure (fun S => 2 ^ (V S).randomBits) := by
  have hbase : Bounded sourceMeasure (fun S => 2 * (sourceMeasure S + 3)) :=
    (bounded_const 2).mul (bounded_size.add (bounded_const 3))
  refine (hbase.pow a).mono (fun S => ?_)
  have hb := binaryBlockSize_le (sourceMeasure S + 2)
  change 2 ^ Nat.clog 2 (sourceMeasure S + 2) ≤ 2 * (sourceMeasure S + 2 + 1) at hb
  calc
    2 ^ (V S).randomBits ≤ 2 ^ (a * Nat.clog 2 (sourceMeasure S + 2)) :=
      Nat.pow_le_pow_right (by decide) (hr S)
    _ = (2 ^ Nat.clog 2 (sourceMeasure S + 2)) ^ a := by rw [Nat.mul_comm a, pow_mul]
    _ ≤ (2 * (sourceMeasure S + 3)) ^ a := Nat.pow_le_pow_left (by simpa [Nat.add_assoc] using hb) a

theorem auxiliaryCap_bounded : Bounded sourceMeasure (fun S => auxiliaryCap q (V S).randomBits) :=
  ((bounded_const 2).mul ((((coins_bounded V a hr).add (bounded_const (blockVariableBound q))).add
    (bounded_const 1)).pow 2)).add (bounded_const 2)

theorem widthMeasure_bounded (K e : ℕ) : Bounded sourceMeasure (fun S =>
    widthMeasure q (V S).randomBits (callBudgetCap q a K e (sourceMeasure S))) :=
  ((((((callBudgetCap_bounded q a K e).add (auxiliaryCap_bounded V a hr)).add
    (bounded_const (blockVariableBound q))).add (bounded_const (2 * q))).add (bounded_const (2 ^ q))).add
    (random_bounded V a hr)).add (bounded_const 20)

theorem widthDemand_bounded (K e : ℕ) : Bounded sourceMeasure (fun S =>
    widthDemand q (sourceMeasure S) (V S).randomBits (callBudgetCap q a K e (sourceMeasure S))) :=
  (((widthMeasure_bounded V a hr K e).add bounded_size).add (bounded_const (predicateBlockBits q))).add
    (bounded_const 10)

end NearCubicGates.Adapters.Proximity.SourceCallee
