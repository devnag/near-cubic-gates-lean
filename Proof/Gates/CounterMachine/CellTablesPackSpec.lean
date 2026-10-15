import Proof.Gates.CounterMachine.CellTablesSet

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (WordFunction)

/-- R's size constants with `a₃` multiplied by `2^{n₀ − kLow c_T L}`. -/
def zK (z : Sz) (cT n0 L : ℕ) : Sz := ⟨z.a1, z.c1, z.a2, z.c2, 2 ^ (n0 - kLow cT L) * z.a3, z.c3⟩

/-- A bound for the set-up block (`bkA` reads `n₀`, then `kLow`, then `L·`/`2^·` loops). -/
def bkCost (z : Sz) (cT n0 L : ℕ) : ℕ :=
  bkACost L + 1000 * (L + cT + 10) * (L + 2) * (2 ^ L + 2) + (n0 + 1) * (60 * (zK z cT n0 L).Bk L + 100)

/-- **STATEMENT CellTables-SPLIT3 (packaging).** -/
def PackK : Prop :=
  ∀ {V M : ℕ} {Req : Type} (input output : Req → List Bool) (K : Callee) (z : Sz) (cT : ℕ) (n0 : Req → ℕ)
    (main : St V M) (N : Req → ℕ),
    (∀ r, ∃ rest, input r = natWord (n0 r) ++ rest) →
    (∀ r, ∃ b n, Ex (ctxOf K (zK z cT (n0 r) (leadOnes (input r))) (input r)) main a0 b n ∧ b.out = output r ∧
      n ≤ N r) →
    (∀ r, 1 ≤ z.W (leadOnes (input r))) → (∀ r, 2 ^ (leadOnes (input r) + 2) ≤ z.W (leadOnes (input r))) →
    Nonempty (WordFunction Req input output (fun r =>
      langBudget K (zK z cT (n0 r) (leadOnes (input r))) V M (input r) (N r) +
        bkCost z cT (n0 r) (leadOnes (input r))))

end NearCubicGates.Close.CounterMachine.CellTablesProg
