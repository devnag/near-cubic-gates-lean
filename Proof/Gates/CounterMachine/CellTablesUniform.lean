import Proof.Gates.CounterMachine.CellTablesTarget

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def CellTablesUniform (B1 B2 : ℕ) : Prop :=
  ∀ (PolyTab : TabMachine) (e0 : ℕ), ∃ E : ℕ, ∀ (cT : ℕ) (RK : TabCallMachine B1 B2 cT PolyTab) (C0 : ℕ),
    (∀ x : TabCallReq B1 B2 cT, RK.budget x ≤ C0 * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e0) →
    ∃ (CellTables : TablesMachine B1 B2 cT) (C : ℕ), ∀ r : CellReq B1 B2 cT,
      CellTables.budget r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + E)

end NearCubicGates.Close.CounterMachine
