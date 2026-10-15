import Proof.Gates.CounterMachine.TabCallCls
import Proof.Gates.CounterMachine.CellTablesUniform
import Proof.Gates.CounterMachine.PrefixFinal
import Proof.Gates.CounterAsm.Statement
import Proof.Gates.Dispatch.Final
import Proof.Gates.Cells.PackSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.Supply

open NearCubicWires NearCubicGates NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine NearCubicGates.Close.CounterAsm

def PolyTabReady : Prop :=
  ∀ _a : NearCubicWires.RepairRepresentation.WilliamsAlgorithm, ∃ PolyTab : TabMachine, ∀ R : TabReq,
    PolyTab.order R = printerOrder R.s

/-- **The producers at any exponents.** -/
theorem counterInputs_of (B1 B2 : ℕ) (PolyTab : TabMachine) (hord : ∀ R : TabReq, PolyTab.order R = printerOrder R.s)
    (hK6 : CellTablesUniform B1 B2) (hCellsProc : Cells.CellsUniform B1 B2) : CounterInputs B1 B2 := by
  obtain ⟨RK, e0, hRK⟩ :=
    TabCallProg.tabCallMachine_uniform B1 B2 PolyTab hord (PrefixProg.prefixMachine B1 B2) (PrefixProg.prefixMachine_uniform B1 B2)
  obtain ⟨E, hE⟩ := hK6 PolyTab e0
  have hk : ∀ cT, ∃ (CellTables : TablesMachine B1 B2 cT) (C : ℕ), ∀ r : CellReq B1 B2 cT,
      CellTables.budget r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + E) := fun cT => by
    obtain ⟨C0, hC0⟩ := hRK cT
    exact hE cT (RK cT) C0 hC0
  choose CellTables C6 hCellTables' using hk
  obtain ⟨CellsProc, eO, hO⟩ := hCellsProc
  exact ⟨fun cT => Dispatch.dispatchMachineFinal B1 B2 cT, CellTables, CellsProc, ⟨E, fun cT => ⟨C6 cT, hCellTables' cT⟩⟩, ⟨eO, hO⟩⟩

theorem counterInputsAll_of (hK5 : PolyTabReady) (hK6 : ∀ B1 B2, CellTablesUniform B1 B2)
    (hCellsProc : ∀ B1 B2, Cells.CellsUniform B1 B2) : CounterInputsAll := by
  intro s
  obtain ⟨a⟩ := s.williams
  obtain ⟨PolyTab, hord⟩ := hK5 a
  exact ⟨1, 1, le_rfl, le_rfl, counterInputs_of 1 1 PolyTab hord (hK6 1 1) (hCellsProc 1 1)⟩

end NearCubicGates.Close.CounterMachine.Supply
