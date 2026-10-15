import Proof.Gates.Interfaces.CounterFormats
import Proof.Gates.Closure.Obligations
import Proof.Gates.Counter.OutOK

set_option autoImplicit false

namespace NearCubicGates.Close.CounterAsm

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- One class exponent for every `c_T`: `budget ≤ C_{c_T}·2^{n−k}·(n+1)^{2 J_max + e}` (prop:time 1820–1839). -/
def CellCls {B1 B2 : ℕ} (bud : ∀ cT : ℕ, CellReq B1 B2 cT → ℕ) : Prop :=
  ∃ e : ℕ, ∀ cT : ℕ, ∃ C : ℕ, ∀ r : CellReq B1 B2 cT,
    bud cT r ≤ C * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + e)

/-- The producers of the counter program at exponents `B₁, B₂`. -/
def CounterInputs (B1 B2 : ℕ) : Prop :=
  ∃ (_D : ∀ cT : ℕ, DispatchMachine B1 B2 cT) (CellTables : ∀ cT : ℕ, TablesMachine B1 B2 cT)
    (CellsProc : ∀ cT : ℕ, CellsMachine B1 B2 cT),
    CellCls (fun cT => (CellTables cT).budget) ∧ CellCls (fun cT => (CellsProc cT).budget)

/-- The hypothesis of `counterSupply_of`. -/
def CounterInputsAll : Prop :=
  ∀ _s : GateSources, ∃ B1 B2 : ℕ, 1 ≤ B1 ∧ 1 ≤ B2 ∧ CounterInputs B1 B2

/-- The type of `O1asm_of` (proved in `CounterAsm.Main`). -/
def CounterOfProducersStatement : Prop :=
  ∀ (_s : GateSources) (B1 B2 : ℕ), 1 ≤ B1 → 1 ≤ B2 → ∀ (_D : ∀ cT : ℕ, DispatchMachine B1 B2 cT)
    (CellTables : ∀ cT : ℕ, TablesMachine B1 B2 cT) (CellsProc : ∀ cT : ℕ, CellsMachine B1 B2 cT),
    CellCls (fun cT => (CellTables cT).budget) → CellCls (fun cT => (CellsProc cT).budget) →
    ∃ ctr : Counter B1 B2, Counter.DenOK ctr ∧ Counter.OutOK ctr

/-- `CounterOfProducersStatement` gives `Closure.CounterSupply` from `CounterInputsAll`. -/
theorem counterSupply_of_statement (H : CounterOfProducersStatement) (h : CounterInputsAll) : Closure.CounterSupply := by
  intro s
  obtain ⟨B1, B2, hB1, hB2, D, CellTables, CellsProc, hK6, hCellsProc⟩ := h s
  exact ⟨B1, B2, hB1, hB2, H s B1 B2 hB1 hB2 D CellTables CellsProc hK6 hCellsProc⟩

end NearCubicGates.Close.CounterAsm
