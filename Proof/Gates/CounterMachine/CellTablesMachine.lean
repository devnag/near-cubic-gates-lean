import Proof.Gates.CounterMachine.CellTablesCls14
import Proof.Gates.CounterMachine.CellTablesUniform
import Proof.Gates.CounterMachine.CellTablesPack6

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine.CellTablesProg

noncomputable def tablesMachineOfK {B1 B2 cT : ℕ} (PolyTab : TabMachine) (RK : TabCallMachine B1 B2 cT PolyTab)
    (C0 e0 : ℕ)
    (hRK : ∀ x : TabCallReq B1 B2 cT, RK.budget x ≤ C0 * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e0) :
    TablesMachine B1 B2 cT :=
  let z := zOf B1 B2 C0 e0
  let N : CellReq B1 B2 cT → ℕ := fun r =>
    mainCost ((zOf B1 B2 C0 e0).Lk (leadOnes (cellInput r)))
      ((zK z cT r.c.n (leadOnes (cellInput r))).Bk (leadOnes (cellInput r))) (C0 * (r.c.n + 1) ^ e0) r
  have hrun : ∀ r : CellReq B1 B2 cT, ∃ b n, Ex (ctxOf (tabCallCallee RK) (zK z cT r.c.n (leadOnes (cellInput r)))
      (cellInput r)) mainK a0 b n ∧ b.out = cellWord r.c r.p r.wt ∧ n ≤ N r := fun r =>
    main_run RK r _ _ _ _ (fit_of RK C0 e0 hRK r).1 (fit_of RK C0 e0 hRK r).2
  have hW1 : ∀ r : CellReq B1 B2 cT, 1 ≤ z.W (leadOnes (cellInput r)) := fun r =>
    Nat.mul_le_mul (Nat.one_le_two_pow) (by show 1 ≤ C0 + 100 * zeta ^ 2 + 16; omega)
  have hW2 : ∀ r : CellReq B1 B2 cT, 2 ^ (leadOnes (cellInput r) + 2) ≤ z.W (leadOnes (cellInput r)) := fun r => by
    show 2 ^ (leadOnes (cellInput r) + 2) ≤ 2 ^ ((e0 + 2 * b0Of B1 B2) * leadOnes (cellInput r)) *
      (C0 + 100 * zeta ^ 2 + 16)
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_left _ (by unfold b0Of; omega))) (by norm_num)
  have wf := (packK_of (V := VV) (M := MM) (by decide) cellInput (fun r => cellWord r.c r.p r.wt) (tabCallCallee RK) z cT
    (fun r => r.c.n) mainK N cellInput_natWord hrun hW1 hW2).some
  ⟨_, wf, ⟨Kf B1 B2 C0 e0 cT RK.wf.program.tapeCount, dE B1 B2 e0, fun r => budget_le RK r C0 e0⟩⟩

theorem cellTablesUniform : ∀ B1 B2 : ℕ, CellTablesUniform B1 B2 := by
  intro B1 B2 PolyTab e0
  refine ⟨dE B1 B2 e0, fun cT RK C0 hRK => ⟨tablesMachineOfK PolyTab RK C0 e0 hRK,
    Kf B1 B2 C0 e0 cT RK.wf.program.tapeCount, fun r => budget_le RK r C0 e0⟩⟩

/-- **STATEMENT CellTables** (`CellTablesTarget`). -/
noncomputable def tablesMachineOf (B1 B2 cT : ℕ) (PolyTab : TabMachine) : CellTablesTarget B1 B2 cT PolyTab :=
  fun RK => tablesMachineOfK PolyTab RK (Classical.choose RK.cls) (Classical.choose (Classical.choose_spec RK.cls))
    (Classical.choose_spec (Classical.choose_spec RK.cls))

end NearCubicGates.Close.CounterMachine
