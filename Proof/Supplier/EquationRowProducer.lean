import Proof.Supplier.EquationRowFramed
import Proof.Supplier.EquationRowBounds

/-! The composable ordinary row-to-matrix supplier with a uniform proved
budget and physical reset. No local execution record is an input premise. -/
namespace NearCubicWires.RepairOrdinary.EquationRowFramed
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def uniformBudget (r : EquationRow.Input) :=
  600000*(EquationRowRaw.mass r)^3+24*(EquationRowRaw.source r).length+7

theorem budget_bound (r : EquationRow.Input) : budget r ≤ uniformBudget r := by
  have h := EquationRowRaw.budget_polynomial r
  unfold budget uniformBudget
  omega

theorem producer_run (r : EquationRow.Input) : ∃ actual,
    run machine (uniformBudget r) (input r)=some actual ∧
    actual.final.tapes 128=physicalInput (EquationRow.request r) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ uniformBudget r := by
  obtain ⟨actual,ha,ht,hh,hs⟩ := framed_run r
  have hb := budget_bound r
  have hm := run_moreFuel machine (budget r) (uniformBudget r-budget r) _ actual ha
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨actual,hm,ht,hh,hs.trans hb⟩

noncomputable def program : Program where
  tapeCount := 130
  stateCount := _
  twoTapes := by decide
  machine := machine
  outputTape := 128
  outputFresh := by decide

theorem input_eq (r : EquationRow.Input) : program.inputTapes (EquationRowRaw.source r)=input r := by
  change (fun i : Fin 130 => if i.val=0 then frame (EquationRowRaw.source r) else [])=input r
  funext i
  fin_cases i <;> rfl

noncomputable def producer : RewoundWordFunction EquationRow.Input EquationRowRaw.source
    (fun r => physicalInput (EquationRow.request r)) uniformBudget where
  program := program
  realizes := by
    intro r
    obtain ⟨actual,ha,ht,_hh,_hs⟩ := producer_run r
    exact ⟨actual,by rw [input_eq]; exact ha,ht⟩
  headsReset := by
    intro r receipt hr
    rw [input_eq] at hr
    obtain ⟨actual,ha,_ht,hh,_hs⟩ := producer_run r
    have he : receipt=actual := Option.some.inj (hr.symm.trans ha)
    subst receipt
    exact hh

end NearCubicWires.RepairOrdinary.EquationRowFramed
