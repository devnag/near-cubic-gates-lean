import Proof.Supplier.EquationRowForward
import Proof.Assembly.AppendOutputFrame

/-! A complete fixed ordinary machine reads the original equation row and
emits the exact externally framed matrix request, with every head reset. -/
namespace NearCubicWires.RepairOrdinary.EquationRowFramed
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := AppendOutputFrame.machine EquationRowRaw.machine 110
def input (r : EquationRow.Input) : Fin 130 → List Bool :=
  fun i => if i=0 then frame (EquationRowRaw.source r) else []
def budget (r : EquationRow.Input) := 6*EquationRowRaw.budget r+7

theorem framed_run (r : EquationRow.Input) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 128=MatrixScoreBatch.physicalInput (EquationRow.request r) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ budget r := by
  obtain ⟨base,hb,_bt0,_bh0,bt,bh,bs⟩ := EquationRowRaw.raw_run r
  have hlen : (MatrixScoreBatch.word (EquationRow.request r)).length ≤ base.steps := by
    obtain ⟨hp,_hh⟩ := prefix_of_run EquationRowRaw.machine (EquationRowRaw.budget r)
      (initialConfiguration EquationRowRaw.machine (EquationRowRaw.input r)) base hb
    have h := SelectiveReset.prefix_head hp 110
    rw [bh] at h
    simpa only [initialConfiguration,Nat.zero_add] using h
  obtain ⟨actual,ha,actualT,ah,ast⟩ := AppendOutputFrame.frame_run EquationRowRaw.machine 110
    EquationRowRaw.output_forward (EquationRowRaw.budget r) (EquationRowRaw.input r)
    base hb (MatrixScoreBatch.word (EquationRow.request r)) bt bh
  have hin : AppendOutputFrame.input (EquationRowRaw.input r)=input r := by
    funext i; fin_cases i <;> rfl
  rw [hin] at ha
  have htime : 2*base.steps+4*(MatrixScoreBatch.word (EquationRow.request r)).length+7 ≤ budget r := by
    unfold budget
    omega
  have hm := run_moreFuel machine _
    (budget r-(2*base.steps+4*(MatrixScoreBatch.word (EquationRow.request r)).length+7)) _ actual ha
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨actual,hm,actualT,ah,ast.trans htime⟩

end NearCubicWires.RepairOrdinary.EquationRowFramed
