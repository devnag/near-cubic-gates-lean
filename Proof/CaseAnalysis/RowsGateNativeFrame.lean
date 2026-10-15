import Proof.CaseAnalysis.RowsGateNativeRun

/-! Frame the actual append cursor and retain the support verdict, with
the existing measured-length wrapper and its complete execution budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
open LocalBitMultitape RepairRepresentation CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def framedMachine (compressed : Bool) := AppendOutputFrame.machine (machine compressed) 23
def framedInput (fields : List (Bool×List Bool)) (membership source : List Bool) (n : ℕ) :=
  AppendOutputFrame.input (input fields membership source n)
def framedBudget (compressed : Bool) (fields : List (Bool×List Bool))
    (membership source : List Bool) (n w : ℕ) :=
  2*budget compressed fields membership n w+4*(word compressed fields membership source n).length+7

theorem framed_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership source : List Bool) (n w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ out,
    ClockJoin.ReadyRun (framedMachine compressed) (framedBudget compressed fields membership source n w)
      (framedInput fields membership source n) out ∧
      out 40=frame (word compressed fields membership source n) ∧
      out 25=[validity fields membership true fields.length] := by
  obtain ⟨base,hbase,bs,bt,bh,bflag⟩ := native_run compressed fields membership source n w hw
  obtain ⟨r,hr,rt,rh,ro,rs⟩ := PCPPNativeFrame.frame_run (machine compressed) 23 (output_forward compressed)
    _ _ base hbase _ bt bh
  have htime : 2*base.steps+4*(word compressed fields membership source n).length+7 ≤
      framedBudget compressed fields membership source n w := by unfold framedBudget;omega
  have more := run_moreFuel (framedMachine compressed) _
    (framedBudget compressed fields membership source n w-
      (2*base.steps+4*(word compressed fields membership source n).length+7))
    (framedInput fields membership source n) r hr
  rw [Nat.add_sub_of_le htime] at more
  exact ⟨r.final.tapes,⟨r,more,rfl,rh,rs.trans htime⟩,rt,(ro 25).trans bflag⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
