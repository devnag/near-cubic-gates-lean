import Proof.MachineModel.OrdinaryMatrixCoordinateFinish

/-! One paid aggregate rewind after coordinate transposition and stream
closure. The global source cursor is retained; only the sort input resets. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def resetMachine : Machine 13 40 := SelectiveReset.machine closedMachine 10
noncomputable def resetInput (w cap : ℕ) (rs : List Record) (pre record clone rank : List Bool) :=
  Rewind.recording (cfg closedMachine.start w cap (pre++stream w rs) pre.length record clone rank []) 0
def resetOutput (w cap count : ℕ) (rs : List Record) (pre record clone rank : List Bool) :=
  let final := cfg (37 : Fin 38) w cap (pre++stream w rs) (pre.length+(stream w rs).length)
    record clone rank (output w rs++[false])
  SelectiveReset.finished (s := 38) (fun i => if i=10 then 0 else final.heads i) final.tapes count

theorem reset_run (w cap : ℕ) (rs : List Record) (pre record clone rank : List Bool)
    (hcap : 2*w ≤ cap) (hr : record.length ≤ 4*w+1)
    (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ fr fc fk count,fr.length ≤ 4*w+1 ∧ fc.length ≤ 4*w+1 ∧ fk.length ≤ 2*w+1 ∧
      count ≤ rs.length*(64*w+47)+3 ∧
      ∃ actual : ExecutionReceipt 13 40,
        runFrom resetMachine (2*(rs.length*(64*w+47)+3)+2) (resetInput w cap rs pre record clone rank)=some actual ∧
        actual.final=resetOutput w cap count rs pre fr fc fk ∧
        actual.steps ≤ 2*(rs.length*(64*w+47)+3)+2 := by
  obtain ⟨fr,fc,fk,hfr,hfc,hfk,base,hbase,hf,hs⟩ := closed_run w cap rs pre record clone rank hcap hr hc hk
  have hh := SelectiveReset.prefix_head (prefix_of_run closedMachine _ _ base hbase).1 (10 : Fin 12)
  have hz : (cfg closedMachine.start w cap (pre++stream w rs) pre.length record clone rank []).heads 10=0 := rfl
  rw [hz,Nat.zero_add] at hh
  obtain ⟨actual,ha,haf,has,_⟩ := SelectiveReset.reset_run closedMachine 10 _ _ base hbase hh
  have hb : 2*base.steps+2 ≤ 2*(rs.length*(64*w+47)+3)+2 := by omega
  have hm := runFrom_moreFuel resetMachine (2*base.steps+2)
    (2*(rs.length*(64*w+47)+3)+2-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨fr,fc,fk,base.steps,hfr,hfc,hfk,hs,actual,hm,?_,by omega⟩
  rw [haf,hf]
  rfl

theorem reset_output_tape (w cap count : ℕ) (rs : List Record) (pre record clone rank : List Bool) :
    (resetOutput w cap count rs pre record clone rank).tapes 10=output w rs++[false] := by
  simp [resetOutput,SelectiveReset.finished,Rewind.config,cfg,Fin.addCases]

theorem reset_output_head (w cap count : ℕ) (rs : List Record) (pre record clone rank : List Bool) :
    (resetOutput w cap count rs pre record clone rank).heads 10=0 := by
  simp [resetOutput,SelectiveReset.finished,Rewind.config,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
