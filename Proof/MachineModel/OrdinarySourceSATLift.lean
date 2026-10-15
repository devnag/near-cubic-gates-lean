import Proof.MachineModel.OrdinarySourceSATLiftBound

/-! Closed cold sourceSAT-to-correctedSat oracle conversion. The runtime
budget is actual unary input data; its parsing, capacity production, source
head restoration, every corrected query and final framed output are paid. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def lifted (p : OrdinaryOracleProgram) : OrdinaryOracleProgram :=
  Full.program (clocked p)

theorem lifted_runs {p : OrdinaryOracleProgram} {input output : List Bool} {b : ℕ}
    (h : OrdinaryOracleRuns RecoveryOracle.sourceSAT p input output b) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (lifted p) (boundInput input b) output
      (1099511627776*(b+input.length+1)^3) := by
  obtain ⟨cost,n,source,hcost,hn,htrace,hhalt,houtput,hheads,_clock,_log,_query,hwidth⟩ := clocked_runs h
  let q := clocked p
  obtain ⟨data,hprepare,hcold⟩ := Full.cold_prepare q input b
  obtain ⟨heads',data',hsource,hready⟩ := Full.source_ready q input output b (cost+n+2)
    (Full.parsedHeads q input b) data hcold source htrace (by omega) hhalt hheads houtput
  obtain ⟨last,final,hlast,hfinish,hfinal,hout⟩ := Full.finish q output heads' data' hready
  obtain ⟨used,hused,whole⟩ := hprepare.trans hsource
  have hjoined := OrdinaryOracleCompose.trans whole hfinish
  refine ⟨used+last,final,?_,hjoined,hfinal,hout⟩
  have hcost' : 10*capacity b*(cost+n+2) ≤ 20*capacity b*(b+1) := by
    calc
      _ ≤ 10*capacity b*(2*b+2) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hlen : output.length ≤ b := by rw [frame_length] at hwidth; omega
  have hledger : used+last ≤ Full.ledger input b := by
    unfold Full.ledger
    omega
  exact hledger.trans (Full.ledger_bound input b)

end NearCubicWires.RepairSource.OrdinarySourceSATLift
