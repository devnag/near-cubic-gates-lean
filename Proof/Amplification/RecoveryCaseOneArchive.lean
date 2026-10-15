import Proof.Amplification.RecoveryCaseOnePayload

/-! Retain the original binary proof dimension before the canonical search.
The source and archived field both have paid zero-head endpoints. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneArchive
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Rewind.machine CompetitorFrameAppend.machine
def input (bits : List Bool) : Fin 4→List Bool := ![frame bits,[],[],[]]
def budget (bits : List Bool) := 8*bits.length+8

theorem archive_ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits) (input bits) out ∧
      out 0=frame bits ∧ out 1=frame bits := by
  obtain ⟨base,hbase,hfinal,hsteps⟩ := CompetitorFrameAppend.append_run bits [] []
  have hr : run CompetitorFrameAppend.machine (4*bits.length+3) ![frame bits,[],[]]=some base := by
    have hi : CompetitorFrameAppend.scan 0 (frame bits++[]) 0 []=
        initialConfiguration CompetitorFrameAppend.machine ![frame bits,[],[]] := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [CompetitorFrameAppend.scan,initialConfiguration]
    rw [hi] at hbase
    exact hbase
  obtain ⟨r,hrun,rt,rh,rs,_⟩ := Rewind.reset_run CompetitorFrameAppend.machine _ _ base hr
  have ht : 2*base.steps+2=budget bits := by rw [hsteps]; unfold budget; omega
  rw [ht] at hrun rs
  have hi : Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      ![frame bits,[],[]] (fun _=>[])=input bits := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,rh,rs.le⟩,?_,?_⟩
  · exact (rt 0).trans (by rw [hfinal]; exact List.append_nil _)
  · exact (rt 1).trans (by rw [hfinal]; rfl)

end NearCubicWires.RepairSource.RecoveryCaseOneArchive
