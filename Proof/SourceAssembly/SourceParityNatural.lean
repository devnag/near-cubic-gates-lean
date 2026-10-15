import Proof.SourceAssembly.SourcePairSupport
import Proof.CaseAnalysis.RowsEstimatorParityNatural

/- Exact cold natural producer: its only nonblank input is the paid raw count.
The output retains the logical field boundary; no initial padded bank is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyParityNatural
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound
noncomputable section

theorem cold_run (n : Nat) : ∃ A,
    ClockJoin.ReadyRun Natural.machine (Natural.budget n) (Natural.source n) A ∧
    A 20=frame (natWord n) ∧ A 17=natWord n := by
  obtain ⟨base,hb,bword,bhead,_b1,_bh1,_bs⟩:=EquationHeaderAppend.append_run n []
  have he : EquationHeaderAppend.entry n []=
      initialConfiguration EquationHeaderAppend.machine (EquationHeaderAppend.tapes n []) := by
    apply configuration_ext
    · rfl
    · funext i;simp [EquationHeaderAppend.entry,EquationHeaderAppend.heads,initialConfiguration]
    · rfl
  rw [he] at hb
  obtain ⟨framed,hf,word,heads,old,steps⟩:=PCPPNativeFrame.frame_run EquationHeaderAppend.machine 17
    EquationRowRaw.header_append_forward _ (EquationHeaderAppend.tapes n []) base hb (natWord n)
    (by simpa only [List.nil_append] using bword) (by simpa only [List.nil_append] using bhead)
  have ht : 2*base.steps+4*(natWord n).length+7≤Natural.budget n := by
    have hbase:=runFrom_steps_le _ _ _ base hb
    unfold Natural.budget
    omega
  have more:=run_moreFuel Natural.machine _ (Natural.budget n-(2*base.steps+4*(natWord n).length+7)) _ framed hf
  rw [Nat.add_sub_of_le ht,Natural.input_eq] at more
  refine ⟨framed.final.tapes,⟨framed,more,rfl,heads,?_⟩,word,?_⟩
  · exact runFrom_steps_le _ _ _ framed more
  · exact (old 17).trans (by simpa only [List.nil_append] using bword)

end
end SourceAssemblyParityNatural
