import SourceAdapters.Machine.CappedOutputSeek

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: paid forward and backward sweeps of the output cap. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

theorem forward_step (source marker : List Bool) (cap pos : ℕ) (hp : pos<cap)
    (fuel : ℕ) (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (walk 2 source marker cap (pos+1))=some r) :
    ∃ result, runFrom machine (fuel+4) (walk 2 source marker cap pos)=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4 := by
  have hclock : readTapeBit (List.replicate cap true) pos=true := by
    simpa only [readTapeBit] using (List.getD_replicate (x:=true) (y:=false) hp)
  have h0 := step_known 2 3 source [] marker cap pos (4*pos+2) pos pos
    .right .right .right .right none (by simp [machine, config, Configuration.scanned, hclock])
  have h1 := step_known 3 4 source [] marker cap (pos+1) (4*pos+3) (pos+1) (pos+1)
    .stay .right .stay .stay none (by rfl)
  have h2 := step_known 4 5 source [] marker cap (pos+1) (4*pos+4) (pos+1) (pos+1)
    .stay .right .stay .stay none (by rfl)
  have h3 := step_known 5 2 source [] marker cap (pos+1) (4*pos+5) (pos+1) (pos+1)
    .stay .right .stay .stay none (by rfl)
  simp only [written, HeadMove.apply] at h0 h1 h2 h3
  have hend : 4*pos+5+1=4*(pos+1)+2 := by omega
  rw [hend] at h3
  have e3 := runFrom_step machine _ _ r (by rfl) h3 hr
  have e2 := runFrom_step machine _ _ _ (by rfl) h2 e3
  have e1 := runFrom_step machine _ _ _ (by rfl) h1 e2
  have e0 := runFrom_step machine _ _ _ (by rfl) h0 e1
  exact ⟨_,e0,rfl,by simp only⟩

theorem backward_step (source marker : List Bool) (cap pos : ℕ)
    (hm : readTapeBit marker (pos+1)=false) (fuel : ℕ) (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (walk 6 source marker cap pos)=some r) :
    ∃ result, runFrom machine (fuel+4) (walk 6 source marker cap (pos+1))=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4 := by
  have ho : readTapeBit [true] (pos+1)=false := by simp [readTapeBit, List.getD]
  have h0 := step_known 6 7 source [] marker cap (pos+1) (4*pos+6) (pos+1) (pos+1)
    .left .left .left .left none (by simp [machine, config, Configuration.scanned, hm, ho])
  have h1 := step_known 7 8 source [] marker cap pos (4*pos+5) pos pos
    .stay .left .stay .stay none (by rfl)
  have h2 := step_known 8 9 source [] marker cap pos (4*pos+4) pos pos
    .stay .left .stay .stay none (by rfl)
  have h3 := step_known 9 6 source [] marker cap pos (4*pos+3) pos pos
    .stay .left .stay .stay none (by rfl)
  simp only [written, HeadMove.apply, Nat.add_sub_cancel] at h0 h1 h2 h3
  have ha6 : 4*pos+6-1=4*pos+5 := by omega
  have ha5 : 4*pos+5-1=4*pos+4 := by omega
  have ha4 : 4*pos+4-1=4*pos+3 := by omega
  have ha3 : 4*pos+3-1=4*pos+2 := by omega
  rw [ha6] at h0
  rw [ha5] at h1
  rw [ha4] at h2
  rw [ha3] at h3
  have e3 := runFrom_step machine _ _ r (by rfl) h3 hr
  have e2 := runFrom_step machine _ _ _ (by rfl) h2 e3
  have e1 := runFrom_step machine _ _ _ (by rfl) h1 e2
  have e0 := runFrom_step machine _ _ _ (by rfl) h0 e1
  have hwalk : config 6 source [] marker cap (pos+1) (4*pos+6) (pos+1) (pos+1) =
      walk 6 source marker cap (pos+1) := by simp [walk, Nat.mul_add, Nat.add_assoc]
  rw [hwalk] at e0
  exact ⟨_,e0,rfl,by simp only⟩

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
