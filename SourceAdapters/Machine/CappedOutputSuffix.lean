import SourceAdapters.Machine.CappedOutputLoops

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: materialize the precise final output extent and its framing suffix. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

theorem suffix_run (source marker : List Bool) (cap len mh ch : ℕ) :
    ∃ r, runFrom machine 5 (config 14 source [] marker cap len (4*len+2) mh ch)=some r ∧
      r.final=config 19 source (List.replicate (4*len+2) false ++ [true,false,false])
        marker cap (len-1) (4*len+1) mh ch ∧ r.steps=5 := by
  let pref := List.replicate (4*len+2) false
  have h14 := step_known 14 15 source [] marker cap len (4*len+2) mh ch
    .stay .right .stay .stay (some true) (by rfl)
  have h15 := step_known 15 16 source (pref++[true]) marker cap len (4*len+3) mh ch
    .stay .right .stay .stay (some false) (by rfl)
  have h16 := step_known 16 17 source (pref++[true,false]) marker cap len (4*len+4) mh ch
    .stay .left .stay .stay (some false) (by rfl)
  have h17 := step_known 17 18 source (pref++[true,false,false]) marker cap len (4*len+3) mh ch
    .stay .left .stay .stay none (by rfl)
  have h18 := step_known 18 19 source (pref++[true,false,false]) marker cap len (4*len+2) mh ch
    .left .left .stay .stay none (by rfl)
  have hw1 : writeTapeBit (pref++[true]) (4*len+3) false=pref++[true,false] := by
    simpa [pref,List.append_assoc] using Streaming.write_append (pref++[true]) false
  have hw2 : writeTapeBit (pref++[true,false]) (4*len+4) false=pref++[true,false,false] := by
    simpa [pref,List.append_assoc] using Streaming.write_append (pref++[true,false]) false
  simp only [written,OutputFrame.write_blank,HeadMove.apply] at h14
  simp only [written,hw1,HeadMove.apply] at h15
  simp only [written,hw2,HeadMove.apply] at h16
  simp only [written,HeadMove.apply] at h17 h18
  have ha4 : 4*len+4-1=4*len+3 := by omega
  have ha3 : 4*len+3-1=4*len+2 := by omega
  have ha2 : 4*len+2-1=4*len+1 := by omega
  rw [ha4] at h16
  rw [ha3] at h17
  rw [ha2] at h18
  let final := config 19 source (pref++[true,false,false]) marker cap (len-1) (4*len+1) mh ch
  let r : ExecutionReceipt 5 20 := ⟨final,0,final.tapeCells⟩
  have h0 : runFrom machine 0 final=some r := by rfl
  have e18 := runFrom_step machine _ _ r (by rfl) h18 h0
  have e17 := runFrom_step machine _ _ _ (by rfl) h17 e18
  have e16 := runFrom_step machine _ _ _ (by rfl) h16 e17
  have e15 := runFrom_step machine _ _ _ (by rfl) h15 e16
  have e14 := runFrom_step machine _ _ _ (by rfl) h14 e15
  exact ⟨_,e14,rfl,rfl⟩

theorem advance_run (source marker : List Bool) (cap pos mh ch fuel : ℕ)
    (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (config 14 source [] marker cap (pos+1) (4*(pos+1)+2) mh ch)=some r) :
    ∃ result, runFrom machine (fuel+4) (config 10 source [] marker cap pos (4*pos+2) mh ch)=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4 := by
  have h10 := step_known 10 11 source [] marker cap pos (4*pos+2) mh ch
    .right .right .stay .stay none (by rfl)
  have h11 := step_known 11 12 source [] marker cap (pos+1) (4*pos+3) mh ch
    .stay .right .stay .stay none (by rfl)
  have h12 := step_known 12 13 source [] marker cap (pos+1) (4*pos+4) mh ch
    .stay .right .stay .stay none (by rfl)
  have h13 := step_known 13 14 source [] marker cap (pos+1) (4*pos+5) mh ch
    .stay .right .stay .stay none (by rfl)
  simp only [written,HeadMove.apply] at h10 h11 h12 h13
  have he : 4*pos+5+1=4*(pos+1)+2 := by omega
  rw [he] at h13
  have e13 := runFrom_step machine _ _ r (by rfl) h13 hr
  have e12 := runFrom_step machine _ _ _ (by rfl) h12 e13
  have e11 := runFrom_step machine _ _ _ (by rfl) h11 e12
  have e10 := runFrom_step machine _ _ _ (by rfl) h10 e11
  exact ⟨_,e10,rfl,by simp only⟩

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
