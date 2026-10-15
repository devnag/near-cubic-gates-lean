import Proof.Hierarchy.CompetitorWitnessCapBlock

/-! The total cap loop. Its time depends only on the real input length,
including when the supplied witness is arbitrarily longer than the cap. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop (w x pre wpre : List Bool) :
    ∃ t px pw,t≤3*x.length+2 ∧
      Timed machine t (cfg 0 (pre++frame x) (wpre++frame w) pre.length wpre.length)
        (cfg 33 (pre++frame x) (wpre++frame w) px pw [decide (16*w.length≤x.length)]) := by
  induction w generalizing x pre wpre with
  | nil =>
    refine ⟨1,pre.length,wpre.length,by omega,?_⟩
    simpa [frame] using Timed.single (by rfl) (accept_step (pre++frame x) wpre pre.length)
  | cons bit w ih =>
    have hfirst := Timed.single (by rfl)
      (witness_step (pre++frame x) wpre (bit::frame w) pre.length)
    by_cases hx : x.length<16
    · have hshort := short_block x pre (wpre++frame (bit::w)) 0 (wpre.length+1) (by omega)
      have h := hfirst.trans hshort
      refine ⟨1+(2*x.length+1),pre.length+2*x.length,wpre.length+1,by omega,?_⟩
      have hf : ¬16*(bit::w).length≤x.length := by simp only [List.length_cons]; omega
      simpa only [frame,hf,decide_false] using h
    · have htake : (x.take 16).length=16 := by simp [List.length_take]; omega
      have hfull := full_block (x.take 16) pre (x.drop 16) (wpre++frame (bit::w)) 0
        (wpre.length+1) (by decide) (by omega)
      rw [List.take_append_drop,htake] at hfull
      obtain ⟨t,px,pw,ht,hi⟩ := ih (x.drop 16) (pre++Streaming.marks (x.take 16)) (wpre++[true,bit])
      have hex : (pre++Streaming.marks (x.take 16))++frame (x.drop 16)=pre++frame x := by
        rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
      have hew : (wpre++[true,bit])++frame w=wpre++frame (bit::w) := by simp [frame,List.append_assoc]
      have hpl : (pre++Streaming.marks (x.take 16)).length=pre.length+32 := by
        simp only [List.length_append,Streaming.marks_length,htake]
      have hwpl : (wpre++[true,bit]).length=wpre.length+2 := by simp
      rw [hex,hew,hpl,hwpl] at hi
      have hc : (16*w.length≤(x.drop 16).length) ↔ 16*(bit::w).length≤x.length := by
        simp only [List.length_drop,List.length_cons]
        omega
      simp only [hc] at hi
      have h := (hfirst.trans hfull).trans hi
      refine ⟨(1+2*16)+t,px,pw,?_,?_⟩
      · simp only [List.length_drop] at ht
        omega
      · simpa only [frame] using h

theorem raw_run (x w : List Bool) :
    ∃ r,run machine (3*x.length+2) ![frame x,frame w,[]]=some r ∧
      r.final.tapes=![frame x,frame w,[decide (16*w.length≤x.length)]] ∧
      r.steps≤3*x.length+2 := by
  obtain ⟨t,px,pw,ht,h⟩ := loop w x [] []
  simp only [List.nil_append,List.length_nil] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  have he : cfg 0 (frame x) (frame w) 0 0=initialConfiguration machine ![frame x,frame w,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [he] at hr
  have hm := run_moreFuel machine t (3*x.length+2-t) _ r hr
  rw [Nat.add_sub_of_le ht] at hm
  exact ⟨r,hm,by rw [hf]; rfl,by omega⟩

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
