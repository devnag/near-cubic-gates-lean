import SourceAdapters.Machine.CappedOutputSeekRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: actual complete nested-frame writer after end location. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def entry (source marker : List Bool) (mh : ℕ) : Configuration 4 8 :=
  config 6 source (List.replicate (4*source.length+2) false ++ [true,false,false])
    marker (source.length-1) (4*source.length+1) mh

theorem writer_run (source marker : List Bool) (mh : ℕ)
    (hmark : readTapeBit marker mh=decide (0 < source.length)) :
    ∃ result, runFrom machine (4*source.length+3) (entry source marker mh)=some result ∧
      result.final=config 7 source (frame (true::frame source)) marker 0 0 mh := by
  obtain ⟨r,hr,hf,_⟩ := word_run source [] [true,false,false] marker mh
  simp only [List.append_nil] at hr hf
  have hstep := step_known 6 (if source.length=0 then 4 else 0) source
    (List.replicate (4*source.length+2) false ++ [true,false,false]) marker
    (source.length-1) (4*source.length+1) mh .stay .stay none (by
      by_cases h : source.length=0
      · simp [machine,config,Configuration.scanned,hmark,h]
      · have hp : 0 < source.length := Nat.pos_of_ne_zero h
        simp [machine,config,Configuration.scanned,hmark,h,hp])
  simp only [written,HeadMove.apply] at hstep
  have e := runFrom_step machine _ _ r (by rfl) hstep hr
  refine ⟨_,e,?_⟩
  change r.final=config 7 source (frame (true::frame source)) marker 0 0 mh
  rw [hf,result_frame]

theorem marked_writer_run (source marker : List Bool) (hm : OutputTracking.Marked source marker) :
    ∃ result, runFrom machine (4*source.length+3) (entry source marker (source.length-1))=some result ∧
      result.final=config 7 source (frame (true::frame source)) marker 0 0 (source.length-1) := by
  apply writer_run
  by_cases hn : source.length=0
  · have he : marker=[] := by simpa [hn] using hm.1
    simp [he,hn,readTapeBit,List.getD]
  · have hp : 0 < source.length := Nat.pos_of_ne_zero hn
    simpa [hp] using OutputSeek.end_marker source marker hm hp

end NearCubicGates.Adapters.Machine.Capped.OutputFrame
