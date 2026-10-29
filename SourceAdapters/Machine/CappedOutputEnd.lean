import SourceAdapters.Machine.CappedOutputSuffix

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: end-marker semantics for empty and nonempty physical output words. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

def ready (source marker : List Bool) (cap : ℕ) : Configuration 5 20 :=
  config 19 source (List.replicate (4*source.length+2) false ++ [true,false,false])
    marker cap (source.length-1) (4*source.length+1) (source.length-1) (source.length-1)

theorem end_marker (source marker : List Bool) (hm : OutputTracking.Marked source marker)
    (hn : 0 < source.length) : readTapeBit marker (source.length-1)=true := by
  obtain ⟨hl,he | ⟨pre,he⟩⟩ := hm
  · subst marker; simp at hl; omega
  · have hp : pre.length=source.length-1 := by rw [he] at hl; simp at hl; omega
    rw [he,←hp]
    exact Streaming.read_append pre [] true

theorem end_run (source marker : List Bool) (cap : ℕ) (hm : OutputTracking.Marked source marker) :
    ∃ fuel, fuel ≤ 10 ∧ ∃ r,
      runFrom machine fuel (walk 6 source marker cap (source.length-1))=some r ∧
      r.final=ready source marker cap ∧ r.steps=fuel := by
  by_cases hn : source.length=0
  · have hs : source=[] := by simpa using hn
    have hm0 : marker=[] := by simpa using (hm.1.trans hn)
    subst source; subst marker
    obtain ⟨r,hr,hf,hsteps⟩ := suffix_run [] [] cap 0 0 0
    have h6 := step_known 6 14 [] [] [] cap 0 2 0 0
      .stay .stay .stay .stay none (by rfl)
    simp only [written,HeadMove.apply] at h6
    have e6 := runFrom_step machine _ _ r (by rfl) h6 hr
    refine ⟨6,by omega,_,e6,?_,?_⟩
    · exact hf
    · change r.steps+1=6
      omega
  · let k := source.length-1
    have hk : k+1=source.length := by dsimp [k]; omega
    have hmarker : readTapeBit marker k=true := end_marker source marker hm (by omega)
    obtain ⟨r,hr,hf,hsteps⟩ := suffix_run source marker cap (k+1) k k
    obtain ⟨r1,hr1,hf1,hs1⟩ := advance_run source marker cap k k k 5 r hr
    have h6 := step_known 6 10 source [] marker cap k (4*k+2) k k
      .stay .stay .stay .stay none (by simp [machine,config,Configuration.scanned,hmarker])
    simp only [written,HeadMove.apply] at h6
    have e6 := runFrom_step machine _ _ r1 (by rfl) h6 hr1
    refine ⟨10,by omega,_,e6,?_,?_⟩
    · change r1.final=ready source marker cap
      rw [hf1,hf]
      simp only [ready,hk]
      rfl
    · change r1.steps+1=10
      omega

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
