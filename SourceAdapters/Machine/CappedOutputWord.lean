import SourceAdapters.Machine.CappedOutputBlock
import Mathlib.Data.List.Induction

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: backward nested-frame printing for an arbitrary physical output word. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def pending (source marker : List Bool) (size mh : ℕ) (tail : List Bool) : Configuration 4 8 :=
  config (if size=0 then 4 else 0) source
    (List.replicate (4*size+2) false ++ tail) marker (size-1) (4*size+1) mh

theorem word_run (pref suffix tail marker : List Bool) (mh : ℕ) :
    ∃ r, runFrom machine (4*pref.length+2)
      (pending (pref++suffix) marker pref.length mh tail)=some r ∧
      r.final=config 7 (pref++suffix) ([true,true]++blocks pref++tail) marker 0 0 mh ∧
      r.steps=4*pref.length+2 := by
  induction pref using List.reverseRecOn generalizing suffix tail with
  | nil => simpa [pending, blocks] using header_run suffix tail marker mh
  | append_singleton pref b ih =>
    obtain ⟨r, hr, hf, hs⟩ := ih (b::suffix) (true::true::true::b::tail)
    have hsource : (pref++[b])++suffix=pref++b::suffix := by simp
    have hread : readTapeBit ((pref++[b])++suffix) pref.length=b := by
      rw [hsource]
      exact Streaming.read_append pref suffix b
    have hrest : runFrom machine (4*pref.length+2)
        (blockEnd ((pref++[b])++suffix) marker pref.length mh b tail)=some r := by
      simpa only [blockEnd, pending, hsource] using hr
    obtain ⟨result, hrun, hfinal, hsteps⟩ :=
      block_run ((pref++[b])++suffix) marker pref.length mh b tail hread _ r hrest
    refine ⟨result, ?_, ?_, ?_⟩
    · simpa [pending, blockStart, Nat.mul_add, Nat.add_assoc] using hrun
    · rw [hfinal, hf]
      simp [hsource, blocks, List.append_assoc]
    · rw [hsteps, hs]
      simp [Nat.mul_add]

end NearCubicGates.Adapters.Machine.Capped.OutputFrame
