import SourceAdapters.Machine.CappedOutputSweep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: exact linear costs for complete output-end sweeps. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

theorem forward_run (source marker : List Bool) (cap pos count : ℕ)
    (hend : pos+count=cap) (fuel : ℕ) (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (walk 6 source marker cap cap)=some r) :
    ∃ result, runFrom machine (fuel+4*count+1) (walk 2 source marker cap pos)=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4*count+1 := by
  induction count generalizing pos with
  | zero =>
    have hp : pos=cap := by omega
    subst pos
    have hclock : readTapeBit (List.replicate cap true) cap=false := by simp [readTapeBit, List.getD]
    have h := step_known 2 6 source [] marker cap cap (4*cap+2) cap cap
      .stay .stay .stay .stay none (by simp [machine, config, Configuration.scanned, hclock])
    simp only [written, HeadMove.apply] at h
    have e := runFrom_step machine _ _ r (by rfl) h hr
    exact ⟨_,e,rfl,by simp only [Nat.mul_zero, Nat.add_zero]⟩
  | succ count ih =>
    obtain ⟨middle, hm, hf, hs⟩ := ih (pos+1) (by omega)
    obtain ⟨result, he, hfe, hse⟩ := forward_step source marker cap pos (by omega) _ middle hm
    refine ⟨result, ?_, hfe.trans hf, ?_⟩
    · simpa [Nat.mul_add, Nat.add_assoc] using he
    · rw [hse,hs]
      omega

theorem backward_run (source marker : List Bool) (cap stop count : ℕ)
    (hz : ∀ p, stop < p → p ≤ stop+count → readTapeBit marker p=false)
    (fuel : ℕ) (r : ExecutionReceipt 5 20)
    (hr : runFrom machine fuel (walk 6 source marker cap stop)=some r) :
    ∃ result, runFrom machine (fuel+4*count) (walk 6 source marker cap (stop+count))=some result ∧
      result.final=r.final ∧ result.steps=r.steps+4*count := by
  induction count with
  | zero => exact ⟨r,by simpa using hr,rfl,by simp⟩
  | succ count ih =>
    obtain ⟨middle, hm, hf, hs⟩ := ih (fun p hp hle => hz p hp (by omega))
    obtain ⟨result, he, hfe, hse⟩ := backward_step source marker cap (stop+count)
      (hz _ (by omega) (by omega)) _ middle hm
    refine ⟨result, ?_, hfe.trans hf, ?_⟩
    · simpa [Nat.mul_add, Nat.add_assoc] using he
    · rw [hse,hs]
      omega

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
