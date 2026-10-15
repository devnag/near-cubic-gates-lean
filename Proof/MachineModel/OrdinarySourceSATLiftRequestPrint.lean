import Proof.MachineModel.OrdinarySourceSATLiftRequestScale

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestPrint
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (bits out : List Bool) (pos : ℕ) (hp : pos ≤ bits.length) :
    Configuration 1 (bits.length+1) :=
  ⟨⟨pos,by omega⟩,fun _ => out.length+pos,fun _ => out++bits.take pos⟩

theorem step (bits out : List Bool) (pos : ℕ) (hp : pos<bits.length) :
    LocalBitMultitape.step (HierarchyFixedWord.raw bits) (cfg bits out pos hp.le)=
      some (cfg bits out (pos+1) (by omega)) := by
  simp [LocalBitMultitape.step,HierarchyFixedWord.raw,cfg,hp]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i
    simp only [applyAction]
    have h := Streaming.write_append (out++bits.take pos) bits[pos]
    have hl : (out++bits.take pos).length=out.length+pos := by simp [Nat.min_eq_left hp.le]
    rw [hl] at h
    exact h.trans (by rw [List.append_assoc,List.take_append_getElem hp])

theorem tail (bits out : List Bool) (pos remaining : ℕ) (hp : pos+remaining=bits.length) :
    Timed (HierarchyFixedWord.raw bits) remaining (cfg bits out pos (by omega))
      (cfg bits out bits.length (by omega)) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos=bits.length := by omega
    subst pos
    exact Timed.refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [HierarchyFixedWord.raw,cfg]; omega) (step bits out pos (by omega))
      (ih (pos+1) (by omega))

theorem run (bits out : List Bool) : ∃ r,
    runFrom (HierarchyFixedWord.raw bits) bits.length
      ⟨(HierarchyFixedWord.raw bits).start,fun _ => out.length,fun _ => out⟩=some r ∧
      r.final.heads=(fun _ => (out++bits).length) ∧
      r.final.tapes=(fun _ => out++bits) ∧ r.steps=bits.length := by
  obtain ⟨r,hr,hf,hs⟩ := (tail bits out 0 bits.length (by omega)).run (by simp [HierarchyFixedWord.raw,cfg])
  refine ⟨r,?_,?_,?_,hs⟩
  · simpa [cfg,HierarchyFixedWord.raw] using hr
  · simp [hf,cfg]
  · simp [hf,cfg]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.RequestPrint
