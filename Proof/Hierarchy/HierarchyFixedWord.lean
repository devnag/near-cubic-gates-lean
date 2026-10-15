import Proof.Hierarchy.HierarchyBinaryKernel

/-! A fixed hierarchy's finite program prints its literal binary coefficient
or code word. Only the already fixed word indexes this finite rule table. -/
namespace NearCubicWires.RepairOrdinary.HierarchyFixedWord
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (bits : List Bool) : Machine 1 (bits.length+1) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==bits.length
  rule := fun q _ => if h : q.val<bits.length then
    some ⟨⟨q.val+1,by omega⟩,fun _ => some bits[q.val],fun _ => .right⟩ else none
def cfg (bits : List Bool) (pos : ℕ) (hp : pos≤bits.length) : Configuration 1 (bits.length+1) :=
  ⟨⟨pos,by omega⟩,fun _ => pos,fun _ => bits.take pos⟩

theorem write_step (bits : List Bool) (pos : ℕ) (hp : pos<bits.length) :
    step (raw bits) (cfg bits pos hp.le)=some (cfg bits (pos+1) (by omega)) := by
  simp [step,raw,cfg,hp]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    simp only [applyAction]
    have h := Streaming.write_append (bits.take pos) bits[pos]
    have hl : (bits.take pos).length=pos := by simp [Nat.min_eq_left hp.le]
    rw [hl] at h
    exact h.trans (List.take_append_getElem hp)

theorem write_prefix (bits : List Bool) (pos remaining : ℕ) (hp : pos+remaining=bits.length) :
    Timed (raw bits) remaining (cfg bits pos (by omega)) (cfg bits bits.length (by omega)) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos=bits.length := by omega
    subst pos
    exact Timed.refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [raw,cfg]; omega) (write_step bits pos (by omega))
      (ih (pos+1) (by omega))

def machine (bits : List Bool) : Machine 2 (bits.length+1+2) := Rewind.machine (raw bits)

theorem word_ready (bits : List Bool) :
    ReadyRun (machine bits) (2*bits.length+2) (fun _ => [])
      ![bits,List.replicate bits.length false] := by
  obtain ⟨base,hb,hf,hs⟩ := (write_prefix bits 0 bits.length (by omega)).run (by simp [raw,cfg])
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (raw bits) _ _ base hb 0
  have he : 2*base.steps+2=2*bits.length+2 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.HierarchyFixedWord
