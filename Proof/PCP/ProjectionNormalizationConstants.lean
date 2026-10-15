import Proof.PCP.ProjectionNormalizationFieldList
import Proof.Hierarchy.HierarchyFixedWord

/-! The padding producer uses the existing finite literal-word printer at
a retained output cursor. The printed word is fixed zero-projection code;
runtime dimensions are supplied only by physical repetition drivers. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Constants
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (bits pre : List Bool) (pos : ℕ) (hp : pos≤bits.length) :
    Configuration 1 (bits.length+1) :=
  ⟨⟨pos,by omega⟩,fun _ => pre.length+pos,fun _ => pre++bits.take pos⟩

theorem write_step (bits pre : List Bool) (pos : ℕ) (hp : pos<bits.length) :
    step (HierarchyFixedWord.raw bits) (cfg bits pre pos hp.le)=
      some (cfg bits pre (pos+1) (by omega)) := by
  simp [step,HierarchyFixedWord.raw,cfg,hp]
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i
    simp only [applyAction]
    have h := Streaming.write_append (pre++bits.take pos) bits[pos]
    have hl : (pre++bits.take pos).length=pre.length+pos := by simp [Nat.min_eq_left hp.le]
    rw [hl] at h
    rw [h,List.append_assoc,List.take_append_getElem hp]

theorem write_prefix (bits pre : List Bool) (pos remaining : ℕ)
    (hp : pos+remaining=bits.length) :
    Timed (HierarchyFixedWord.raw bits) remaining
      (cfg bits pre pos (by omega)) (cfg bits pre bits.length (by omega)) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos=bits.length := by omega
    subst pos
    exact Timed.refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [HierarchyFixedWord.raw,cfg]; omega)
      (write_step bits pre pos (by omega)) (ih (pos+1) (by omega))

theorem write_run (bits pre : List Bool) :
    ∃ r,runFrom (HierarchyFixedWord.raw bits) bits.length (cfg bits pre 0 (by omega))=some r ∧
      r.final=cfg bits pre bits.length (by omega) ∧ r.steps=bits.length :=
  (write_prefix bits pre 0 bits.length (by omega)).run (by simp [HierarchyFixedWord.raw,cfg])

def zeroField : List Bool := frame zeroCode.bits
noncomputable def machine := RepeatMachine.machine (HierarchyFixedWord.raw zeroField) (fun _ _ => true)
noncomputable def entry (pre : List Bool) (count : ℕ) :=
  RepeatMachine.cfg 0 (cfg zeroField pre 0 (by omega)) count 1
noncomputable def endpoint (pre : List Bool) (count : ℕ) :=
  RepeatMachine.cfg 3 (cfg zeroField (pre++(List.replicate count zeroField).flatten) 0 (by omega)) count 1

theorem zeroField_length : zeroField.length=7 := by decide

theorem iterate_append (n : ℕ) (pre : List Bool) :
    RepeatMachine.iterate (fun out => (true,out++zeroField)) n pre=
      (true,pre++(List.replicate n zeroField).flatten) := by
  induction n generalizing pre with
  | zero => simp [RepeatMachine.iterate]
  | succ n ih => simp [RepeatMachine.iterate,ih,List.replicate_succ,List.append_assoc]

theorem pad_run (pre : List Bool) (count : ℕ) :
    ∃ r,runFrom machine (10*count+3) (entry pre count)=some r ∧
      r.steps≤10*count+3 ∧ r.final=endpoint pre count := by
  have hs (out : List Bool) (_ : True) := write_run zeroField out
  have hsupply : ∀ out : List Bool, True → ∃ r,
      runFrom (HierarchyFixedWord.raw zeroField) 7 (cfg zeroField out 0 (by omega))=some r ∧
      r.steps≤7 ∧ r.final.heads=(cfg zeroField (out++zeroField) 0 (by omega)).heads ∧
      r.final.tapes=(cfg zeroField (out++zeroField) 0 (by omega)).tapes ∧
      (true : Bool)=true ∧ ((true : Bool)=true → True) := by
    intro out _
    obtain ⟨r,hr,hf,ht⟩ := hs out trivial
    refine ⟨r,hr,ht.le,?_,?_,rfl,fun _ => trivial⟩
    · rw [hf]
      funext i
      simp [cfg]
    · rw [hf]
      funext i
      simp [cfg]
  obtain ⟨r,hr,ht,hf⟩ := RepeatMachine.repeat_run (HierarchyFixedWord.raw zeroField)
    (fun _ _ => true) (fun out => cfg zeroField out 0 (by omega))
    (fun out => (true,out++zeroField)) (fun _ => True) 7
    (fun _ _ => rfl) hsupply count pre trivial
  rw [iterate_append] at hf
  have he : count*(7+3)+3=10*count+3 := by omega
  rw [he] at hr ht
  exact ⟨r,hr,ht,hf⟩

end NearCubicWires.RepairSource.ProjectionNormalization.Constants
