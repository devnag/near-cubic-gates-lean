import Proof.PCP.PCPPNativeFrame
import Proof.PCP.ProjectionNormalizationField

/-! Physically frame the retained original hierarchy word, which contains
exactly its two existing fields. Two original field-copy calls measure the
word while copying it; no hierarchy source or length prepass is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HierarchyFrame
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw:=Composition.machine Field.machine Field.machine
def rawInput (left right : List Bool) : Fin 2→List Bool:=![frame left++frame right,[]]
def rawBudget (left right : List Bool):=(2*left.length+1)+1+(2*right.length+1)

theorem raw_run (left right : List Bool) : ∃ r,run raw (rawBudget left right) (rawInput left right)=some r ∧
    r.steps≤rawBudget left right ∧ r.final.tapes 1=frame left++frame right ∧
    r.final.heads 1=(frame left++frame right).length ∧ r.final.tapes 0=frame left++frame right:=by
  obtain ⟨first,hf,ft,fs⟩:=Field.copy_run [] left (frame right) []
  obtain ⟨last,hl,lt,ls⟩:=Field.copy_run (frame left) right [] (frame left)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hf ft
  simp only [List.append_nil] at hl lt
  have hi : Composition.restart first.final Field.machine.start=
      Field.cfg 0 (frame left++frame right) (frame left).length (frame left):=by
    rw [ft]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [Composition.restart,Field.cfg,frame_length]
    · rfl
  have hr : runFrom Field.machine (2*right.length+1) (Composition.restart first.final Field.machine.start)=some last:=by
    rw [hi]
    exact hl
  have whole:=Composition.run_join Field.machine Field.machine _ _ _ first last hf hr
  have hin : Composition.leftConfig 3 (Field.cfg 0 (frame left++frame right) 0 [])=
      initialConfiguration raw (rawInput left right):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  rw [hin] at whole
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤rawBudget left right
    rw [fs,ls]
    rfl
  · change last.final.tapes 1=_
    rw [lt]
    rfl
  · change last.final.heads 1=_
    rw [lt]
    rfl
  · change last.final.tapes 0=_
    rw [lt]
    rfl

theorem field_forward : CursorRestore.NoLeft Field.machine 1:=by
  intro q bits action h
  simp only [Field.machine] at h
  split at h
  · cases h;simp
  · split at h
    · cases h;simp
    · contradiction
theorem forward : CursorRestore.NoLeft raw 1:=
  CursorRestore.composition_forward _ _ _ field_forward field_forward
noncomputable def machine:=AppendOutputFrame.machine raw 1
def input (hierarchy : List Bool) : Fin 6→List Bool:=SourceHandoff.sourceTapes hierarchy
def budget (left right : List Bool):=2*rawBudget left right+4*(frame left++frame right).length+7

theorem frame_run (left right : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget left right) (input (frame left++frame right)) out ∧
      out 4=frame (frame left++frame right) ∧ out 0=frame left++frame right:=by
  obtain ⟨base,hb,bs,bt,bh,keep⟩:=raw_run left right
  obtain ⟨r,hr,ht,hh,hkeep,hs⟩:=PCPPNativeFrame.frame_run raw 1 forward _ _ base hb _ bt bh
  have hi : AppendOutputFrame.input (rawInput left right)=input (frame left++frame right):=by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  have ready : ClockJoin.ReadyRun machine (2*base.steps+4*(frame left++frame right).length+7)
      (input (frame left++frame right)) r.final.tapes:=⟨r,hr,rfl,hh,hs⟩
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),ht,(hkeep 0).trans keep⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.HierarchyFrame
