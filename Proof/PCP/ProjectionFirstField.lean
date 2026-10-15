import Proof.Hierarchy.HierarchySelectedSource

/-! Paid first-field extraction retains the complete raw two-field hierarchy
request. Both source and copied target heads are reset for the next call. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.FirstField
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Rewind.machine FrameLoad.machine
def input (bits suffix : List Bool) : Fin 4 → List Bool := ![frame bits++suffix,[],[],[]]
def output (bits suffix : List Bool) : Fin 4 → List Bool :=
  ![frame bits++suffix,frame bits,List.replicate (2*bits.length+1) false,List.replicate (4*bits.length+3) false]

theorem ready (bits suffix : List Bool) :
    ClockJoin.ReadyRun machine (8*bits.length+8) (input bits suffix) (output bits suffix) := by
  obtain ⟨base,hb,hf,hs,hspace⟩ := FrameLoad.load_run [] bits suffix [] (by simp)
  have hi : FrameLoad.scan 0 ([]++frame bits++suffix) 0 [] []=
      initialConfiguration FrameLoad.machine ![frame bits++suffix,[],[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  change runFrom FrameLoad.machine (4*bits.length+3)
    (FrameLoad.scan 0 ([]++frame bits++suffix) 0 [] [])=some base at hb
  rw [hi] at hb
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace FrameLoad.machine _ _ base hb 0
  have hin : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![frame bits++suffix,[],[]] (fun _ : Fin 1 => []))=input bits suffix := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2) (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
    ![frame bits++suffix,[],[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hin] at hr
  have he : 2*base.steps+2=8*bits.length+8 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i; fin_cases i
  · simpa [output,hf,FrameLoad.reset] using ht 0
  · simpa [output,hf,FrameLoad.reset] using ht 1
  · simpa [output,hf,FrameLoad.reset] using ht 2
  · simpa [output,hs] using hcount

end NearCubicWires.RepairSource.ProjectionNormalization.FirstField
