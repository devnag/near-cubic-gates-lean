import Proof.MachineModel.OrdinaryMatrixRightScan

/-! Reusable framed scalar copy for advancing right-plane buckets. Both
bounded counters are physically retained and every selected head is reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixFrameCopy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coreInput (bits backing : List Bool) : Fin 3 → List Bool :=
  ![frame bits,backing,List.replicate (2*bits.length+1) false]
def input (bits backing : List Bool) : Fin 4 → List Bool :=
  ![frame bits,backing,List.replicate (2*bits.length+1) false,List.replicate (4*bits.length+3) false]
def machine : Machine 4 6 := Rewind.machine FrameLoad.machine

theorem copy_run (bits backing : List Bool) (hb : backing.length ≤ 2*bits.length+1) :
    ∃ r : ExecutionReceipt 4 6,run machine (8*bits.length+8) (input bits backing)=some r ∧
      r.final.tapes=![frame bits,frame bits,List.replicate (2*bits.length+1) false,List.replicate (4*bits.length+3) false] ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=8*bits.length+8 := by
  obtain ⟨base,hbRun,hbf,hbs,_⟩ := CellLoad.loader_run [] bits [] backing hb
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hbRun hbf
  have hi : CellLoad.loaderInput (frame bits) 0 backing bits.length=
      initialConfiguration FrameLoad.machine (coreInput bits backing) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hbRun
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace FrameLoad.machine _
    (coreInput bits backing) base hbRun (4*bits.length+3)
  have hin : Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (coreInput bits backing)
      (fun _ : Fin 1 => List.replicate (4*bits.length+3) false)=input bits backing := by
    funext i; fin_cases i <;> rfl
  rw [hin,hbs] at hr
  have htime : 2*(4*bits.length+3)+2=8*bits.length+8 := by omega
  rw [htime] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  have h3 : (0 : Fin 1).natAdd 3=(3 : Fin 4) := by decide
  rw [h3,hbs,max_self] at hcounter
  funext i
  fin_cases i
  · exact (ht 0).trans (by rw [hbf]; rfl)
  · exact (ht 1).trans (by rw [hbf]; rfl)
  · exact (ht 2).trans (by rw [hbf]; rfl)
  · exact hcounter

end NearCubicWires.RepairOrdinary.MatrixFrameCopy
