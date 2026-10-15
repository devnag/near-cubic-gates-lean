import Proof.CaseAnalysis.CaseTwoHonestInput
import Proof.CaseAnalysis.CaseTwoRankSlice

/-! An actual final-address field is produced in both raw and framed form.
The original slice appends exactly its requested bits, so the existing
append-output framer measures and frames them without a separate length pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SliceFrame
open LocalBitMultitape RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem forward : CursorRestore.NoLeft SliceMachine.machine 1:=by
  intro q bits a h
  simp only [SliceMachine.machine] at h
  split_ifs at h <;>cases h <;>simp [SliceMachine.action]
noncomputable def machine:=AppendOutputFrame.machine SliceMachine.machine 1
def input (pre field tail : List Bool) : Fin 8→List Bool:=
  ![frame (pre++field++tail),[],List.replicate pre.length true,List.replicate field.length true,[],[],[],[]]
def budget (offset width : ℕ):=4*offset+8*width+11

theorem slice_run (pre field tail : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget pre.length field.length) (input pre field tail) out ∧
      out 6=frame field ∧ out 1=field ∧ out 0=frame (pre++field++tail) ∧
      out 2=List.replicate pre.length true ∧ out 3=List.replicate field.length true:=by
  obtain ⟨base,hb,bf,bs,_⟩:=SliceMachine.field_run pre field tail
  have bt:base.final.tapes 1=field:=by rw [bf];rfl
  have bh:base.final.heads 1=field.length:=by rw [bf];rfl
  obtain ⟨r,hr,rt,rh,keep,rs⟩:=PCPPNativeFrame.frame_run SliceMachine.machine 1 forward _ _ base hb _ bt bh
  have hi:AppendOutputFrame.input (SliceMachine.input pre field tail)=input pre field tail:=by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  have he:2*base.steps+4*field.length+7=budget pre.length field.length:=by rw [bs];unfold budget;omega
  rw [he] at hr rs
  exact ⟨_,⟨r,hr,rfl,rh,rs⟩,rt,(keep 1).trans bt,
    (keep 0).trans (by rw [bf];rfl),(keep 2).trans (by rw [bf];rfl),(keep 3).trans (by rw [bf];rfl)⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SliceFrame
