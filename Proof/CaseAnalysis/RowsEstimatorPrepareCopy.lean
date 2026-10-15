import Proof.CaseAnalysis.RowsEstimatorPrepareWords

/-! One physical D scan copies all seven retained fields into the actual Warm input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem old_val (p : Program) (i : Fin (WholePrefix.tapes p)) : (old p i).val=i.val := rfl

@[simp] theorem copy_source (p : Program) (i : Fin 7) :
    copySlots p ((i.castAdd (7+1)).castAdd 1)=source p i := by
  simp only [copySlots,Fin.addCases_left]
@[simp] theorem copy_dest (p : Program) (i : Fin 7) :
    copySlots p (((i.castAdd 1).natAdd 7).castAdd 1)=dest p i := by
  simp only [copySlots,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem copy_driver (p : Program) (i : Fin 1) :
    copySlots p (((i.natAdd 7).natAdd 7).castAdd 1)=driver p := by
  simp only [copySlots,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem copy_log (p : Program) (i : Fin 1) :
    copySlots p (i.natAdd (7+(7+1)))=log p := by
  simp only [copySlots,Fin.addCases_right]

theorem copy_avoids_old (p : Program) (i : Fin (WholePrefix.tapes p))
    (hi : ∀ k,WarmFields.slots p k≠i) : ∀ j,copySlots p j≠old p i := by
  intro j
  refine Fin.addCases (m:=7+(7+1)) (n:=1) (fun k=>?_) (fun k=>?_) j
  · refine Fin.addCases (m:=7) (n:=7+1) (fun l=>?_) (fun l=>?_) k
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      rw [copy_source,source_val] at hv
      rw [old_val] at hv
      have h:=i.isLt
      unfold Reuse.tapes at hv
      omega
    · refine Fin.addCases (m:=7) (n:=1) (fun m=>?_) (fun m=>?_) l
      · intro he
        rw [copy_dest] at he
        exact hi m (Fin.ext (congrArg (fun z : Fin (tapes p)=>z.val) he))
      · intro he
        have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
        rw [copy_driver,driver_val] at hv
        rw [old_val] at hv
        have h:=i.isLt
        omega
  · intro he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    rw [copy_log,log_val] at hv
    rw [old_val] at hv
    have h:=i.isLt
    omega

theorem copy_avoids_spare (p : Program) : ∀ j,copySlots p j≠spare p := by
  intro j
  refine Fin.addCases (m:=7+(7+1)) (n:=1) (fun k=>?_) (fun k=>?_) j
  · refine Fin.addCases (m:=7) (n:=7+1) (fun l=>?_) (fun l=>?_) k
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      rw [copy_source,source_val] at hv
      change Reuse.tapes p+l.val=WholePrefix.tapes p+1 at hv
      unfold Reuse.tapes at hv
      omega
    · refine Fin.addCases (m:=7) (n:=1) (fun m=>?_) (fun m=>?_) l
      · intro he
        have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
        rw [copy_dest,dest_val] at hv
        change (WarmFields.slots p m).val=WholePrefix.tapes p+1 at hv
        have h:=(WarmFields.slots p m).isLt
        omega
      · intro he
        have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
        rw [copy_driver,driver_val] at hv
        change WholePrefix.tapes p+2=WholePrefix.tapes p+1 at hv
        omega
  · intro he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    rw [copy_log,log_val] at hv
    change WholePrefix.tapes p=WholePrefix.tapes p+1 at hv
    omega

theorem copy_input (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) (ha : ∀ i,A (WarmFields.slots p i)=List.replicate D false)
    (i : Fin (7+(7+1)+1)) :
    data p A D (D+1) fields (copySlots p i)=MetadataBatch.input fields D i := by
  refine Fin.addCases (m:=7+(7+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=7) (n:=7+1) (fun k=>?_) (fun k=>?_) j
    · simp only [copy_source,at_source,MetadataBatch.input,Fin.addCases_left]
    · refine Fin.addCases (m:=7) (n:=1) (fun l=>?_) (fun l=>?_) k
      · simp only [copy_dest,dest,at_old,ha,MetadataBatch.input,Fin.addCases_left,Fin.addCases_right]
      · simp only [copy_driver,at_driver,MetadataBatch.input,Fin.addCases_left,Fin.addCases_right]
  · simp only [copy_log,at_log,MetadataBatch.input,Fin.addCases_right]

theorem copy_output (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) :
    install (copySlots p) (data p A D (D+1) fields) (MetadataBatch.output fields D)=
      data p (install (WarmFields.slots p) A (fun i=>ZeroPadding.pad D (fields i))) D (D+1) fields := by
  classical
  apply data_ext p
  · intro i
    by_cases hit : ∃ k,WarmFields.slots p k=i
    · obtain ⟨k,rfl⟩:=hit
      change install (copySlots p) (data p A D (D+1) fields) (MetadataBatch.output fields D) (dest p k)=
        data p _ D (D+1) fields (dest p k)
      rw [←copy_dest,install_slot _ (copy_injective p)]
      simp only [MetadataBatch.output,Fin.addCases_left,Fin.addCases_right,copy_dest,dest,at_old,
        install_slot _ (WarmFields.injective p)]
    · have ho : ∀ k,WarmFields.slots p k≠i:=by simpa using hit
      rw [install_other _ _ _ _ (copy_avoids_old p i ho),at_old,at_old,install_other _ _ _ _ ho]
  · rw [←copy_log p 0,install_slot _ (copy_injective p)]
    simp only [MetadataBatch.output,Fin.addCases_right,copy_log,at_log]
  · rw [install_other _ _ _ _ (copy_avoids_spare p),at_spare,at_spare]
  · rw [←copy_driver p 0,install_slot _ (copy_injective p)]
    simp only [MetadataBatch.output,Fin.addCases_left,Fin.addCases_right,copy_driver,at_driver]
  · intro i
    rw [←copy_source,install_slot _ (copy_injective p)]
    simp only [MetadataBatch.output,Fin.addCases_left,copy_source,at_source]

theorem copy_ready (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) (ha : ∀ i,A (WarmFields.slots p i)=List.replicate D false)
    (hd : ∀ i,(fields i).length ≤ D) :
    ReadyRun (copy p) (2*D+4) (data p A D (D+1) fields)
      (data p (install (WarmFields.slots p) A (fun i=>ZeroPadding.pad D (fields i))) D (D+1) fields) := by
  have h:=(MetadataBatch.ready fields D hd).focus (copySlots p) (copy_injective p)
    (data p A D (D+1) fields) (copy_input p A D fields ha)
  rw [copy_output] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
