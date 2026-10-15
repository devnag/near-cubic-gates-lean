import Proof.MachineModel.OrdinaryMatrixPacketRestore
import Proof.MachineModel.OrdinaryMatrixPacketEntryForm

/-! The paid erase/copy output is the literal padded packet-entry array.
Only the two live packet controls remain outside the erased work set. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketRestoreDock
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def slots (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) : Fin (MatrixPacketRestore.tapes a E) :=
  (MatrixPacketBootstrapErase.old a E i).castAdd 2
theorem slots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slots a E) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) h)

theorem work_witness (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixVariablePacketWorkspace.tapes a))
    (hi : MatrixVariablePacketWorkspace.working a i) :
    ∃ j,MatrixPacketWorkClear.work a E j=MatrixPacketBootstrapErase.old a E i := by
  have hb:=i.isLt
  unfold MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes at hb
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  unfold MatrixVariablePacketWorkspace.working at hi
  by_cases h0 : i.val<424
  · refine ⟨⟨i.val,by unfold MatrixPacketWorkClear.count; omega⟩,?_⟩
    apply Fin.ext
    rw [MatrixPacketWorkClear.work_val]
    change (if i.val<424 then i.val else if i.val<MatrixVariableProduct.tapes a+15 then i.val+1 else i.val+2)=i.val
    rw [if_pos h0]
  by_cases h1 : i.val<MatrixVariableProduct.tapes a+16
  · refine ⟨⟨i.val-1,by unfold MatrixPacketWorkClear.count; omega⟩,?_⟩
    apply Fin.ext
    rw [MatrixPacketWorkClear.work_val]
    change (if i.val-1<424 then i.val-1 else if i.val-1<MatrixVariableProduct.tapes a+15 then i.val-1+1 else i.val-1+2)=i.val
    split_ifs <;> omega
  · refine ⟨⟨i.val-2,by unfold MatrixPacketWorkClear.count; omega⟩,?_⟩
    apply Fin.ext
    rw [MatrixPacketWorkClear.work_val]
    change (if i.val-2<424 then i.val-2 else if i.val-2<MatrixVariableProduct.tapes a+15 then i.val-2+1 else i.val-2+2)=i.val
    split_ifs <;> omega

theorem copy_misses (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hi : i.val≠0) :
    ∀ j,MatrixPacketRestore.copySlots a E j≠slots a E i := by
  intro j hj
  have hv:=congrArg Fin.val hj
  have hb:=i.isLt
  fin_cases j
  · change MatrixPacketCapacityNative.tapes a E+1=i.val at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega
  · change (0 : ℕ)=i.val at hv
    exact hi hv.symm
  · change MatrixPacketWorkClear.tapes a E=i.val at hv
    unfold MatrixPacketWorkClear.tapes MatrixPacketCapacityNative.tapes at hv
    omega
  · change MatrixPacketWorkClear.tapes a E+1=i.val at hv
    unfold MatrixPacketWorkClear.tapes MatrixPacketCapacityNative.tapes at hv
    omega

theorem clear_misses (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixVariablePacketWorkspace.tapes a))
    (hi : ¬MatrixVariablePacketWorkspace.working a i) :
    ∀ j,MatrixPacketWorkClear.slots a E j≠MatrixPacketBootstrapErase.old a E i := by
  intro j hj
  rw [MatrixPacketWorkClear.slots_cases] at hj
  split_ifs at hj
  · have hw:=MatrixPacketBootstrapErase.work_working a E ⟨j.val,by assumption⟩
    have he : MatrixPacketBootstrapErase.workIndex a E ⟨j.val,by assumption⟩=i :=
      Fin.ext (congrArg (fun k : Fin (MatrixPacketWorkClear.tapes a E) => k.val) hj)
    exact hi (he ▸ hw)
  · have hc:=MatrixPacketWorkClear.cap_bound a E
    have hv:=congrArg Fin.val hj
    change (MatrixPacketWorkClear.capTape a E).val=i.val at hv
    omega
  · have hv:=congrArg Fin.val hj
    change MatrixPacketCapacityNative.tapes a E=i.val at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega

theorem output_tapes (a : WilliamsAlgorithm) (E cap log left right : ℕ) (bits : List Bool)
    (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool)
    (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    MatrixPacketRestore.output a E cap log left right bits ambient (slots a E i)=
      if i.val=0 then ZeroPadding.pad cap (frame bits)
      else if MatrixVariablePacketWorkspace.working a i then List.replicate cap false
      else ambient (MatrixPacketBootstrapErase.old a E i) := by
  by_cases h0 : i.val=0
  · rw [if_pos h0]
    have he : slots a E i=MatrixPacketRestore.copySlots a E 1 := Fin.ext h0
    rw [he]
    exact install_slot (MatrixPacketRestore.copySlots a E) (MatrixPacketRestore.copySlots_injective a E) _ _ 1
  rw [if_neg h0]
  have hc := install_other (MatrixPacketRestore.copySlots a E)
    (Fin.addCases (motive := fun _ => List Bool) (MatrixPacketRestore.cleared a E cap log ambient) (MatrixPacketRestore.extras left right))
    (MatrixPacketRequestCopy.output bits cap left right) (slots a E i) (copy_misses a E i h0)
  change MatrixPacketRestore.output a E cap log left right bits ambient (slots a E i)=_
  apply hc.trans
  change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
    (MatrixPacketRestore.cleared a E cap log ambient) (MatrixPacketRestore.extras left right))
      ((MatrixPacketBootstrapErase.old a E i).castAdd 2)=_
  rw [Fin.addCases_left]
  by_cases hi : MatrixVariablePacketWorkspace.working a i
  · rw [if_pos hi]
    obtain ⟨j,hj⟩ := work_witness a E i hi
    rw [←hj]
    have hs:=install_slot (MatrixPacketWorkClear.slots a E) (MatrixPacketWorkClear.slots_injective a E) ambient
      (MatrixPacketWorkClear.eraseData cap (max log (cap+1)) (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false))
      ((j.castAdd 1).castAdd 1)
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_left] at hs
    exact hs
  · rw [if_neg hi]
    exact install_other _ _ _ _ (clear_misses a E i hi)

end NearCubicWires.RepairOrdinary.MatrixPacketRestoreDock
