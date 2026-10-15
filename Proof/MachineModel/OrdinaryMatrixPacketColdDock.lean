import Proof.MachineModel.OrdinaryMatrixPacketPrepare

/-! The executed cold copy/offset output is the literal first-packet
bootstrap input. Only the original framed request is present at entry. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketColdDock
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixPacketColdPrepare (output copied cold heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_fields (a : WilliamsAlgorithm) (E : ℕ) (r : Request) (j : Fin 4) :
    output a E r (MatrixPacketRestore.copySlots a E j)=MatrixPacketRequestCopy.output (word r) 0 0 0 j := by
  have no : ∀ k,MatrixPacketStateAdvance.slot a E k≠MatrixPacketRestore.copySlots a E j := by
    intro k
    exact Ne.symm (MatrixPacketRestoreDock.copy_misses a E (MatrixPacketState.offset a)
      (by change (424 : ℕ)≠0; decide) j)
  exact (install_other (MatrixPacketStateAdvance.slot a E) (copied a E r)
    (fun _ => UnaryTemplate.tape 0) _ no).trans
    (install_slot (MatrixPacketRestore.copySlots a E) (MatrixPacketRestore.copySlots_injective a E)
      (cold a E r) (MatrixPacketRequestCopy.output (word r) 0 0 0) j)

theorem old_tapes (a : WilliamsAlgorithm) (E : ℕ) (r : Request)
    (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    output a E r (MatrixPacketRestoreDock.slots a E i)=(MatrixVariablePacketReset.input a r 0 []).tapes i := by
  have ht:=MatrixPacketEntryForm.input_tapes a r 0 [] i
  simp only [ite_self] at ht
  apply Eq.trans (b := if i.val=0 then physicalInput r else if i.val=424 then UnaryTemplate.tape 0 else []) ?_ ht.symm
  by_cases h0 : i.val=0
  · rw [if_pos h0]
    have he : MatrixPacketRestoreDock.slots a E i=MatrixPacketRestore.copySlots a E 1 := Fin.ext h0
    rw [he]
    have h:=copy_fields a E r 1
    exact h.trans (ZeroPadding.pad_zero (frame (word r)))
  rw [if_neg h0]
  by_cases h1 : i.val=424
  · rw [if_pos h1]
    have he : MatrixPacketRestoreDock.slots a E i=MatrixPacketStateAdvance.slot a E 0 := Fin.ext h1
    rw [he]
    exact install_slot (MatrixPacketStateAdvance.slot a E) (MatrixPacketStateAdvance.slot_injective a E)
      (copied a E r) (fun _ => UnaryTemplate.tape 0) 0
  rw [if_neg h1]
  have no : ∀ j,MatrixPacketStateAdvance.slot a E j≠MatrixPacketRestoreDock.slots a E i := by
    intro j he
    exact h1 (congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) he.symm)
  apply (install_other (MatrixPacketStateAdvance.slot a E) (copied a E r)
    (fun _ => UnaryTemplate.tape 0) _ no).trans
  apply (install_other (MatrixPacketRestore.copySlots a E) (cold a E r)
    (MatrixPacketRequestCopy.output (word r) 0 0 0) _ (MatrixPacketRestoreDock.copy_misses a E i h0)).trans
  exact if_neg (MatrixPacketRestoreControls.controls_outside a E 2 i)

theorem middle_blank (a : WilliamsAlgorithm) (E : ℕ) (r : Request)
    (i : Fin (MatrixPacketRestore.tapes a E))
    (hlo : MatrixVariablePacketWorkspace.tapes a≤ i.val) (hhi : i.val≤MatrixPacketCapacityNative.tapes a E) :
    output a E r i=[] := by
  have hW : 425≤MatrixVariablePacketWorkspace.tapes a := by
    unfold MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega
  have no : ∀ j,MatrixPacketStateAdvance.slot a E j≠i := by
    intro j he
    have hv:=congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) he
    change (424 : ℕ)=i.val at hv
    omega
  have nc : ∀ j,MatrixPacketRestore.copySlots a E j≠i := by
    intro j he
    have hv:=congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) he
    fin_cases j
    · change MatrixPacketCapacityNative.tapes a E+1=i.val at hv
      omega
    · change (0 : ℕ)=i.val at hv
      omega
    · change MatrixPacketWorkClear.tapes a E=i.val at hv
      unfold MatrixPacketWorkClear.tapes at hv
      omega
    · change MatrixPacketWorkClear.tapes a E+1=i.val at hv
      unfold MatrixPacketWorkClear.tapes at hv
      omega
  exact (install_other (MatrixPacketStateAdvance.slot a E) (copied a E r) (fun _ => UnaryTemplate.tape 0) i no).trans
    ((install_other (MatrixPacketRestore.copySlots a E) (cold a E r) (MatrixPacketRequestCopy.output (word r) 0 0 0) i nc).trans
      (if_neg (Ne.symm (nc 0))))

theorem head_val (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (MatrixPacketRestore.tapes a E)) :
    heads a E i=if i.val=424 then 1 else 0 := by
  have he : (i=MatrixPacketStateAdvance.slot a E 0)↔i.val=424 :=
    ⟨fun h => congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) h,fun h => Fin.ext h⟩
  simp only [heads,he]

theorem tapes_eq (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :
    output a E r=(MatrixPacketBootstrapState.input a E C r []).tapes := by
  funext i
  refine Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := MatrixPacketCapacityNative.extra E)
        (fun z => ?_) (fun z => ?_) k
      · exact (old_tapes a E r z).trans (MatrixPacketColdFields.old_fields a E C r z).1.symm
      · have h:=middle_blank a E r (((z.natAdd (MatrixVariablePacketWorkspace.tapes a)).castAdd 2).castAdd 2)
          (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)
          (by have hz:=z.isLt; unfold MatrixPacketCapacityNative.tapes; simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)
        exact h.trans (MatrixPacketColdFields.capacity_fields a E C r z).1.symm
    · fin_cases k
      · have h:=middle_blank a E r (((0 : Fin 2).natAdd (MatrixPacketCapacityNative.tapes a E)).castAdd 2)
          (by unfold MatrixPacketCapacityNative.tapes; simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero]; omega)
          (by simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero]; omega)
        exact h.trans (MatrixPacketColdFields.external_fields a E C r 0).1.symm
      · exact (copy_fields a E r 0).trans (MatrixPacketColdFields.external_fields a E C r 1).1.symm
  · fin_cases j
    · have h:=copy_fields a E r 2
      have hn : MatrixPacketRequestCopy.output (word r) 0 0 0 2=MatrixPacketBootstrapState.counters r 0 := by
        change List.replicate (max 0 (2*(word r).length+1)) false=List.replicate (2*(word r).length+1) false
        rw [Nat.zero_max]
      exact (h.trans hn).trans (MatrixPacketColdFields.counter_fields a E C r 0).1.symm
    · have h:=copy_fields a E r 3
      have hn : MatrixPacketRequestCopy.output (word r) 0 0 0 3=MatrixPacketBootstrapState.counters r 1 := by
        change List.replicate (max 0 (4*(word r).length+3)) false=List.replicate (4*(word r).length+3) false
        rw [Nat.zero_max]
      exact (h.trans hn).trans (MatrixPacketColdFields.counter_fields a E C r 1).1.symm

theorem heads_eq (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :
    heads a E=(MatrixPacketBootstrapState.input a E C r []).heads := by
  have hW : 425≤MatrixVariablePacketWorkspace.tapes a := by
    unfold MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega
  have hN : MatrixVariablePacketWorkspace.tapes a≤MatrixPacketCapacityNative.tapes a E := by
    unfold MatrixPacketCapacityNative.tapes; omega
  funext i
  refine Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m := MatrixPacketCapacityNative.tapes a E) (n := 2) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m := MatrixVariablePacketWorkspace.tapes a) (n := MatrixPacketCapacityNative.extra E)
        (fun z => ?_) (fun z => ?_) k
      · exact ((head_val a E _).trans (MatrixPacketColdFields.core_heads a r z).symm).trans
          (MatrixPacketColdFields.old_fields a E C r z).2.symm
      · apply Eq.trans (b := 0) ?_ (MatrixPacketColdFields.capacity_fields a E C r z).2.symm
        rw [head_val]
        exact if_neg (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)
    · apply Eq.trans (b := 0) ?_ (MatrixPacketColdFields.external_fields a E C r k).2.symm
      rw [head_val]
      exact if_neg (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)
  · apply Eq.trans (b := 0) ?_ (MatrixPacketColdFields.counter_fields a E C r j).2.symm
    rw [head_val]
    exact if_neg (by simp only [Fin.val_natAdd]; unfold MatrixPacketWorkClear.tapes; omega)

end NearCubicWires.RepairOrdinary.MatrixPacketColdDock
