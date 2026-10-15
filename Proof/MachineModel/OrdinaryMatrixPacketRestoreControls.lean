import Proof.MachineModel.OrdinaryMatrixPacketOffset

/-! The five physical controls needed by the next packet call. These are
actual erase/copy outputs, including stable copy counters. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketRestoreControls
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def controls (a : WilliamsAlgorithm) (E : ℕ) : Fin 5 → Fin (MatrixPacketRestore.tapes a E) :=
  ![(MatrixPacketWorkClear.capTape a E).castAdd 2,
    (MatrixPacketWorkClear.logTape a E).castAdd 2,
    MatrixPacketRestore.copySlots a E 0,
    MatrixPacketRestore.copySlots a E 2,
    MatrixPacketRestore.copySlots a E 3]
def values (cap : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  ![List.replicate cap true,List.replicate (cap+1) false,frame bits,
    List.replicate (2*bits.length+1) false,List.replicate (4*bits.length+3) false]

theorem controls_outside (a : WilliamsAlgorithm) (E : ℕ) (j : Fin 5) :
    ∀ i,MatrixPacketRestoreDock.slots a E i≠controls a E j := by
  intro i he
  have hb:=i.isLt
  have hv:=congrArg (fun k : Fin (MatrixPacketRestore.tapes a E) => k.val) he
  have hc:=MatrixPacketWorkClear.cap_bound a E
  fin_cases j
  · change i.val=(MatrixPacketWorkClear.capTape a E).val at hv
    omega
  · change i.val=MatrixPacketCapacityNative.tapes a E at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega
  · change i.val=MatrixPacketCapacityNative.tapes a E+1 at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega
  · change i.val=MatrixPacketWorkClear.tapes a E at hv
    unfold MatrixPacketWorkClear.tapes MatrixPacketCapacityNative.tapes at hv
    omega
  · change i.val=MatrixPacketWorkClear.tapes a E+1 at hv
    unfold MatrixPacketWorkClear.tapes MatrixPacketCapacityNative.tapes at hv
    omega

theorem copy_misses (a : WilliamsAlgorithm) (E : ℕ) (j : Fin 2) :
    ∀ k,MatrixPacketRestore.copySlots a E k≠controls a E j.castSucc.castSucc.castSucc := by
  have cv (j : Fin 5) : (controls a E j).val=(![(MatrixPacketCapacityNative.outputTape a E).val,
      MatrixPacketCapacityNative.tapes a E,MatrixPacketCapacityNative.tapes a E+1,
      MatrixPacketWorkClear.tapes a E,MatrixPacketWorkClear.tapes a E+1] : Fin 5 → ℕ) j := by
    fin_cases j <;> rfl
  have kv (k : Fin 4) : (MatrixPacketRestore.copySlots a E k).val=(![MatrixPacketCapacityNative.tapes a E+1,
      0,MatrixPacketWorkClear.tapes a E,MatrixPacketWorkClear.tapes a E+1] : Fin 4 → ℕ) k := by
    fin_cases k <;> rfl
  intro k he
  have hc:=MatrixPacketWorkClear.cap_bound a E
  change MatrixVariablePacketWorkspace.tapes a≤(MatrixPacketCapacityNative.outputTape a E).val at hc
  have hu:=(MatrixPacketCapacityNative.outputTape a E).isLt
  have hv:=congrArg (fun z : Fin (MatrixPacketRestore.tapes a E) => z.val) he
  rw [cv,kv] at hv
  have hpos : 0<MatrixVariablePacketWorkspace.tapes a := by
    unfold MatrixVariablePacketWorkspace.tapes; omega
  unfold MatrixPacketWorkClear.tapes at hv
  fin_cases j <;> fin_cases k <;> norm_num at hv <;> omega

theorem output_controls (a : WilliamsAlgorithm) (E cap : ℕ) (bits : List Bool)
    (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool) (j : Fin 5) :
    MatrixPacketRestore.output a E cap (cap+1) (2*bits.length+1) (4*bits.length+3) bits ambient
      (controls a E j)=values cap bits j := by
  fin_cases j
  · have hm:=install_other (MatrixPacketRestore.copySlots a E)
      (Fin.addCases (motive := fun _ => List Bool)
        (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
        (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
      (MatrixPacketRequestCopy.output bits cap (2*bits.length+1) (4*bits.length+3))
      (controls a E 0) (copy_misses a E 0)
    apply hm.trans
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
      (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
        ((MatrixPacketWorkClear.capTape a E).castAdd 2)=List.replicate cap true
    refine Eq.trans (Fin.addCases_left (m := MatrixPacketWorkClear.tapes a E) (n := 2)
      (left := MatrixPacketRestore.cleared a E cap (cap+1) ambient)
      (right := MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3))
      (motive := fun _ => List Bool) (MatrixPacketWorkClear.capTape a E)) ?_
    have h:=install_slot (MatrixPacketWorkClear.slots a E) (MatrixPacketWorkClear.slots_injective a E) ambient
      (MatrixPacketWorkClear.eraseData cap (max (cap+1) (cap+1))
        (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false))
      (((0 : Fin 1).natAdd (MatrixPacketWorkClear.count a)).castAdd 1)
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_left,Fin.addCases_right] at h
    convert h using 1
    rfl
  · have hm:=install_other (MatrixPacketRestore.copySlots a E)
      (Fin.addCases (motive := fun _ => List Bool)
        (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
        (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
      (MatrixPacketRequestCopy.output bits cap (2*bits.length+1) (4*bits.length+3))
      (controls a E 1) (copy_misses a E 1)
    apply hm.trans
    change (Fin.addCases (m := MatrixPacketWorkClear.tapes a E) (n := 2) (motive := fun _ => List Bool)
      (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
      (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
        ((MatrixPacketWorkClear.logTape a E).castAdd 2)=List.replicate (cap+1) false
    refine Eq.trans (Fin.addCases_left (m := MatrixPacketWorkClear.tapes a E) (n := 2)
      (left := MatrixPacketRestore.cleared a E cap (cap+1) ambient)
      (right := MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3))
      (motive := fun _ => List Bool) (MatrixPacketWorkClear.logTape a E)) ?_
    have h:=install_slot (MatrixPacketWorkClear.slots a E) (MatrixPacketWorkClear.slots_injective a E) ambient
      (MatrixPacketWorkClear.eraseData cap (max (cap+1) (cap+1))
        (fun _ : Fin (MatrixPacketWorkClear.count a) => List.replicate cap false))
      ((0 : Fin 1).natAdd (MatrixPacketWorkClear.count a+1))
    simp only [MatrixPacketWorkClear.slots,MatrixPacketWorkClear.eraseData,Fin.addCases_right] at h
    convert h.trans (congrArg (fun n => List.replicate n false) (max_self (cap+1))) using 1
    rfl
  · have h:=install_slot (MatrixPacketRestore.copySlots a E) (MatrixPacketRestore.copySlots_injective a E)
      (Fin.addCases (motive := fun _ => List Bool) (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
        (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
      (MatrixPacketRequestCopy.output bits cap (2*bits.length+1) (4*bits.length+3)) 0
    exact h
  · have h:=install_slot (MatrixPacketRestore.copySlots a E) (MatrixPacketRestore.copySlots_injective a E)
      (Fin.addCases (motive := fun _ => List Bool) (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
        (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
      (MatrixPacketRequestCopy.output bits cap (2*bits.length+1) (4*bits.length+3)) 2
    exact h.trans (congrArg (fun n => List.replicate n false) (max_self (2*bits.length+1)))
  · have h:=install_slot (MatrixPacketRestore.copySlots a E) (MatrixPacketRestore.copySlots_injective a E)
      (Fin.addCases (motive := fun _ => List Bool) (MatrixPacketRestore.cleared a E cap (cap+1) ambient)
        (MatrixPacketRestore.extras (2*bits.length+1) (4*bits.length+3)))
      (MatrixPacketRequestCopy.output bits cap (2*bits.length+1) (4*bits.length+3)) 3
    exact h.trans (congrArg (fun n => List.replicate n false) (max_self (4*bits.length+3)))

end NearCubicWires.RepairOrdinary.MatrixPacketRestoreControls
