import Proof.MachineModel.OrdinaryMatrixPacketBootstrapState

/-! Exact cold-bootstrap field projections used by the original-only
copy and offset initializer. No runtime dimension is supplied here. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketColdFields
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem old_fields (a : WilliamsAlgorithm) (E C : ℕ) (r : Request)
    (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    (MatrixPacketBootstrapState.input a E C r []).tapes (MatrixPacketRestoreDock.slots a E i)=
      (MatrixVariablePacketReset.input a r 0 []).tapes i ∧
    (MatrixPacketBootstrapState.input a E C r []).heads (MatrixPacketRestoreDock.slots a E i)=
      (MatrixVariablePacketReset.input a r 0 []).heads i := by
  constructor
  · exact (Fin.addCases_left (motive := fun _ => List Bool)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).tapes)
      (right := MatrixPacketBootstrapState.counters r) ((i.castAdd (MatrixPacketCapacityNative.extra E)).castAdd 2)).trans
      ((Fin.addCases_left (motive := fun _ => List Bool) (left := (MatrixPacketCapacityNative.input a E C r 0 []).tapes)
        (right := MatrixPacketBootstrapErase.extras (physicalInput r)) (i.castAdd (MatrixPacketCapacityNative.extra E))).trans
        (Fin.addCases_left (motive := fun _ => List Bool) (left := (MatrixVariablePacketReset.input a r 0 []).tapes)
          (right := fun _ : Fin (MatrixPacketCapacityNative.extra E) => []) i))
  · exact (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).heads)
      (right := fun _ : Fin 2 => 0) ((i.castAdd (MatrixPacketCapacityNative.extra E)).castAdd 2)).trans
      ((Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixPacketCapacityNative.input a E C r 0 []).heads)
        (right := fun _ : Fin 2 => 0) (i.castAdd (MatrixPacketCapacityNative.extra E))).trans
        (Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixVariablePacketReset.input a r 0 []).heads)
          (right := fun _ : Fin (MatrixPacketCapacityNative.extra E) => 0) i))

theorem capacity_fields (a : WilliamsAlgorithm) (E C : ℕ) (r : Request)
    (i : Fin (MatrixPacketCapacityNative.extra E)) :
    (MatrixPacketBootstrapState.input a E C r []).tapes
      (((i.natAdd (MatrixVariablePacketWorkspace.tapes a)).castAdd 2).castAdd 2)=[] ∧
    (MatrixPacketBootstrapState.input a E C r []).heads
      (((i.natAdd (MatrixVariablePacketWorkspace.tapes a)).castAdd 2).castAdd 2)=0 := by
  constructor
  · exact (Fin.addCases_left (motive := fun _ => List Bool)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).tapes)
      (right := MatrixPacketBootstrapState.counters r) ((i.natAdd (MatrixVariablePacketWorkspace.tapes a)).castAdd 2)).trans
      ((Fin.addCases_left (motive := fun _ => List Bool) (left := (MatrixPacketCapacityNative.input a E C r 0 []).tapes)
        (right := MatrixPacketBootstrapErase.extras (physicalInput r)) (i.natAdd (MatrixVariablePacketWorkspace.tapes a))).trans
        (Fin.addCases_right (motive := fun _ => List Bool) (left := (MatrixVariablePacketReset.input a r 0 []).tapes)
          (right := fun _ : Fin (MatrixPacketCapacityNative.extra E) => []) i))
  · exact (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).heads)
      (right := fun _ : Fin 2 => 0) ((i.natAdd (MatrixVariablePacketWorkspace.tapes a)).castAdd 2)).trans
      ((Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixPacketCapacityNative.input a E C r 0 []).heads)
        (right := fun _ : Fin 2 => 0) (i.natAdd (MatrixVariablePacketWorkspace.tapes a))).trans
        (Fin.addCases_right (motive := fun _ => ℕ) (left := (MatrixVariablePacketReset.input a r 0 []).heads)
          (right := fun _ : Fin (MatrixPacketCapacityNative.extra E) => 0) i))

theorem external_fields (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (i : Fin 2) :
    (MatrixPacketBootstrapState.input a E C r []).tapes
      ((i.natAdd (MatrixPacketCapacityNative.tapes a E)).castAdd 2)=
        MatrixPacketBootstrapErase.extras (physicalInput r) i ∧
    (MatrixPacketBootstrapState.input a E C r []).heads
      ((i.natAdd (MatrixPacketCapacityNative.tapes a E)).castAdd 2)=0 := by
  constructor
  · exact (Fin.addCases_left (motive := fun _ => List Bool)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).tapes)
      (right := MatrixPacketBootstrapState.counters r) (i.natAdd (MatrixPacketCapacityNative.tapes a E))).trans
      (Fin.addCases_right (motive := fun _ => List Bool) (left := (MatrixPacketCapacityNative.input a E C r 0 []).tapes)
        (right := MatrixPacketBootstrapErase.extras (physicalInput r)) i)
  · exact (Fin.addCases_left (motive := fun _ => ℕ)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).heads)
      (right := fun _ : Fin 2 => 0) (i.natAdd (MatrixPacketCapacityNative.tapes a E))).trans
      (Fin.addCases_right (motive := fun _ => ℕ) (left := (MatrixPacketCapacityNative.input a E C r 0 []).heads)
        (right := fun _ : Fin 2 => 0) i)

theorem counter_fields (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (i : Fin 2) :
    (MatrixPacketBootstrapState.input a E C r []).tapes
      (i.natAdd (MatrixPacketWorkClear.tapes a E))=MatrixPacketBootstrapState.counters r i ∧
    (MatrixPacketBootstrapState.input a E C r []).heads
      (i.natAdd (MatrixPacketWorkClear.tapes a E))=0 := by
  constructor
  · exact Fin.addCases_right (motive := fun _ => List Bool)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).tapes)
      (right := MatrixPacketBootstrapState.counters r) i
  · exact Fin.addCases_right (motive := fun _ => ℕ)
      (left := (MatrixPacketBootstrapErase.input a E C r 0 [] (physicalInput r)).heads)
      (right := fun _ : Fin 2 => 0) i

theorem product_heads (a : WilliamsAlgorithm) (r : Request) (i : Fin (MatrixVariableProduct.tapes a)) :
    (MatrixVariableProduct.input a r 0).heads i=if i.val=424 then 1 else 0 := by
  refine Fin.addCases (m := 425) (n := (MatrixWilliamsProduct.source a).program.tapeCount) (fun j => ?_) (fun j => ?_) i
  · have h:=Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixVariableInput.input r 0).heads)
      (right := fun _ : Fin (MatrixWilliamsProduct.source a).program.tapeCount => 0) j
    apply h.trans
    change (MatrixVariablePlane.input r 0).heads j=_
    rw [MatrixVariablePlane.input_heads]
    simp only [Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have h:=Fin.addCases_right (motive := fun _ => ℕ) (left := (MatrixVariableInput.input r 0).heads)
      (right := fun _ : Fin (MatrixWilliamsProduct.source a).program.tapeCount => 0) j
    apply h.trans
    rw [if_neg (by simp only [Fin.val_natAdd]; omega)]

theorem core_heads (a : WilliamsAlgorithm) (r : Request) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    (MatrixVariablePacketReset.input a r 0 []).heads i=if i.val=424 then 1 else 0 := by
  have countHeads (j : Fin (MatrixVariableCount.tapes a)) :
      (MatrixVariablePacket.input a r 0 []).heads j=if j.val=424 then 1 else 0 := by
    refine Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (fun k => ?_) (fun k => ?_) j
    · have h:=Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixVariableProduct.input a r 0).heads)
        (right := MatrixVariableCount.extraHeads []) k
      exact h.trans (product_heads a r k)
    · have h:=Fin.addCases_right (motive := fun _ => ℕ) (left := (MatrixVariableProduct.input a r 0).heads)
        (right := MatrixVariableCount.extraHeads []) k
      apply h.trans
      have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
      simp only [MatrixVariableCount.extraHeads,List.length_nil,ite_self,Fin.val_natAdd]
      rw [if_neg (by omega)]
  refine Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (fun j => ?_) (fun j => ?_) i
  · have h:=Fin.addCases_left (motive := fun _ => ℕ) (left := (MatrixVariablePacket.input a r 0 []).heads)
      (right := fun _ : Fin 1 => 0) j
    exact h.trans (countHeads j)
  · have h:=Fin.addCases_right (motive := fun _ => ℕ) (left := (MatrixVariablePacket.input a r 0 []).heads)
      (right := fun _ : Fin 1 => 0) j
    apply h.trans
    have hK : 425≤MatrixVariableCount.tapes a := by unfold MatrixVariableCount.tapes MatrixVariableProduct.tapes; omega
    rw [if_neg (by simp only [Fin.val_natAdd]; omega)]

end NearCubicWires.RepairOrdinary.MatrixPacketColdFields
