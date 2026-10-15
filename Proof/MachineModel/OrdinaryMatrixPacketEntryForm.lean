import Proof.MachineModel.OrdinaryMatrixPacketBootstrapErase

/-! Literal entry bytes for the reusable packet caller. These equations
identify the exact cold/padded configuration supplied by paid erase/copy. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketEntryForm
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem plane_tapes (r : Request) (bit : ℕ) (i : Fin 425) :
    (MatrixVariableInput.input r bit).tapes i=
      if i.val=0 then physicalInput r else if i.val=424 then UnaryTemplate.tape (2*bit) else [] := by
  refine Fin.addCases (m := 409) (n := 16) (fun j => ?_) (fun j => ?_) i
  · change (Fin.addCases (m := 409) (n := 16) (motive := fun _ => List Bool)
      (MatrixSignedEntry.input r) (MatrixVariablePlane.extraTapes bit)) (j.castAdd 16)=_
    rw [Fin.addCases_left]
    simp only [MatrixSignedEntry.input,Fin.ext_iff,Fin.val_zero,Fin.val_castAdd]
    rw [if_neg (by omega : j.val≠424)]
  · change (Fin.addCases (m := 409) (n := 16) (motive := fun _ => List Bool)
      (MatrixSignedEntry.input r) (MatrixVariablePlane.extraTapes bit)) (j.natAdd 409)=_
    rw [Fin.addCases_right]
    change (if j=15 then UnaryTemplate.tape (2*bit) else [])=
      if 409+j.val=0 then physicalInput r else if 409+j.val=424 then UnaryTemplate.tape (2*bit) else []
    rw [if_neg (by omega : ¬409+j.val=0)]
    by_cases hj : j=15
    · subst j
      simp
    · rw [if_neg hj,if_neg (fun he => hj (Fin.ext (by omega)))]

theorem product_tapes (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (i : Fin (MatrixVariableProduct.tapes a)) :
    (MatrixVariableProduct.input a r bit).tapes i=
      if i.val=0 then physicalInput r else if i.val=424 then UnaryTemplate.tape (2*bit) else [] := by
  refine Fin.addCases (m := 425) (n := (source a).program.tapeCount) (fun j => ?_) (fun j => ?_) i
  · change (Fin.addCases (m := 425) (n := (source a).program.tapeCount) (motive := fun _ => List Bool)
      (MatrixVariableInput.input r bit).tapes (fun _ => [])) (j.castAdd (source a).program.tapeCount)=_
    rw [Fin.addCases_left]
    exact plane_tapes r bit j
  · change (Fin.addCases (m := 425) (n := (source a).program.tapeCount) (motive := fun _ => List Bool)
      (MatrixVariableInput.input r bit).tapes (fun _ => [])) (j.natAdd 425)=_
    rw [Fin.addCases_right]
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem count_tapes (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool) (i : Fin (MatrixVariableCount.tapes a)) :
    (MatrixVariablePacket.input a r bit out).tapes i=
      if i.val=0 then physicalInput r else if i.val=424 then UnaryTemplate.tape (2*bit)
      else if i.val=MatrixVariableProduct.tapes a+16 then out else [] := by
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  refine Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (fun j => ?_) (fun j => ?_) i
  · change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (motive := fun _ => List Bool)
      (MatrixVariableProduct.input a r bit).tapes (MatrixVariableCount.extraTapes out)) (j.castAdd 17)=_
    rw [Fin.addCases_left,product_tapes]
    simp only [Fin.val_castAdd]
    rw [if_neg (by omega : j.val≠MatrixVariableProduct.tapes a+16)]
  · change (Fin.addCases (m := MatrixVariableProduct.tapes a) (n := 17) (motive := fun _ => List Bool)
      (MatrixVariableProduct.input a r bit).tapes (MatrixVariableCount.extraTapes out)) (j.natAdd (MatrixVariableProduct.tapes a))=_
    rw [Fin.addCases_right]
    change (if j=16 then out else [])=
      if MatrixVariableProduct.tapes a+j.val=0 then physicalInput r
      else if MatrixVariableProduct.tapes a+j.val=424 then UnaryTemplate.tape (2*bit)
      else if MatrixVariableProduct.tapes a+j.val=MatrixVariableProduct.tapes a+16 then out else []
    rw [if_neg (by omega : MatrixVariableProduct.tapes a+j.val≠0),
      if_neg (by omega : MatrixVariableProduct.tapes a+j.val≠424)]
    by_cases hj : j=16
    · subst j
      simp
    · rw [if_neg hj,if_neg (fun he => hj (Fin.ext (by omega)))]

theorem input_tapes (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool) (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    (MatrixVariablePacketReset.input a r bit out).tapes i=
      if i.val=0 then physicalInput r else if i.val=424 then UnaryTemplate.tape (2*bit)
      else if i.val=MatrixVariableProduct.tapes a+16 then out else [] := by
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  refine Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (fun j => ?_) (fun j => ?_) i
  · change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (motive := fun _ => List Bool)
      (MatrixVariablePacket.input a r bit out).tapes (fun _ => [])) (j.castAdd 1)=_
    rw [Fin.addCases_left]
    exact count_tapes a r bit out j
  · fin_cases j
    change (Fin.addCases (m := MatrixVariableCount.tapes a) (n := 1) (motive := fun _ => List Bool)
      (MatrixVariablePacket.input a r bit out).tapes (fun _ => [])) ((0 : Fin 1).natAdd (MatrixVariableCount.tapes a))=_
    rw [Fin.addCases_right]
    simp only [Fin.val_natAdd,Nat.add_zero]
    unfold MatrixVariableCount.tapes
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

end NearCubicWires.RepairOrdinary.MatrixPacketEntryForm
