import Proof.MachineModel.CleanRound

/-! The cleanup's exact ports, without exposing the enclosing controller. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)
noncomputable def clearedHeads (H : Fin (T a) → ℕ) :=
  dockH (eraseSlots a) (maskedHeads a H) (fun _=>0)
noncomputable def clearedTapes (C : ℕ) (A : Fin (T a) → List Bool) :=
  install (eraseSlots a) (loggedTapes a C A) (cleanData a C)

theorem erase_avoids (j : Fin 12) (h7 : j.val≠7) (h8 : j.val≠8) (h9 : j.val≠9)
    (i : Fin (SB a+1+1+1)) : eraseSlots a i≠(ex a j).castAdd 1 := by
  intro he
  have hv:=congrArg Fin.val he
  rw [eraseSlots_val] at hv
  simp only [Fin.val_castAdd,ex_val] at hv
  have hi:=i.isLt
  split_ifs at hv <;> omega

theorem erase_avoids_log (i : Fin (SB a+1+1+1)) :
    eraseSlots a i≠Fin.natAdd (T a) (0 : Fin 1) := by
  intro he
  have hv:=congrArg Fin.val he
  rw [eraseSlots_val] at hv
  simp only [Fin.val_natAdd,Fin.val_zero,Nat.add_zero] at hv
  have hi:=i.isLt
  unfold T at hv
  split_ifs at hv <;> omega

theorem cleared_bank (C : ℕ) (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (i : Fin (SB a)) :
    clearedHeads a H ((bk a i).castAdd 1)=0 ∧
    clearedTapes a C A ((bk a i).castAdd 1)=List.replicate C false := by
  unfold clearedHeads clearedTapes
  rw [←eraseSlots_bank,dockH_slot _ (eraseSlots_injective a),install_slot _ (eraseSlots_injective a)]
  simp only [cleanData,Fin.addCases_left,and_self]

theorem cleared_extra (C : ℕ) (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (j : Fin 12) :
    clearedHeads a H ((ex a j).castAdd 1)=(if j=7 ∨ j=8 ∨ j=9 then 0 else H (ex a j)) ∧
    clearedTapes a C A ((ex a j).castAdd 1)=
      (if j=7 then List.replicate C false else if j=8 then List.replicate C true
       else if j=9 then List.replicate (C+1) false else A (ex a j)) := by
  unfold clearedHeads clearedTapes
  by_cases h7:j=7
  · subst j
    rw [show (ex a 7).castAdd 1=(fcp a).castAdd 1 from rfl,←eraseSlots_counter,
      dockH_slot _ (eraseSlots_injective a),install_slot _ (eraseSlots_injective a)]
    simp only [cleanData,Fin.addCases_left,true_or,↓reduceIte,and_self]
  by_cases h8:j=8
  · subst j
    rw [show (ex a 8).castAdd 1=(drv a).castAdd 1 from rfl,←eraseSlots_driver,
      dockH_slot _ (eraseSlots_injective a),install_slot _ (eraseSlots_injective a)]
    simp only [cleanData,Fin.addCases_left,Fin.addCases_right,h7,true_or,or_true,↓reduceIte,and_self]
  by_cases h9:j=9
  · subst j
    rw [show (ex a 9).castAdd 1=(wsp a).castAdd 1 from rfl,←eraseSlots_workspace,
      dockH_slot _ (eraseSlots_injective a),install_slot _ (eraseSlots_injective a)]
    simp only [cleanData,Fin.addCases_right,h7,h8,or_true,↓reduceIte,and_self]
  have hn:=erase_avoids a j (fun h=>h7 (Fin.ext h)) (fun h=>h8 (Fin.ext h)) (fun h=>h9 (Fin.ext h))
  rw [dockH_other _ _ _ _ hn,install_other _ _ _ _ hn]
  simp only [maskedHeads,loggedTapes,Fin.addCases_left,selected_extra a j h7,
    Bool.false_eq_true,h7,h8,h9,false_or,↓reduceIte,and_self]

theorem cleared_log (C : ℕ) (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool) :
    clearedHeads a H (Fin.natAdd (T a) (0 : Fin 1))=0 ∧
    clearedTapes a C A (Fin.natAdd (T a) (0 : Fin 1))=List.replicate C false := by
  unfold clearedHeads clearedTapes
  rw [dockH_other _ _ _ _ (erase_avoids_log a),install_other _ _ _ _ (erase_avoids_log a)]
  simp only [maskedHeads,loggedTapes,Fin.addCases_right,and_self]

end NearCubicWires.ExtDecompositionBatch
