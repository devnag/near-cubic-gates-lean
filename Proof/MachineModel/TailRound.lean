import Proof.MachineModel.SourceRound

/-! The actual constructor output supplies all three accumulated streams:
per-occurrence count, ordered child body, and running unary total. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

noncomputable def fieldHeads {q : ℕ} (g : SupportedNormalizedGate q) (c1 : List Bool) (H : Fin (T a) → ℕ) :=
  dockH (fieldSlots a) H ![2*natBitLength (children a g).length+1,0,(c1++natWord (children a g).length).length]
noncomputable def fieldTapes {q : ℕ} (C : ℕ) (g : SupportedNormalizedGate q) (c1 : List Bool)
    (A : Fin (T a) → List Bool) :=
  install (fieldSlots a) A ![ZeroPadding.pad C (exactListWord (children a g)),
    StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength (children a g).length)) (A (bfld a)),
    c1++natWord (children a g).length]
noncomputable def recordHeads {q : ℕ} (g : SupportedNormalizedGate q) (c2 : List Bool) (H : Fin (T a) → ℕ) :=
  dockH (recSlots a) H ![2*natBitLength (children a g).length+1+((children a g).flatMap exactWord).length,0,
    (c2++(children a g).flatMap exactWord).length,1,1]
noncomputable def recordTapes {q : ℕ} (C : ℕ) (g : SupportedNormalizedGate q) (c2 : List Bool)
    (A : Fin (T a) → List Bool) :=
  install (recSlots a) A ![ZeroPadding.pad C (exactListWord (children a g)),
    Records.savedList (children a g) (A (bfld a)),c2++(children a g).flatMap exactWord,
    UnaryTemplate.tape q,ZeroPadding.pad C (UnaryTemplate.tape (children a g).length)]
noncomputable def totalHeads {q : ℕ} (g : SupportedNormalizedGate q) (c3 : List Bool) (H : Fin (T a) → ℕ) :=
  dockH (totSlots a) H ![1,(c3++List.replicate (children a g).length true).length]
noncomputable def totalTapes {q : ℕ} (C : ℕ) (g : SupportedNormalizedGate q) (c3 : List Bool)
    (A : Fin (T a) → List Bool) :=
  install (totSlots a) A ![ZeroPadding.pad C (UnaryTemplate.tape (children a g).length),
    c3++List.replicate (children a g).length true]
noncomputable def tailHeads {q : ℕ} (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool) (H : Fin (T a) → ℕ) :=
  totalHeads a g c3 (recordHeads a g c2 (fieldHeads a g c1 H))
noncomputable def tailTapes {q : ℕ} (C : ℕ) (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool)
    (A : Fin (T a) → List Bool) :=
  totalTapes a C g c3 (recordTapes a C g c2 (fieldTapes a C g c1 A))
noncomputable def tailRound:=Composition.machine (Composition.machine (stage3 a) (stage4 a)) (stage5 a)
def tailCost {q : ℕ} (g : SupportedNormalizedGate q):=
  (2*natBitLength (children a g).length+3)+1+
    (((children a g).flatMap exactWord).length+(6*q+10)*(children a g).length+3)+1+
    (2*(children a g).length+2)

theorem tail_round (C q : ℕ) (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (hsrcT : A (bsrc a)=ZeroPadding.pad C (exactListWord (children a g))) (hsrcH : H (bsrc a)=0)
    (hfldH : H (bfld a)=0)
    (hcntT : A (cnt a)=c1) (hcntH : H (cnt a)=c1.length)
    (hbodT : A (bod a)=c2) (hbodH : H (bod a)=c2.length)
    (hdomT : A (dom a)=UnaryTemplate.tape q) (hdomH : H (dom a)=1)
    (hkT : A (bcnt a)=ZeroPadding.pad C (UnaryTemplate.tape (children a g).length)) (hkH : H (bcnt a)=1)
    (htotT : A (tot a)=c3) (htotH : H (tot a)=c3.length)
    (hk : (children a g).length+2 ≤ C) :
    Step (tailRound a) (tailCost a g) H A (tailHeads a g c1 c2 c3 H) (tailTapes a C g c1 c2 c3 A) := by
  have field_bod:∀ j,fieldSlots a j≠bod a:=
    notin_field a (bod a) (fun i=>bk_ne_ex a i 2) (ex_ne a (by decide : (2 : Fin 12).val≠1))
  have field_dom:∀ j,fieldSlots a j≠dom a:=
    notin_field a (dom a) (fun i=>bk_ne_ex a i 10) (ex_ne a (by decide : (10 : Fin 12).val≠1))
  have field_tot:∀ j,fieldSlots a j≠tot a:=
    notin_field a (tot a) (fun i=>bk_ne_ex a i 3) (ex_ne a (by decide : (3 : Fin 12).val≠1))
  have record_tot:∀ j,recSlots a j≠tot a:=
    notin_rec a (tot a) (fun i=>bk_ne_ex a i 3)
      (ex_ne a (by decide : (3 : Fin 12).val≠2)) (ex_ne a (by decide : (3 : Fin 12).val≠10))
  have first:=stage3_step a C q g c1 H A hsrcT hsrcH hfldH hcntT hcntH
  have second:=stage4_step a C q g c2 (fieldHeads a g c1 H) (fieldTapes a C g c1 A)
    (install_slot (fieldSlots a) (field_injective a) A _ 0)
    (dockH_slot (fieldSlots a) (field_injective a) H _ 0)
    (dockH_slot (fieldSlots a) (field_injective a) H _ 1)
    ((install_other (fieldSlots a) A _ _ field_bod).trans hbodT)
    ((dockH_other (fieldSlots a) H _ _ field_bod).trans hbodH)
    ((install_other (fieldSlots a) A _ _ field_dom).trans hdomT)
    ((dockH_other (fieldSlots a) H _ _ field_dom).trans hdomH)
    ((install_other (fieldSlots a) A _ _ (field_ne_bcnt a)).trans hkT)
    ((dockH_other (fieldSlots a) H _ _ (field_ne_bcnt a)).trans hkH) hk
  have third:=stage5_step a C q g c3
    (recordHeads a g c2 (fieldHeads a g c1 H)) (recordTapes a C g c2 (fieldTapes a C g c1 A))
    (install_slot (recSlots a) (rec_injective a) _ _ 4)
    (dockH_slot (recSlots a) (rec_injective a) _ _ 4)
    ((install_other (recSlots a) _ _ _ record_tot).trans
      ((install_other (fieldSlots a) A _ _ field_tot).trans htotT))
    ((dockH_other (recSlots a) _ _ _ record_tot).trans
      ((dockH_other (fieldSlots a) H _ _ field_tot).trans htotH))
  exact (first.seq second).seq third

end NearCubicWires.ExtDecompositionBatch
