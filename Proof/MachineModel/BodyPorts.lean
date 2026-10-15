import Proof.MachineModel.Body

/-! Named live ports of the five-stage occurrence body. Only the three
accumulators change; the source cursor advances across its original frame. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def tailPortHeads {q : ℕ} (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool)
    (H : Fin (T a) → ℕ) (j : Fin 12) :=
  if j=3 then (c3++List.replicate (children a g).length true).length else
  if j=2 then (c2++(children a g).flatMap exactWord).length else
  if j=10 then 1 else
  if j=1 then (c1++natWord (children a g).length).length else H (ex a j)
def tailPortTapes {q : ℕ} (_C : ℕ) (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool)
    (A : Fin (T a) → List Bool) (j : Fin 12) :=
  if j=3 then c3++List.replicate (children a g).length true else
  if j=2 then c2++(children a g).flatMap exactWord else
  if j=10 then UnaryTemplate.tape q else
  if j=1 then c1++natWord (children a g).length else A (ex a j)

theorem tail_ports (C q : ℕ) (g : SupportedNormalizedGate q) (c1 c2 c3 : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool) (j : Fin 12) :
    tailHeads a g c1 c2 c3 H (ex a j)=tailPortHeads a g c1 c2 c3 H j ∧
    tailTapes a C g c1 c2 c3 A (ex a j)=tailPortTapes a C g c1 c2 c3 A j := by
  unfold tailHeads tailTapes totalHeads totalTapes tailPortHeads tailPortTapes
  by_cases h3:j=3
  · subst j
    simp only [↓reduceIte]
    exact ⟨dockH_slot (totSlots a) (tot_injective a) _ _ 1,
      install_slot (totSlots a) (tot_injective a) _ _ 1⟩
  have nt:=notin_tot a (ex a j) (fun i=>bk_ne_ex a i j)
    (fun he=>h3 (ex_injective a he))
  rw [dockH_other _ _ _ _ nt,install_other _ _ _ _ nt]
  simp only [h3,↓reduceIte]
  unfold recordHeads recordTapes
  by_cases h2:j=2
  · subst j
    simp only [↓reduceIte]
    exact ⟨dockH_slot (recSlots a) (rec_injective a) _ _ 2,
      install_slot (recSlots a) (rec_injective a) _ _ 2⟩
  by_cases h10:j=10
  · subst j
    simp only [h2,↓reduceIte]
    exact ⟨dockH_slot (recSlots a) (rec_injective a) _ _ 3,
      install_slot (recSlots a) (rec_injective a) _ _ 3⟩
  have nr:=notin_rec a (ex a j) (fun i=>bk_ne_ex a i j)
    (fun he=>h2 (ex_injective a he)) (fun he=>h10 (ex_injective a he))
  rw [dockH_other _ _ _ _ nr,install_other _ _ _ _ nr]
  simp only [h2,h10,↓reduceIte]
  unfold fieldHeads fieldTapes
  by_cases h1:j=1
  · subst j
    simp only [↓reduceIte]
    exact ⟨dockH_slot (fieldSlots a) (field_injective a) _ _ 2,
      install_slot (fieldSlots a) (field_injective a) _ _ 2⟩
  have nf:=notin_field a (ex a j) (fun i=>bk_ne_ex a i j)
    (fun he=>h1 (ex_injective a he))
  rw [dockH_other _ _ _ _ nf,install_other _ _ _ _ nf]
  simp only [h1,↓reduceIte]
  exact ⟨trivial,trivial⟩

theorem source_special (C pre size : ℕ) (word source : List Bool)
    (H : Fin (T a) → ℕ) (A : Fin (T a) → List Bool)
    (KH : Fin (SB a) → ℕ) (K : Fin (SB a) → List Bool) :
    sourceHeads a pre size H KH (str a)=pre+size ∧
    sourceTapes a C word source A K (str a)=source ∧
    sourceHeads a pre size H KH (fcp a)=0 ∧
    sourceTapes a C word source A K (fcp a)=List.replicate C false := by
  simp only [str,fcp]
  rw [source_head_extra,source_tape_extra,source_head_extra,source_tape_extra]
  exact ⟨dockH_slot (copySlots a) (copy_injective a) _ _ 0,
    install_slot (copySlots a) (copy_injective a) _ _ 0,
    dockH_slot (copySlots a) (copy_injective a) _ _ 2,
    install_slot (copySlots a) (copy_injective a) _ _ 2⟩

end NearCubicWires.ExtDecompositionBatch
