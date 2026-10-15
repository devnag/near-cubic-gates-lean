import Proof.PCP.PCPPNativeOracle

/-! Physically allocate the exact reusable query bank from blank work and
the actual common G driver. The original descriptor and C/F are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryAllocate
open LocalBitMultitape PCPPNativeQueryReusable PCPPNativeQueryReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) (C F G : ℕ) (i : Fin 171) : List Bool :=
  if i=0 then bits else if i=4 then List.replicate C true
  else if i=120 then List.replicate F true else if i=169 then List.replicate G true else []
noncomputable def machine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 163)

theorem erase_input (bits : List Bool) (C F G : ℕ) (j : Fin 165) :
    input bits C F G (eraseSlots j)=
      (Fin.addCases (motive := fun _ : Fin 165 => List Bool) (m := 164) (n := 1)
        (Fin.addCases (motive := fun _ : Fin 164 => List Bool) (m := 163) (n := 1) (fun _ => []) (fun _ => List.replicate G true))
        (fun _ => [])) j := by
  refine Fin.addCases (m := 163) (n := 2) (fun i => ?_) (fun i => ?_) j
  · have h := erase_work i
    have h0 : eraseSlots (i.castAdd 2)≠0 := by apply Fin.ne_of_val_ne; change _≠0; omega
    have h4 : eraseSlots (i.castAdd 2)≠4 := by apply Fin.ne_of_val_ne; change _≠4; omega
    have h120 : eraseSlots (i.castAdd 2)≠120 := by apply Fin.ne_of_val_ne; change _≠120; omega
    have h169 : eraseSlots (i.castAdd 2)≠169 := by apply Fin.ne_of_val_ne; change _≠169; omega
    have hin : input bits C F G (eraseSlots (i.castAdd 2))=[] := by
      simp only [input,h0,h4,h120,h169,ite_false]
    rw [hin]
    simp [Fin.addCases,show i.val<164 by omega,i.isLt]
  · fin_cases i <;> rfl

theorem outside (bits : List Bool) (C F G : ℕ) (i : Fin 171)
    (hi : ∀ j,eraseSlots j≠i) : data bits [] 0 C F G [] i=input bits C F G i := by
  rcases coverage i with ⟨j,rfl⟩|⟨j,hj⟩
  · fin_cases j <;> simp [data,input,resetSlots,retainedSlots]
  · exact False.elim (hi j hj)

theorem allocate_run (bits : List Bool) (C F G : ℕ) :
    ClockJoin.ReadyRun machine (2*G+4) (input bits C F G) (data bits [] 0 C F G []) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready G 0 (fun _ : Fin 163 => []) (by simp)
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 163) (2*G+4)
      (Fin.addCases (Fin.addCases (fun _ : Fin 163 => []) (fun _ : Fin 1 => List.replicate G true))
        (fun _ : Fin 1 => [])) (erased G) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    rw [ht]
    funext j
    refine Fin.addCases (m := 163) (n := 2) (fun i => ?_) (fun i => ?_) j
    · rfl
    · fin_cases i <;> simp [erased]
  have focused := ready.focus eraseSlots erase_injective (input bits C F G) (erase_input bits C F G)
  rw [HierarchyWidth.install_eq eraseSlots erase_injective _ (data bits [] 0 C F G []) _
    (fun j => (erased_data bits 0 C F G [] j).symm) (outside bits C F G)] at focused
  exact focused

end NearCubicWires.RepairOrdinary.PCPPNativeQueryAllocate
