import Proof.PCP.PCPPNativeInputFields

/-! Original compound input to the retained hierarchy stream producer. The
oracle descriptor is a disjoint physically loaded raw field. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
open LocalBitMultitape RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : RepairSource.ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (k : ℕ) := 4+HierarchyStreams.tapes source k
def loadSlots (k : ℕ) (i : Fin 4) : Fin (tapes source k) := i.castAdd (HierarchyStreams.tapes source k)
def hierarchySlots (k : ℕ) (i : Fin (HierarchyStreams.tapes source k)) : Fin (tapes source k) :=
  if i.val=0 then ⟨1,by dsimp [tapes]; omega⟩ else i.natAdd 4
theorem load_injective (k : ℕ) : Function.Injective (loadSlots source k) := by
  intro a b he
  exact Fin.ext (congrArg (fun i : Fin (tapes source k) => i.val) he)
theorem hierarchy_injective (k : ℕ) : Function.Injective (hierarchySlots source k) := by
  intro a b he
  apply Fin.ext
  have hv := congrArg Fin.val he
  dsimp only [hierarchySlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem hierarchy_away (k : ℕ) (j : Fin 4) (hj : j.val≠1) :
    ∀ i,hierarchySlots source k i≠loadSlots source k j := by
  intro i he
  have hv := congrArg Fin.val he
  dsimp only [hierarchySlots,loadSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (k : ℕ) (a b : List Bool) : Fin (tapes source k) → List Bool :=
  SourceHandoff.sourceTapes (PCPPNativeInputFields.word a b)
def loaded (k : ℕ) (a b : List Bool) :=
  install (loadSlots source k) (input source k a b) (PCPPNativeInputFields.output a b)
theorem load_input (k : ℕ) (a b : List Bool) (i : Fin 4) :
    input source k a b (loadSlots source k i)=PCPPNativeInputFields.input a b i := by
  fin_cases i <;> rfl
theorem loaded_local (k : ℕ) (a b : List Bool) (i : Fin 4) :
    loaded source k a b (loadSlots source k i)=PCPPNativeInputFields.output a b i :=
  install_slot _ (load_injective source k) _ _ _
theorem hierarchy_input (k : ℕ) (a b : List Bool) (i : Fin (HierarchyStreams.tapes source k)) :
    loaded source k a b (hierarchySlots source k i)=SourceHandoff.sourceTapes a i := by
  by_cases hi : i.val=0
  · have he : hierarchySlots source k i=loadSlots source k 1 := by simp [hierarchySlots,hi,loadSlots]; rfl
    rw [he,loaded_local]
    simp [PCPPNativeInputFields.output,SourceHandoff.sourceTapes,hi]
  · have hn : ¬∃ j,loadSlots source k j=hierarchySlots source k i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [loadSlots,hierarchySlots,hi,if_false,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    rw [loaded,install_other _ _ _ _ (fun j hj => hn ⟨j,hj⟩)]
    simp [input,SourceHandoff.sourceTapes,hierarchySlots,hi]

def load (k : ℕ) := RecoveryFocus.machine (loadSlots source k) PCPPNativeInputFields.machine
def hierarchy (k CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (hierarchySlots source k) (HierarchyStreams.machine source k CH Cpad code)
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (load source k) (hierarchy source k CH Cpad code)
def budget (k CH Cpad : ℕ) (code x bound oracle : List Bool) :=
  PCPPNativeInputFields.budget (frame x++frame bound) oracle+1+HierarchyStreams.budget source k CH Cpad code x

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
