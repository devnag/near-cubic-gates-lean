import Proof.Hierarchy.HierarchyBinaryPowerLoop
import Proof.Hierarchy.HierarchyFixedWord

/-! Initialize the fixed-degree power computation by actually printing one
and expanding it to the paid width. All future multiply blocks stay blank. -/
namespace NearCubicWires.RepairOrdinary.HierarchyPower
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialData (D w : ℕ) (bits : List Bool) : Fin (tapes D) → List Bool :=
  fun i => if i.val=0 then frame bits else if i.val=1 then List.replicate w true else []
def printedData (D w : ℕ) (bits : List Bool) : Fin (tapes D) → List Bool :=
  fun i => if i.val=3 then frame [true] else if i.val=6 then List.replicate 3 false else initialData D w bits i
def initializedData (D w : ℕ) (bits : List Bool) : Fin (tapes D) → List Bool :=
  fun i => if i.val=2 then frame (binary w 1) else if i.val=4 then [true]
    else if i.val=5 then List.replicate (2*w+1) false else printedData D w bits i
def printSlots (D : ℕ) : Fin 2 → Fin (tapes D) :=
  ![⟨3,by dsimp [tapes]; omega⟩,⟨6,by dsimp [tapes]; omega⟩]
def normalizeSlots (D : ℕ) : Fin 5 → Fin (tapes D) :=
  ![⟨1,by dsimp [tapes]; omega⟩,⟨3,by dsimp [tapes]; omega⟩,⟨2,by dsimp [tapes]; omega⟩,
    ⟨4,by dsimp [tapes]; omega⟩,⟨5,by dsimp [tapes]; omega⟩]
theorem print_injective (D : ℕ) : Function.Injective (printSlots D) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [printSlots] at h ⊢
theorem normalize_injective (D : ℕ) : Function.Injective (normalizeSlots D) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [normalizeSlots] at h ⊢
noncomputable def printProgram (D : ℕ) := RecoveryFocus.machine (printSlots D)
  (HierarchyFixedWord.machine (frame [true]))
noncomputable def normalizeProgram (D : ℕ) := RecoveryFocus.machine (normalizeSlots D) ClockNormalize.machine
noncomputable def bootstrap (D : ℕ) := Composition.machine (printProgram D) (normalizeProgram D)

theorem print_ready (D w : ℕ) (bits : List Bool) :
    ReadyRun (printProgram D) 8 (initialData D w bits) (printedData D w bits) := by
  have h := (HierarchyFixedWord.word_ready (frame [true])).focus (printSlots D) (print_injective D)
    (initialData D w bits) (by intro j; fin_cases j <;> rfl)
  have he : install (printSlots D) (initialData D w bits)
      ![frame [true],List.replicate 3 false]=printedData D w bits := by
    funext i
    by_cases h3 : i.val=3
    · have hi : i=printSlots D 0 := Fin.ext h3
      subst i
      exact install_slot (printSlots D) (print_injective D) _ _ 0
    by_cases h6 : i.val=6
    · have hi : i=printSlots D 1 := Fin.ext h6
      subst i
      exact install_slot (printSlots D) (print_injective D) _ _ 1
    have hnone : ∀ j : Fin 2,printSlots D j≠i := by
      intro j
      fin_cases j <;> apply Fin.ne_of_val_ne
      · simpa [printSlots] using Ne.symm h3
      · simpa [printSlots] using Ne.symm h6
    rw [install_other _ _ _ _ hnone]
    simp [printedData,h3,h6]
  change ReadyRun (printProgram D) 8 (initialData D w bits)
    (install (printSlots D) (initialData D w bits) ![frame [true],List.replicate 3 false]) at h
  rw [he] at h
  exact h

theorem scalar_one_ready (w : ℕ) (hw : 1≤w) :
    ReadyRun ClockNormalize.machine (4*w+4)
      ![List.replicate w true,frame [true],[],[],[]]
      ![List.replicate w true,frame [true],frame (binary w 1),[true],List.replicate (2*w+1) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w [true] (by simpa using hw)
  have hi : ClockNormalize.input w [true]=![List.replicate w true,frame [true],[],[],[]] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs⟩
  funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem normalize_ready (D w : ℕ) (bits : List Bool) (hw : 1≤w) :
    ReadyRun (normalizeProgram D) (4*w+4) (printedData D w bits) (initializedData D w bits) := by
  have h := (scalar_one_ready w hw).focus (normalizeSlots D) (normalize_injective D)
    (printedData D w bits) (by intro j; fin_cases j <;> rfl)
  have he : install (normalizeSlots D) (printedData D w bits)
      ![List.replicate w true,frame [true],frame (binary w 1),[true],List.replicate (2*w+1) false]=
      initializedData D w bits := by
    funext i
    by_cases h1 : i.val=1
    · have hi : i=normalizeSlots D 0 := Fin.ext h1
      subst i
      exact install_slot (normalizeSlots D) (normalize_injective D) _ _ 0
    by_cases h3 : i.val=3
    · have hi : i=normalizeSlots D 1 := Fin.ext h3
      subst i
      exact install_slot (normalizeSlots D) (normalize_injective D) _ _ 1
    by_cases h2 : i.val=2
    · have hi : i=normalizeSlots D 2 := Fin.ext h2
      subst i
      exact install_slot (normalizeSlots D) (normalize_injective D) _ _ 2
    by_cases h4 : i.val=4
    · have hi : i=normalizeSlots D 3 := Fin.ext h4
      subst i
      exact install_slot (normalizeSlots D) (normalize_injective D) _ _ 3
    by_cases h5 : i.val=5
    · have hi : i=normalizeSlots D 4 := Fin.ext h5
      subst i
      exact install_slot (normalizeSlots D) (normalize_injective D) _ _ 4
    have hnone : ∀ j : Fin 5,normalizeSlots D j≠i := by
      intro j
      fin_cases j <;> apply Fin.ne_of_val_ne
      · exact Ne.symm h1
      · exact Ne.symm h3
      · exact Ne.symm h2
      · exact Ne.symm h4
      · exact Ne.symm h5
    rw [install_other _ _ _ _ hnone]
    simp [initializedData,h2,h4,h5]
  rw [he] at h
  exact h

theorem bootstrap_ready (D w : ℕ) (bits : List Bool) (hw : 1≤w) :
    ReadyRun (bootstrap D) (4*w+13) (initialData D w bits) (initializedData D w bits) := by
  have h := HierarchyMultiplyEntry.join_exact (printProgram D) (normalizeProgram D) 8 (4*w+4) _ _ _
    (print_ready D w bits) (normalize_ready D w bits hw)
  have ht : 8+1+(4*w+4)=4*w+13 := by omega
  simpa only [bootstrap,ht] using h

theorem initialized_input (D C n : ℕ) (hD : 0<D) :
    Input D C n ⟨0,hD⟩ (initializedData D (HierarchyBinary.width C D n) (ClockBinary.word n)) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · simp [operand,previous,initializedData]
  · intro i hi
    simp only [Nat.mul_zero,Nat.add_zero] at hi
    simp [initializedData,printedData,initialData,show i.val≠0 by omega,show i.val≠1 by omega,
      show i.val≠2 by omega,show i.val≠3 by omega,show i.val≠4 by omega,show i.val≠5 by omega,
      show i.val≠6 by omega]

end NearCubicWires.RepairOrdinary.HierarchyPower
