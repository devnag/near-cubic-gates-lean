import Proof.PCP.PCPPNativeMass

/-! The actual compact-clause count creates a physical three-fields-per-
clause driver. Original clause bytes occupy a disjoint retained tape. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeTripleMass
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fixedSlots : Fin 2 → Fin 12 := ![1,11]
def productSlots : Fin 4 → Fin 12 := ![0,1,2,3]
def dimensionSlots : Fin 4 → Fin 12 := ![2,6,7,8]
def massSlots : Fin 5 → Fin 12 := ![4,5,8,9,10]
theorem fixed_injective : Function.Injective fixedSlots := by decide
theorem product_injective : Function.Injective productSlots := by decide
theorem dimension_injective : Function.Injective dimensionSlots := by decide
theorem mass_injective : Function.Injective massSlots := by decide
def data (source : List Bool) (M phase : ℕ) : Fin 12 → List Bool :=
  ![List.replicate M true,if 1≤phase then UnaryTemplate.tape 3 else [],
    if 2≤phase then List.replicate (M*3) true else [],
    if 2≤phase then List.replicate (WilliamsUnaryProduct.scratch M 3) false else [],
    source,[],[],[],[],[],[],if 1≤phase then List.replicate 5 false else []]
noncomputable def first := RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 3))
noncomputable def second := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def prepare := Composition.machine first second
noncomputable def dimension := RecoveryFocus.machine dimensionSlots MatrixDimensionHeader.machine
noncomputable def measure := RecoveryFocus.machine massSlots PCPSerializerCapacity.MassReady.machine
noncomputable def machine := Composition.machine (Composition.machine prepare dimension) measure
def fields (rows : List (Fin 3 → List Bool)) := rows.flatMap List.ofFn
def source (rows : List (Fin 3 → List Bool)) := FieldList.stream (fields rows)
def budget (rows : List (Fin 3 → List Bool)) :=
  (12+1+WilliamsUnaryProduct.budget rows.length 3)+1+(2*(rows.length*3)+3)+1+(16*(source rows).length+18)

theorem field_count (rows : List (Fin 3 → List Bool)) : (fields rows).length=rows.length*3 := by
  induction rows with
  | nil => simp [fields]
  | cons row rows ih =>
    simp only [fields,List.flatMap_cons,List.length_append,List.length_ofFn,List.length_cons] at ih ⊢
    omega

theorem first_run (bits : List Bool) (M : ℕ) :
    ClockJoin.ReadyRun first 12 (data bits M 0) (data bits M 1) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (UnaryTemplate.tape 3)
  have hready : ClockJoin.ReadyRun (HierarchyFixedWord.machine (UnaryTemplate.tape 3)) 12
      (fun _ => []) ![UnaryTemplate.tape 3,List.replicate 5 false] := ⟨r,hr,ht,hh,hs.le⟩
  have h := hready.focus fixedSlots fixed_injective (data bits M 0) (by intro i; fin_cases i <;> rfl)
  rw [HierarchyWidth.install_eq fixedSlots fixed_injective _ (data bits M 1) _
    (by intro i; fin_cases i <;> rfl) (by
      intro i hi
      have h1 := hi 0
      have h11 := hi 1
      fin_cases i <;> simp_all [fixedSlots,data])] at h
  exact h

theorem second_run (bits : List Bool) (M : ℕ) :
    ClockJoin.ReadyRun second (WilliamsUnaryProduct.budget M 3) (data bits M 1) (data bits M 2) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready M 3
  have hready : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget M 3)
      (WilliamsUnaryProduct.input M 3) (WilliamsUnaryProduct.output M 3) := ⟨r,hr,ht,hh,hs.le⟩
  have h := hready.focus productSlots product_injective (data bits M 1) (by intro i; fin_cases i <;> rfl)
  rw [HierarchyWidth.install_eq productSlots product_injective _ (data bits M 2) _
    (by intro i; fin_cases i <;> rfl) (by
      intro i hi
      have h2 := hi 2
      have h3 := hi 3
      fin_cases i <;> simp_all [productSlots,data])] at h
  exact h

theorem prepare_run (bits : List Bool) (M : ℕ) :
    ClockJoin.ReadyRun prepare (12+1+WilliamsUnaryProduct.budget M 3) (data bits M 0) (data bits M 2) :=
  ClockJoin.join _ _ _ _ _ _ _ (first_run bits M) (second_run bits M)

end NearCubicWires.RepairOrdinary.PCPPNativeTripleMass
