import Proof.MachineModel.OrdinaryMatrixDimensionBinary
import Proof.MachineModel.OrdinaryWilliamsUnaryProduct
import Proof.Hierarchy.HierarchyWidth

/-! Fixed unary polynomial evaluation for dimensions polynomial in log T.
The coefficient is printed by finite control; every multiplication and reset
is executed. No clock value T or proof envelope V is expanded into unary. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionPower
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 3+2*D
def valueSlot (D j : ℕ) (hj : j ≤ D) : Fin (tapes D) := ⟨1+2*j,by dsimp [tapes]; omega⟩
def slot (D : ℕ) (j : Fin D) : Fin 4 → Fin (tapes D) :=
  ![valueSlot D j.val j.isLt.le,⟨0,by simp [tapes]⟩,
    valueSlot D (j.val+1) (by omega),⟨4+2*j.val,by dsimp [tapes]; omega⟩]
def printSlots (D : ℕ) : Fin 2 → Fin (tapes D) :=
  ![⟨1,by dsimp [tapes]; omega⟩,⟨2,by dsimp [tapes]; omega⟩]
theorem slot_injective (D : ℕ) (j : Fin D) : Function.Injective (slot D j) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [slot,valueSlot] at he ⊢ <;> omega
theorem print_injective (D : ℕ) : Function.Injective (printSlots D) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [printSlots] at h ⊢

def input (D n : ℕ) : Fin (tapes D) → List Bool :=
  fun i => if i.val=0 then UnaryTemplate.tape n else []
def Fields (D C n j : ℕ) (hj : j ≤ D) (out : Fin (tapes D) → List Bool) : Prop :=
  out ⟨0,by simp [tapes]⟩=UnaryTemplate.tape n ∧
  out (valueSlot D j hj)=List.replicate (C*n^j) true ∧
  ∀ i,3+2*j ≤ i.val → out i=[]

noncomputable def printProgram (D C : ℕ) := RecoveryFocus.machine (printSlots D)
  (HierarchyFixedWord.machine (List.replicate C true))
noncomputable def productProgram (D : ℕ) (j : Fin D) :=
  RecoveryFocus.machine (slot D j) ClockUnaryProduct.machine
def states (C : ℕ) : ℕ → ℕ
  | 0 => (List.replicate C true).length+1+2
  | j+1 => states C j+7
noncomputable def stage (D C : ℕ) : (j : ℕ) → j ≤ D → Machine (tapes D) (states C j)
  | 0,_ => printProgram D C
  | j+1,hj => Composition.machine (stage D C j (by omega)) (productProgram D ⟨j,by omega⟩)
def cost (C n : ℕ) : ℕ → ℕ
  | 0 => 2*C+2
  | j+1 => cost C n j+1+WilliamsUnaryProduct.budget (C*n^j) n

theorem print_run (D C n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (printProgram D C) (cost C n 0) (input D n) out ∧
      Fields D C n 0 (by omega) out := by
  obtain ⟨base,hb,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (List.replicate C true)
  have hbase : ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate C true))
      (2*C+2) (fun _ => []) ![List.replicate C true,List.replicate C false] := by
    simpa only [List.length_replicate] using
      (show ClockJoin.ReadyRun _ _ _ _ from ⟨base,hb,ht,hh,hs.le⟩)
  have h := hbase.focus (printSlots D) (print_injective D) (input D n)
    (by intro i; fin_cases i <;> simp [input,printSlots])
  refine ⟨_,h,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by intro i; fin_cases i <;> simp [printSlots])]
    rfl
  · change install (printSlots D) (input D n) _ (printSlots D 0)=_
    rw [install_slot _ (print_injective D)]
    simp
  · intro i hi
    rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg Fin.val he
      fin_cases j <;> simp [printSlots] at hv <;> omega)]
    simp [input,show i.val≠0 by omega]

theorem product_run (D C n j : ℕ) (hj : j<D) (ambient : Fin (tapes D) → List Bool)
    (hin : Fields D C n j hj.le ambient) : ∃ out,
    ClockJoin.ReadyRun (productProgram D ⟨j,hj⟩) (WilliamsUnaryProduct.budget (C*n^j) n) ambient out ∧
      Fields D C n (j+1) (by omega) out := by
  let f := slot D ⟨j,hj⟩
  have hi := slot_injective D ⟨j,hj⟩
  have h := (show ClockJoin.ReadyRun _ _ _ _ from
    let ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready (C*n^j) n
    ⟨r,hr,ht,hh,hs.le⟩).focus f hi ambient (by
      intro i; fin_cases i
      · exact hin.2.1
      · exact hin.1
      · exact hin.2.2 _ (by simp [f,slot,valueSlot]; omega)
      · exact hin.2.2 _ (by simp [f,slot,valueSlot]))
  refine ⟨_,h,?_,?_,?_⟩
  · change install f ambient _ (f 1)=_
    rw [install_slot _ hi]
    rfl
  · change install f ambient _ (f 2)=_
    rw [install_slot _ hi]
    change List.replicate ((C*n^j)*n) true=List.replicate (C*n^(j+1)) true
    rw [pow_succ,Nat.mul_assoc]
  · intro i hfuture
    have hnone : ∀ l,f l≠i := by
      intro l he
      have hv := congrArg Fin.val he
      fin_cases l <;> simp [f,slot,valueSlot] at hv <;> omega
    rw [install_other _ _ _ _ hnone]
    exact hin.2.2 i (by omega)

theorem stage_run (D C n j : ℕ) (hj : j ≤ D) : ∃ out,
    ClockJoin.ReadyRun (stage D C j hj) (cost C n j) (input D n) out ∧
      Fields D C n j hj out := by
  induction j with
  | zero => exact print_run D C n
  | succ j ih =>
    obtain ⟨middle,hm,hfields⟩ := ih (by omega)
    obtain ⟨out,ho,hout⟩ := product_run D C n j (by omega) middle hfields
    exact ⟨out,ClockJoin.join _ _ _ _ _ _ _ hm ho,hout⟩

noncomputable def machine (D C : ℕ) := stage D C D le_rfl
theorem power_run (D C n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D C) (cost C n D) (input D n) out ∧
      out ⟨0,by simp [tapes]⟩=UnaryTemplate.tape n ∧
      out (valueSlot D D le_rfl)=List.replicate (C*n^D) true := by
  obtain ⟨out,hr,ht,hv,_⟩ := stage_run D C n D le_rfl
  exact ⟨out,hr,ht,hv⟩

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionPower
