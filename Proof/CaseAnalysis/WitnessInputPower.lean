import Proof.CaseAnalysis.WitnessNodeBankPrepare
import Proof.PCP.ProjectionDimensionPowerBounds
import Proof.PCP.ProjectionDimensionTemplate

/-! A cold framed input produces a literal polynomial capacity driver.
The fixed degree, coefficient and offset are program parameters, shared by
the oracle-node and signed-integer banks. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.InputPower
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ):=10+(2+DimensionPower.tapes D)
def allocationSlots (D : ℕ) (i : Fin 10) : Fin (tapes D):=i.castAdd (2+DimensionPower.tapes D)
def templateSlots (D : ℕ) : Fin 3→Fin (tapes D):=
  ![⟨8,by simp [tapes,DimensionPower.tapes];omega⟩,
    ⟨10,by simp [tapes,DimensionPower.tapes]⟩,
    ⟨11,by simp [tapes,DimensionPower.tapes];omega⟩]
def powerSlots (D : ℕ) (i : Fin (DimensionPower.tapes D)) : Fin (tapes D):=
  if i.val=0 then ⟨10,by simp [tapes,DimensionPower.tapes]⟩ else ⟨11+i.val,by simp [tapes];omega⟩
theorem allocation_injective (D : ℕ) : Function.Injective (allocationSlots D):=by
  intro a b h
  have hv:=congrArg (fun i : Fin (tapes D)=>i.val) h
  exact Fin.ext hv
theorem template_injective (D : ℕ) : Function.Injective (templateSlots D):=by
  intro a b h
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [templateSlots] at hv ⊢
theorem power_val (D : ℕ) (i : Fin (DimensionPower.tapes D)) :
    (powerSlots D i).val=if i.val=0 then 10 else 11+i.val:=by
  unfold powerSlots
  split_ifs <;> rfl
theorem power_injective (D : ℕ) : Function.Injective (powerSlots D):=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [power_val,power_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem power_outside (D : ℕ) (i : Fin (tapes D)) (hi : i.val<10) : ∀ j,powerSlots D j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [power_val] at hv
  split_ifs at hv <;> omega

def input (D : ℕ) (bits : List Bool) : Fin (tapes D)→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (10+(2+DimensionPower.tapes D))=>List Bool)
    (HierarchyAllocation.input bits) (fun _=>[])
def allocated (D offset : ℕ) (bits : List Bool) : Fin (tapes D)→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (10+(2+DimensionPower.tapes D))=>List Bool)
    (HierarchyAllocation.output 1 offset bits) (fun _=>[])
noncomputable def templated (D offset : ℕ) (bits : List Bool):=
  install (templateSlots D) (allocated D offset bits) (DimensionTemplate.output false (bits.length+offset))
noncomputable def allocation (D offset : ℕ):=
  RecoveryFocus.machine (allocationSlots D) (HierarchyAllocation.machine 1 offset)
noncomputable def template (D : ℕ):=RecoveryFocus.machine (templateSlots D) (DimensionTemplate.machine false)
noncomputable def power (D C : ℕ):=RecoveryFocus.machine (powerSlots D) (DimensionPower.machine D C)
noncomputable def first (D offset : ℕ):=Composition.machine (allocation D offset) (template D)
noncomputable def machine (D C offset : ℕ):=Composition.machine (first D offset) (power D C)
def budget (D C offset : ℕ) (bits : List Bool):=
  HierarchyAllocation.budget 1 offset bits+1+(2*(bits.length+offset)+8)+1+
    DimensionPower.cost C (bits.length+offset) D

theorem allocated_fresh (D offset : ℕ) (bits : List Bool) (i : Fin (tapes D)) (hi : 10 ≤ i.val) :
    allocated D offset bits i=[]:=by
  simp [allocated,Fin.addCases,show ¬i.val<10 by omega]
theorem allocation_ready (D offset : ℕ) (bits : List Bool) :
    ClockJoin.ReadyRun (allocation D offset) (HierarchyAllocation.budget 1 offset bits)
      (input D bits) (allocated D offset bits):=by
  have h:=(HierarchyAllocation.allocation_ready 1 offset bits).focus
    (allocationSlots D) (allocation_injective D) (input D bits)
    (by intro i;simp only [input,allocationSlots,Fin.addCases_left])
  have he:install (allocationSlots D) (input D bits) (HierarchyAllocation.output 1 offset bits)=
      allocated D offset bits:=by
    apply HierarchyAllocation.install_eq _ (allocation_injective D)
    · intro i
      simp only [allocated,allocationSlots,Fin.addCases_left]
    · intro i hi
      refine Fin.addCases (m:=10) (n:=2+DimensionPower.tapes D)
        (motive:=fun j=>(∀ k,allocationSlots D k≠j) → allocated D offset bits j=input D bits j) ?_ ?_ i hi
      · intro j hj
        exact False.elim (hj j rfl)
      · intro j _
        simp only [allocated,input,Fin.addCases_right]
  rw [he] at h
  exact h

theorem template_ready (D offset : ℕ) (bits : List Bool) :
    ClockJoin.ReadyRun (template D) (2*(bits.length+offset)+8)
      (allocated D offset bits) (templated D offset bits):=by
  apply (DimensionTemplate.ready false (bits.length+offset)).focus
    (templateSlots D) (template_injective D) (allocated D offset bits)
  intro i
  fin_cases i
  · change allocated D offset bits (allocationSlots D 8)=_
    simp [allocated,allocationSlots,HierarchyAllocation.output,DimensionTemplate.input]
  · exact allocated_fresh D offset bits _ (by simp [templateSlots])
  · exact allocated_fresh D offset bits _ (by simp [templateSlots])

theorem power_input (D offset : ℕ) (bits : List Bool) :
    ∀ i,templated D offset bits (powerSlots D i)=DimensionPower.input D (bits.length+offset) i:=by
  intro i
  by_cases hi:i.val=0
  · have he:powerSlots D i=templateSlots D 1:=by apply Fin.ext;rw [power_val,if_pos hi];rfl
    rw [he,templated,install_slot _ (template_injective D)]
    simp only [DimensionTemplate.output,DimensionPower.input,hi,if_true,Bool.toNat_false,Nat.add_zero]
    rfl
  · have hv:(powerSlots D i).val=11+i.val:=by rw [power_val,if_neg hi]
    rw [templated,install_other _ _ _ _ (by
      intro j h
      have he:=congrArg Fin.val h
      rw [hv] at he
      fin_cases j <;> simp [templateSlots] at he <;> omega),
      allocated_fresh _ _ _ _ (by omega)]
    simp only [DimensionPower.input,if_neg hi]

theorem input_power (D C offset : ℕ) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine D C offset) (budget D C offset bits) (input D bits) out ∧
      out (powerSlots D (DimensionPower.valueSlot D D le_rfl))=List.replicate (C*(bits.length+offset)^D) true ∧
      out (powerSlots D ⟨0,by simp [DimensionPower.tapes]⟩)=UnaryTemplate.tape (bits.length+offset) ∧
      out (allocationSlots D 8)=List.replicate (bits.length+offset) true:=by
  obtain ⟨p,hp,ht,hv⟩:=DimensionPower.power_run D C (bits.length+offset)
  have h0:=ClockJoin.join (allocation D offset) (template D) _ _ _ _ _
    (allocation_ready D offset bits) (template_ready D offset bits)
  have h1:=hp.focus (powerSlots D) (power_injective D) (templated D offset bits) (power_input D offset bits)
  have h:=ClockJoin.join (first D offset) (power D C) _ _ _ _ _ h0 h1
  refine ⟨_,h,?_,?_,?_⟩
  · rw [install_slot _ (power_injective D)]
    exact hv
  · rw [install_slot _ (power_injective D)]
    exact ht
  · rw [install_other _ _ _ _ (power_outside D _ (by simp [allocationSlots]))]
    have he:allocationSlots D 8=templateSlots D 0:=by apply Fin.ext;rfl
    rw [he,templated,install_slot _ (template_injective D)]
    rfl

theorem budget_bound (D C offset : ℕ) (bits : List Bool) :
    budget D C offset bits≤12*bits.length+6*offset+2*C+45+
      D*(6*C*(bits.length+offset+1)^(D+1)+7):=by
  have h:=DimensionPower.cost_bound D C (bits.length+offset) D le_rfl
  unfold budget HierarchyAllocation.budget HierarchyAllocation.productCost HierarchyAllocation.offset
  simp only [one_mul]
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.InputPower
