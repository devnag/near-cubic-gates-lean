import Proof.PCP.PCPSerializerCapacityPower
import Proof.MachineModel.ClockJoin

/-! Produce the field width and common traversal capacity from the two
actual retained raw counters. Coefficients are fixed program parameters. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdScalars
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

local instance (D : ℕ) : NeZero (DimensionPolynomial.tapes D):=⟨by dsimp [DimensionPolynomial.tapes];omega⟩

def sumSlots : Fin 4→Fin 40:=![0,1,2,3]
def capSlots (j : Fin (DimensionPolynomial.tapes 4)) : Fin 40:=if j=0 then 2 else ⟨j.val+3,by have ht:=j.isLt;dsimp [DimensionPolynomial.tapes] at ht;omega⟩
def widthSlots (j : Fin (DimensionPolynomial.tapes 1)) : Fin 40:=if j=0 then 2 else ⟨j.val+24,by have ht:=j.isLt;dsimp [DimensionPolynomial.tapes] at ht;omega⟩
theorem cap_injective : Function.Injective capSlots:=by decide
theorem width_injective : Function.Injective widthSlots:=by decide
def input (R B : ℕ) (i : Fin 40):=if i=0 then List.replicate R true else if i=1 then List.replicate B true else []
noncomputable def sumProgram:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def capProgram (K : ℕ):=RecoveryFocus.machine capSlots (PCPSerializerCapacity.Power.machine 4 K)
noncomputable def widthProgram:=RecoveryFocus.machine widthSlots (PCPSerializerCapacity.Power.machine 1 1)
noncomputable def machine (K : ℕ):=Composition.machine (Composition.machine sumProgram (capProgram K)) widthProgram
def budget (K R B : ℕ):=2*(R+B)+6+1+PCPSerializerCapacity.Power.budget 4 K (R+B)+1+
  PCPSerializerCapacity.Power.budget 1 1 (R+B)

theorem sum_input (R B : ℕ) (j : Fin 4) :
    input R B (sumSlots j)= (![List.replicate R true,List.replicate B true,[],[]] : Fin 4→List Bool) j:=by
  fin_cases j <;> rfl
noncomputable def summed (R B : ℕ):=install sumSlots (input R B)
  (![List.replicate R true,List.replicate B true,List.replicate (R+B) true,List.replicate (R+B+2) false] : Fin 4→List Bool)
theorem cap_input (R B : ℕ) (j : Fin (DimensionPolynomial.tapes 4)) :
    summed R B (capSlots j)=DimensionPolynomial.input 4 (R+B) j:=by
  by_cases hz : j=0
  · subst j;exact install_slot sumSlots (by decide) _ _ 2
  have hn : ∀ i,sumSlots i≠capSlots j:=by
    intro i he
    have hj : j.val≠0:=fun h=>hz (Fin.ext h)
    have hcval : (capSlots j).val=j.val+3:=by rw [capSlots,if_neg hz]
    have his : (sumSlots i).val≤3:=by fin_cases i <;> decide
    have hv:=congrArg Fin.val he
    rw [hcval] at hv
    omega
  rw [summed,install_other _ _ _ _ hn]
  have hj : j.val≠0:=fun h=>hz (Fin.ext h)
  simp [input,capSlots,DimensionPolynomial.input,hz,hj,Fin.ext_iff]

theorem width_input (R B : ℕ) (out : Fin (DimensionPolynomial.tapes 4)→List Bool)
    (hs : out 0=List.replicate (R+B) true) (j : Fin (DimensionPolynomial.tapes 1)) :
    install capSlots (summed R B) out (widthSlots j)=DimensionPolynomial.input 1 (R+B) j:=by
  by_cases hz : j=0
  · subst j
    change install capSlots _ out (capSlots 0)=_
    rw [install_slot _ cap_injective,hs]
    rfl
  have hj : j.val≠0:=fun h=>hz (Fin.ext h)
  have hcap : ∀ i,capSlots i≠widthSlots j:=by
    intro i he
    have hi:=i.isLt
    have hv:=congrArg Fin.val he
    simp only [capSlots,widthSlots,hz,if_false] at hv
    dsimp [DimensionPolynomial.tapes] at hi
    split_ifs at hv <;> dsimp at hv <;> omega
  have hsum : ∀ i,sumSlots i≠widthSlots j:=by
    intro i he
    have hwval : (widthSlots j).val=j.val+24:=by rw [widthSlots,if_neg hz]
    have his : (sumSlots i).val≤3:=by fin_cases i <;> decide
    have hv:=congrArg Fin.val he
    rw [hwval] at hv
    omega
  rw [install_other _ _ _ _ hcap,summed,install_other _ _ _ _ hsum]
  simp [input,widthSlots,DimensionPolynomial.input,hz,hj,Fin.ext_iff]

theorem scalar_run (K R B : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine K) (budget K R B) (input R B) out ∧
      out 0=List.replicate R true ∧ out 1=List.replicate B true ∧
      out 14=List.replicate (K*(R+B+1)^4) true ∧ out 29=List.replicate (R+B+1) true:=by
  have sumReady:=(ClockUnarySum.sum_ready R B).focus sumSlots (by decide) (input R B) (sum_input R B)
  change ClockJoin.ReadyRun sumProgram _ (input R B) (summed R B) at sumReady
  obtain ⟨capOut,capReady,capSource,capValue⟩:=PCPSerializerCapacity.Power.capacity_run 4 K (R+B)
  have c:=capReady.focus capSlots cap_injective (summed R B) (cap_input R B)
  obtain ⟨widthOut,widthReady,_widthSource,widthValue⟩:=PCPSerializerCapacity.Power.capacity_run 1 1 (R+B)
  have w:=widthReady.focus widthSlots width_injective _ (width_input R B capOut capSource)
  have whole:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ sumReady c) w
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · rw [install_other widthSlots _ _ 0 (by decide),install_other capSlots _ _ 0 (by decide)]
    exact install_slot sumSlots (by decide) _ _ 0
  · rw [install_other widthSlots _ _ 1 (by decide),install_other capSlots _ _ 1 (by decide)]
    exact install_slot sumSlots (by decide) _ _ 1
  · rw [install_other widthSlots _ _ 14 (by decide)]
    change install capSlots _ capOut (capSlots (PCPSerializerCapacity.Power.outputSlot 4))=_
    rw [install_slot _ cap_injective]
    exact capValue
  · change install widthSlots _ widthOut (widthSlots (PCPSerializerCapacity.Power.outputSlot 1))=_
    rw [install_slot _ width_injective,widthValue]
    simp only [pow_one,Nat.one_mul]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdScalars
