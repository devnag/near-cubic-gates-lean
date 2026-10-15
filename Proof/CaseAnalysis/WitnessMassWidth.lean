import Proof.CaseAnalysis.WitnessMassTrace
import Proof.PCP.ProjectionDimensionTemplate
import Proof.MachineModel.UWalkArithmetic

/-! One paid policy product supplies the common accumulator width for all
sums. Both exact policy inputs remain available; no per-sum multiplication. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassWidth
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oneSlots : Fin 2→Fin 10:=![2,3]
def sumSlots : Fin 4→Fin 10:=![0,2,4,5]
def templateSlots : Fin 3→Fin 10:=![1,6,7]
def productSlots : Fin 4→Fin 10:=![4,6,8,9]
def one:=RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def first:=Composition.machine one sum
def second:=Composition.machine first template
def machine:=Composition.machine second product
def input (T b : ℕ) : Fin 10→List Bool:=
  ![List.replicate T true,List.replicate b true,[],[],[],[],[],[],[],[]]
def budget (T b : ℕ):=4+1+(2*(T+1)+6)+1+(2*b+8)+1+WilliamsUnaryProduct.budget (T+1) (b+1)

theorem width_run (T b : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget T b) (input T b) output ∧
      output 0=List.replicate T true ∧ output 1=List.replicate b true ∧
      output 8=List.replicate (CompetitorSumWidth.width T b) true:=by
  have ho:=(UWalkNumbers.fixed_ready [true]).focus oneSlots (by decide) (input T b)
    (by intro i;fin_cases i <;> rfl)
  let ob:=install oneSlots (input T b) ![[true],[false]]
  have oval:ob 2=[true]:=install_slot oneSlots (by decide) _ _ 0
  have okept (i : Fin 10) (hi : i≠2 ∧ i≠3) : ob i=input T b i:=by
    apply install_other
    intro j;fin_cases j
    · exact Ne.symm hi.1
    · exact Ne.symm hi.2
  have hs:=(ClockUnarySum.sum_ready T 1).focus sumSlots (by decide) ob (by
    intro i;fin_cases i
    · exact okept _ ⟨by decide,by decide⟩
    · exact oval
    all_goals exact okept _ ⟨by decide,by decide⟩)
  let sb:=install sumSlots ob ![List.replicate T true,[true],List.replicate (T+1) true,
    List.replicate (T+1+2) false]
  have sval:sb 4=List.replicate (T+1) true:=install_slot sumSlots (by decide) _ _ 2
  have skept (i : Fin 10) (hi : ∀ j,sumSlots j≠i) : sb i=ob i:=install_other _ _ _ _ hi
  have ht:=(DimensionTemplate.ready true b).focus templateSlots (by decide) sb (by
    intro i;fin_cases i
    all_goals rw [skept _ (by decide)];exact okept _ ⟨by decide,by decide⟩)
  let tb:=install templateSlots sb (DimensionTemplate.output true b)
  have tv:tb 6=UnaryTemplate.tape (b+1):=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide)];rfl
  have tkept (i : Fin 10) (hi : ∀ j,templateSlots j≠i) : tb i=sb i:=install_other _ _ _ _ hi
  obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready (T+1) (b+1)
  have hpr:ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (T+1) (b+1))
      (WilliamsUnaryProduct.input (T+1) (b+1)) (WilliamsUnaryProduct.output (T+1) (b+1)):=
    ⟨p,hp,pt,ph,ps.le⟩
  have hpf:=hpr.focus productSlots (by decide) tb (by
    intro i;fin_cases i
    · rw [tkept _ (by decide)];exact sval
    · exact tv
    all_goals rw [tkept _ (by decide),skept _ (by decide)];exact okept _ ⟨by decide,by decide⟩)
  refine ⟨_,ClockJoin.join second product _ _ _ _ _
    (ClockJoin.join first template _ _ _ _ _
      (ClockJoin.join one sum _ _ _ _ _ ho hs) ht) hpf,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),tkept _ (by decide)]
    exact install_slot sumSlots (by decide) _ _ 0
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot templateSlots (by decide) _ _ 0
  · exact install_slot productSlots (by decide) _ _ 2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassWidth
