import Proof.CaseAnalysis.WitnessMassWidth

/-! Produce the exact reusable scalar bank dimensions from the paid common
width. One successor template serves both fixed polynomial evaluations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassDimensions
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3→Fin 15:=![0,1,2]
def wideSlots : Fin 5→Fin 15:=![1,4,5,6,7]
def capacitySlots : Fin 7→Fin 15:=![1,9,10,11,12,13,14]
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def wide:=RecoveryFocus.machine wideSlots (DimensionPower.machine 1 2)
def capacity:=RecoveryFocus.machine capacitySlots (DimensionPower.machine 2 4096)
def first:=Composition.machine template wide
def machine:=Composition.machine first capacity
def input (B : ℕ) (i : Fin 15):=if i=0 then List.replicate B true else []
def budget (B : ℕ):=(2*B+8)+1+DimensionPower.cost 2 (B+1) 1+1+
  DimensionPower.cost 4096 (B+1) 2

theorem dimensions_run (B : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget B) (input B) output ∧
      output 0=List.replicate B true ∧
      output 6=List.replicate (CompetitorRationalDecision.width B) true ∧
      output 13=List.replicate (CompetitorReusableDecision.capacity B) true:=by
  have ht:=(DimensionTemplate.ready true B).focus templateSlots (by decide) (input B)
    (by intro i;fin_cases i <;> rfl)
  let tb:=install templateSlots (input B) (DimensionTemplate.output true B)
  have t0:tb 0=List.replicate B true:=install_slot templateSlots (by decide) _ _ 0
  have tv:tb 1=UnaryTemplate.tape (B+1):=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide)];rfl
  have tfresh (i : Fin 15) (hi : 3 ≤ i.val) : tb i=[]:=by
    rw [show tb=install templateSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg (fun k : Fin 15=>k.val) h
      fin_cases j <;> simp [templateSlots] at hv <;> omega)]
    exact if_neg (by intro h;subst i;contradiction)
  obtain ⟨w,hw,wt,wv⟩:=DimensionPower.power_run 1 2 (B+1)
  have hwf:=hw.focus wideSlots (by decide) tb (by
    intro i;fin_cases i
    · exact tv
    all_goals exact tfresh _ (by decide))
  let wb:=install wideSlots tb w
  have wkeep (i : Fin 15) (hi : ∀ j,wideSlots j≠i) : wb i=tb i:=install_other _ _ _ _ hi
  have wtemplate:wb 1=UnaryTemplate.tape (B+1):=
    (install_slot wideSlots (by decide) _ w 0).trans wt
  obtain ⟨c,hc,_,cv⟩:=DimensionPower.power_run 2 4096 (B+1)
  have hcf:=hc.focus capacitySlots (by decide) wb (by
    intro i;fin_cases i
    · exact wtemplate
    all_goals rw [wkeep _ (by decide)];exact tfresh _ (by decide))
  refine ⟨_,ClockJoin.join first capacity _ _ _ _ _
    (ClockJoin.join template wide _ _ _ _ _ ht hwf) hcf,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),wkeep _ (by decide)]
    exact t0
  · rw [install_other _ _ _ _ (by decide)]
    change install wideSlots _ _ (wideSlots (DimensionPower.valueSlot 1 1 le_rfl))=_
    rw [install_slot _ (by decide),wv,pow_one]
    congr 1
  · exact (install_slot capacitySlots (by decide) _ c (DimensionPower.valueSlot 2 2 le_rfl)).trans cv

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassDimensions
