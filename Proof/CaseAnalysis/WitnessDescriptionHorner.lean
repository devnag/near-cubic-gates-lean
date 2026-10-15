import Proof.CaseAnalysis.WitnessTermCeil

/-! The two fixed Horner stages used by the exact normalized-gate
description cap. A retained actual multiplier template is reused; the
constant is printed and every arithmetic pass is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionHorner
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def productSlots : Fin 4→Fin 8:=![0,1,2,3]
def constantSlots : Fin 2→Fin 8:=![4,5]
def sumSlots : Fin 4→Fin 8:=![2,4,6,7]
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def constant (k : ℕ):=RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate k true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def first (k : ℕ):=Composition.machine product (constant k)
def machine (k : ℕ):=Composition.machine (first k) sum
def input (x n : ℕ) (i : Fin 8):=
  if i=0 then List.replicate x true else if i=1 then UnaryTemplate.tape n else []
def budget (k x n : ℕ):=WilliamsUnaryProduct.budget x n+1+(2*k+2)+1+(2*(x*n+k)+6)

theorem horner_run (k x n : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine k) (budget k x n) (input x n) output ∧
      output 0=List.replicate x true ∧ output 1=UnaryTemplate.tape n ∧
      output 6=List.replicate (x*n+k) true:=by
  have hp:ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget x n)
      (WilliamsUnaryProduct.input x n) (WilliamsUnaryProduct.output x n):=by
    obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready x n
    exact ⟨p,hp,pt,ph,ps.le⟩
  have hpf:=hp.focus productSlots (by decide) (input x n) (by intro i;fin_cases i <;> rfl)
  let pbank:=install productSlots (input x n) (WilliamsUnaryProduct.output x n)
  have pfresh (i : Fin 8) (hi : 4 ≤ i.val) : pbank i=[]:=by
    rw [show pbank=install productSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [productSlots] at hv <;> omega)]
    simp only [input,if_neg (show i≠0 by intro he;rw [he] at hi;contradiction),
      if_neg (show i≠1 by intro he;rw [he] at hi;contradiction)]
  have hc:=(UWalkNumbers.fixed_ready (List.replicate k true)).focus constantSlots (by decide)
    pbank (by intro i;fin_cases i <;> exact pfresh _ (by decide))
  simp only [List.length_replicate] at hc
  let cb:=install constantSlots pbank ![List.replicate k true,List.replicate k false]
  have ckeep (i : Fin 8) (hi : i.val<4 ∨ 6 ≤ i.val) : cb i=pbank i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [constantSlots] at hv <;> omega)
  have hs:=(ClockUnarySum.sum_ready (x*n) k).focus sumSlots (by decide) cb (by
    intro i;fin_cases i
    · rw [ckeep _ (Or.inl (by decide))]
      change install productSlots _ _ (productSlots 2)=_
      rw [install_slot _ (by decide : Function.Injective productSlots)];rfl
    · change install constantSlots _ _ (constantSlots 0)=_
      rw [install_slot _ (by decide : Function.Injective constantSlots)];rfl
    all_goals rw [ckeep _ (Or.inr (by decide))];exact pfresh _ (by decide))
  have hall:=ClockJoin.join (first k) sum _ _ _ _ _
    (ClockJoin.join product (constant k) _ _ _ _ _ hpf hc) hs
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),ckeep _ (Or.inl (by decide))]
    change install productSlots _ _ (productSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective productSlots)];rfl
  · rw [install_other _ _ _ _ (by decide),ckeep _ (Or.inl (by decide))]
    change install productSlots _ _ (productSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective productSlots)];rfl
  · change install sumSlots _ _ (sumSlots 2)=_
    rw [install_slot _ (by decide : Function.Injective sumSlots)];rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionHorner
