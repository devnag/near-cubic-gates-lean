import Proof.CaseAnalysis.WitnessTermCeil
import Proof.CaseAnalysis.CapacityPower

/-! The actual source clause exponent is expanded once and multiplied
by twice the exact XOR term ceiling. Here cb is source metadata; the
enclosing source bound pays 2^cb as a polynomial in the native width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermMultiply
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def clauseSlots (i : Fin 17) : Fin 27:=i.castAdd 10
def templateSlots : Fin 3→Fin 27:=![17,18,19]
def doubleSlots : Fin 5→Fin 27:=![18,21,22,23,24]
def productSlots : Fin 4→Fin 27:=![23,13,25,26]
def clauses:=RecoveryFocus.machine clauseSlots CloseoutCapacity.Power.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def double:=RecoveryFocus.machine doubleSlots (DimensionPower.machine 1 2)
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def first:=Composition.machine clauses template
def second:=Composition.machine first double
def machine:=Composition.machine second product
def input (cb J : ℕ) (i : Fin 27):=
  if i.val=0 then List.replicate cb true else if i.val=17 then List.replicate J true else []
def budget (cb J : ℕ):=CloseoutCapacity.Power.budget cb+1+(2*J+8)+1+
  DimensionPower.cost 2 J 1+1+WilliamsUnaryProduct.budget (2*J) (2^cb)

theorem clause_injective : Function.Injective clauseSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 27=>k.val) h)

theorem multiply_run (cb J : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget cb J) (input cb J) output ∧
      output 17=List.replicate J true ∧ output 13=UnaryTemplate.tape (2^cb) ∧
      output 25=List.replicate ((2*2^cb)*J) true:=by
  obtain ⟨c,hc,_,ct⟩:=CloseoutCapacity.Power.power_run cb
  have hcf:=hc.focus clauseSlots clause_injective (input cb J) (by
    intro i
    have hi:=i.isLt
    simp only [input,clauseSlots,Fin.val_castAdd,CloseoutCapacity.Power.input]
    split_ifs <;> first | rfl | omega)
  let cbk:=install clauseSlots (input cb J) c
  have cold (i : Fin 17) : cbk (clauseSlots i)=c i:=install_slot _ clause_injective _ _ _
  have cfresh (i : Fin 27) (hi : 17 ≤ i.val) : cbk i=input cb J i:=by
    apply install_other
    intro j h
    have hv:=congrArg (fun k : Fin 27=>k.val) h
    change j.val=i.val at hv
    omega
  have ht:=(DimensionTemplate.ready false J).focus templateSlots (by decide) cbk (by
    intro i;fin_cases i <;> exact cfresh _ (by decide))
  let tb:=install templateSlots cbk (DimensionTemplate.output false J)
  have tv:tb 18=UnaryTemplate.tape J:=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  have tkeep (i : Fin 27) (hi : i.val<17 ∨ 20 ≤ i.val) : tb i=cbk i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [templateSlots] at hv <;> omega)
  obtain ⟨d,hd,_,dv⟩:=DimensionPower.power_run 1 2 J
  have hdf:=hd.focus doubleSlots (by decide) tb (by
    intro i;fin_cases i
    · exact tv
    all_goals rw [tkeep _ (Or.inr (by decide))];exact cfresh _ (by decide))
  let db:=install doubleSlots tb d
  have dkeep (i : Fin 27) (hi : i.val<18 ∨ 25 ≤ i.val) : db i=tb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [doubleSlots] at hv <;> omega)
  have hpr:ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (2*J) (2^cb))
      (WilliamsUnaryProduct.input (2*J) (2^cb)) (WilliamsUnaryProduct.output (2*J) (2^cb)):=by
    obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready (2*J) (2^cb)
    exact ⟨p,hp,pt,ph,ps.le⟩
  have hpf:=hpr.focus productSlots (by decide) db (by
    intro i;fin_cases i
    · change install doubleSlots tb d (doubleSlots (DimensionPower.valueSlot 1 1 le_rfl))=_
      rw [install_slot _ (by decide : Function.Injective doubleSlots),dv,pow_one]
      rfl
    · rw [dkeep _ (Or.inl (by decide)),tkeep _ (Or.inl (by decide))]
      exact (cold 13).trans ct
    all_goals
      rw [dkeep _ (Or.inr (by decide)),tkeep _ (Or.inr (by decide))]
      exact cfresh _ (by decide))
  have hall:=ClockJoin.join second product _ _ _ _ _
    (ClockJoin.join first double _ _ _ _ _
      (ClockJoin.join clauses template _ _ _ _ _ hcf ht) hdf) hpf
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),dkeep _ (Or.inl (by decide))]
    change install templateSlots _ _ (templateSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  · change install productSlots _ _ (productSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective productSlots)];rfl
  · change install productSlots _ _ (productSlots 2)=_
    rw [install_slot _ (by decide : Function.Injective productSlots)]
    change List.replicate ((2*J)*2^cb) true=List.replicate ((2*2^cb)*J) true
    congr 1
    ring

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermMultiply
