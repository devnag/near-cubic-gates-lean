import Proof.CaseAnalysis.PolicyArithmetic
import Proof.PCP.ProjectionDimensionTemplate
import Proof.MachineModel.OrdinaryMatrixBucketDivide
import Proof.MachineModel.UWalkArithmetic

/-! Exact ceiling of the fixed rational XOR term multiplier, from the
actual raw q0 alone. The fixed offset and positive divisor are printed by
finite control; every product, sum, copy and quotient is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCeil
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
open CloseoutWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3→Fin 16:=![0,1,2]
def powerSlots : Fin 5→Fin 16:=![1,4,5,6,7]
def offsetSlots : Fin 2→Fin 16:=![8,9]
def sumSlots : Fin 4→Fin 16:=![6,8,10,11]
def divisorSlots : Fin 2→Fin 16:=![12,13]
def divideSlots : Fin 4→Fin 16:=![10,12,14,15]
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def power (A : ℕ):=RecoveryFocus.machine powerSlots (DimensionPower.machine 1 A)
def offset (B : ℕ):=RecoveryFocus.machine offsetSlots
  (HierarchyFixedWord.machine (List.replicate (B-1) true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def divisor (B : ℕ):=RecoveryFocus.machine divisorSlots (HierarchyFixedWord.machine (UnaryTemplate.tape B))
def divide:=RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
def first (A : ℕ):=Composition.machine template (power A)
def second (A B : ℕ):=Composition.machine (first A) (offset B)
def third (A B : ℕ):=Composition.machine (second A B) sum
def fourth (A B : ℕ):=Composition.machine (third A B) (divisor B)
def machine (A B : ℕ):=Composition.machine (fourth A B) divide
def input (n : ℕ) (i : Fin 16):=if i=0 then List.replicate n true else []
def numerator (A B n : ℕ):=A*n+(B-1)
def budget (A B n : ℕ):=(2*n+8)+1+DimensionPower.cost A n 1+1+(2*(B-1)+2)+1+
  (2*numerator A B n+6)+1+(2*(UnaryTemplate.tape B).length+2)+1+(8*numerator A B n+6)

theorem ceil_run (A B n : ℕ) (hB : 0<B) : ∃ output,
    ClockJoin.ReadyRun (machine A B) (budget A B n) (input n) output ∧
      output 0=List.replicate n true ∧ output 12=UnaryTemplate.tape B ∧
      output 14=List.replicate ((A*n+B-1)/B) true:=by
  have ht:=(DimensionTemplate.ready false n).focus templateSlots (by decide) (input n)
    (by intro i;fin_cases i <;> rfl)
  let t:=install templateSlots (input n) (DimensionTemplate.output false n)
  have tvalue:t 1=UnaryTemplate.tape n:=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  have tfresh (i : Fin 16) (hi : 3 ≤ i.val) : t i=[]:=by
    rw [show t=install templateSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [templateSlots] at hv <;> omega)]
    exact if_neg (by intro he;rw [he] at hi;contradiction)
  obtain ⟨p,hp,_,pv⟩:=DimensionPower.power_run 1 A n
  have hpf:=hp.focus powerSlots (by decide) t (by
    intro i;fin_cases i
    · exact tvalue
    all_goals exact tfresh _ (by decide))
  let pb:=install powerSlots t p
  have pvalue:pb 6=List.replicate (A*n) true:=by
    change install powerSlots _ _ (powerSlots (DimensionPower.valueSlot 1 1 le_rfl))=_
    rw [install_slot _ (by decide : Function.Injective powerSlots),pv,pow_one]
  have pfresh (i : Fin 16) (hi : 8 ≤ i.val) : pb i=[]:=by
    rw [show pb=install powerSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [powerSlots] at hv <;> omega)]
    exact tfresh i (by omega)
  have ho:=(UWalkNumbers.fixed_ready (List.replicate (B-1) true)).focus offsetSlots
    (by decide) pb (by intro i;fin_cases i <;> exact pfresh _ (by decide))
  simp only [List.length_replicate] at ho
  let ob:=install offsetSlots pb ![List.replicate (B-1) true,List.replicate (B-1) false]
  have ovalue:ob 8=List.replicate (B-1) true:=by
    change install offsetSlots _ _ (offsetSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective offsetSlots)]
    rfl
  have okeep (i : Fin 16) (hi : i.val<8 ∨ 10 ≤ i.val) : ob i=pb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [offsetSlots] at hv <;> omega)
  have hs:=(ClockUnarySum.sum_ready (A*n) (B-1)).focus sumSlots (by decide) ob (by
    intro i;fin_cases i
    · exact (okeep _ (Or.inl (by decide))).trans pvalue
    · exact ovalue
    all_goals rw [okeep _ (Or.inr (by decide))];exact pfresh _ (by decide))
  let sb:=install sumSlots ob ![List.replicate (A*n) true,List.replicate (B-1) true,
    List.replicate (numerator A B n) true,List.replicate (numerator A B n+2) false]
  have svalue:sb 10=List.replicate (numerator A B n) true:=by
    change install sumSlots _ _ (sumSlots 2)=_
    rw [install_slot _ (by decide : Function.Injective sumSlots)]
    rfl
  have sfresh (i : Fin 16) (hi : 12 ≤ i.val) : sb i=[]:=by
    rw [show sb=install sumSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [sumSlots] at hv <;> omega),okeep _ (Or.inr (by omega))]
    exact pfresh i (by omega)
  have hd:=(UWalkNumbers.fixed_ready (UnaryTemplate.tape B)).focus divisorSlots
    (by decide) sb (by intro i;fin_cases i <;> exact sfresh _ (by decide))
  let db:=install divisorSlots sb ![UnaryTemplate.tape B,List.replicate (UnaryTemplate.tape B).length false]
  have dvalue:db 12=UnaryTemplate.tape B:=by
    change install divisorSlots _ _ (divisorSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective divisorSlots)]
    rfl
  have dkeep (i : Fin 16) (hi : i.val<12 ∨ 14 ≤ i.val) : db i=sb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [divisorSlots] at hv <;> omega)
  obtain ⟨q,hq,q0,q1,q2,qh,qs⟩:=MatrixBucketDivide.divide_run (numerator A B n) B hB
  have hqr:ClockJoin.ReadyRun MatrixBucketDivide.machine (8*numerator A B n+6)
      (MatrixBucketDivide.resetInput (numerator A B n) B) q.final.tapes:=⟨q,hq,rfl,qh,qs⟩
  have hqf:=hqr.focus divideSlots (by decide) db (by
    intro i;fin_cases i
    · exact (dkeep _ (Or.inl (by decide))).trans svalue
    · exact dvalue
    all_goals rw [dkeep _ (Or.inr (by decide))];exact sfresh _ (by decide))
  have hall:=ClockJoin.join (fourth A B) divide _ _ _ _ _
    (ClockJoin.join (third A B) (divisor B) _ _ _ _ _
      (ClockJoin.join (second A B) sum _ _ _ _ _
        (ClockJoin.join (first A) (offset B) _ _ _ _ _
          (ClockJoin.join template (power A) _ _ _ _ _ ht hpf) ho) hs) hd) hqf
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),dkeep _ (Or.inl (by decide))]
    rw [show sb=install sumSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      okeep _ (Or.inl (by decide))]
    rw [show pb=install powerSlots _ _ by rfl,install_other _ _ _ _ (by decide)]
    change install templateSlots _ _ (templateSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  · change install divideSlots _ _ (divideSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective divideSlots)];exact q1
  · change install divideSlots _ _ (divideSlots 2)=_
    rw [install_slot _ (by decide : Function.Injective divideSlots),q2]
    have he:numerator A B n=A*n+B-1:=by unfold numerator;omega
    rw [he]

theorem policy_run (delta : ℚ) (copies n : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine (termNumerator delta copies) (termDenominator delta copies))
      (budget (termNumerator delta copies) (termDenominator delta copies) n) (input n) output ∧
      output 0=List.replicate n true ∧
      output 12=UnaryTemplate.tape (termDenominator delta copies) ∧
      output 14=List.replicate (RepairRepresentation.xorTermBound delta n copies) true:=by
  rw [naturalTermBound_exact]
  exact ceil_run _ _ _ (termDenominator_positive delta copies)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCeil
