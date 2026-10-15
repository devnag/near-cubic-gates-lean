import Proof.CaseAnalysis.WitnessModeDimensions
import Proof.PCP.ProjectionDimensionTemplate
import Proof.MachineModel.OrdinaryMatrixBucketDivide

/-! The exact mode quotient uses the paid short numerator and logarithm.
Both original fields survive; divisor construction and division are ordinary
workers with all copying, polynomial evaluation and rewinds charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDivide
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (e : ℕ):=13+2*e
def copySlots (e : ℕ) : Fin 3→Fin (tapes e):=![⟨1,by dsimp [tapes];omega⟩,
  ⟨2,by dsimp [tapes];omega⟩,⟨3,by dsimp [tapes];omega⟩]
def templateSlots (e : ℕ) : Fin 3→Fin (tapes e):=![⟨2,by dsimp [tapes];omega⟩,
  ⟨4,by dsimp [tapes];omega⟩,⟨5,by dsimp [tapes];omega⟩]
def powerSlots (e : ℕ) (i : Fin (DimensionPower.tapes e)) : Fin (tapes e):=
  ⟨if i.val=0 then 4 else 6+i.val,by
    have hi:=i.isLt;dsimp only [DimensionPower.tapes,tapes] at *;split_ifs <;> omega⟩
def denominatorSlot (e : ℕ) : Fin (tapes e):=⟨7+2*e,by dsimp [tapes];omega⟩
def divisorSlot (e : ℕ) : Fin (tapes e):=⟨9+2*e,by dsimp [tapes];omega⟩
def valueSlot (e : ℕ) : Fin (tapes e):=⟨11+2*e,by dsimp [tapes];omega⟩
def divisorSlots (e : ℕ) : Fin 3→Fin (tapes e):=![denominatorSlot e,divisorSlot e,
  ⟨10+2*e,by dsimp [tapes];omega⟩]
def divideSlots (e : ℕ) : Fin 4→Fin (tapes e):=![⟨0,by dsimp [tapes];omega⟩,
  divisorSlot e,valueSlot e,⟨12+2*e,by dsimp [tapes];omega⟩]
def copy (e : ℕ):=RecoveryFocus.machine (copySlots e) (UWalkUnary.machine false false)
def template (e : ℕ):=RecoveryFocus.machine (templateSlots e) (DimensionTemplate.machine false)
def power (e den : ℕ):=RecoveryFocus.machine (powerSlots e) (DimensionPower.machine e den)
def divisor (e : ℕ):=RecoveryFocus.machine (divisorSlots e) (DimensionTemplate.machine false)
def divide (e : ℕ):=RecoveryFocus.machine (divideSlots e) MatrixBucketDivide.machine
def first (e : ℕ):=Composition.machine (copy e) (template e)
def second (e den : ℕ):=Composition.machine (first e) (power e den)
def third (e den : ℕ):=Composition.machine (second e den) (divisor e)
def machine (e den : ℕ):=Composition.machine (third e den) (divide e)
def input (e n L : ℕ) (i : Fin (tapes e)):=
  if i.val=0 then List.replicate n true else if i.val=1 then CompareMachine.word L else []
def budget (e den n L : ℕ):=(2*L+6)+1+(2*L+8)+1+DimensionPower.cost den L e+1+
  (2*(den*L^e)+8)+1+(8*n+6)

theorem copy_injective (e : ℕ) : Function.Injective (copySlots e):=by
  intro i j h;have hv:=congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [copySlots] at hv ⊢
theorem template_injective (e : ℕ) : Function.Injective (templateSlots e):=by
  intro i j h;have hv:=congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [templateSlots] at hv ⊢
theorem power_injective (e : ℕ) : Function.Injective (powerSlots e):=by
  intro i j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem divisor_injective (e : ℕ) : Function.Injective (divisorSlots e):=by
  intro i j h;have hv:=congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [divisorSlots,denominatorSlot,divisorSlot] at hv ⊢
theorem divide_injective (e : ℕ) : Function.Injective (divideSlots e):=by
  intro i j h;have hv:=congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [divideSlots,divisorSlot,valueSlot] at hv ⊢ <;> omega
theorem copy_outside (e : ℕ) (i : Fin (tapes e)) (hi : i.val=0 ∨ 4 ≤ i.val) :
    ∀ j,copySlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  fin_cases j <;> simp [copySlots] at hv <;> omega
theorem template_outside (e : ℕ) (i : Fin (tapes e)) (hi : i.val<2 ∨ 6 ≤ i.val) :
    ∀ j,templateSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  fin_cases j <;> simp [templateSlots] at hv <;> omega
theorem power_outside (e : ℕ) (i : Fin (tapes e))
    (hi : i.val<4 ∨ 9+2*e ≤ i.val) : ∀ j,powerSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  have hj:=j.isLt;dsimp only [DimensionPower.tapes] at hj
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> omega
theorem divisor_outside (e : ℕ) (i : Fin (tapes e))
    (hi : i.val<7+2*e ∨ 11+2*e ≤ i.val) : ∀ j,divisorSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  fin_cases j <;> simp [divisorSlots,denominatorSlot,divisorSlot] at hv <;> omega

theorem divide_run (e den n L : ℕ) (hd : 0<den) (hL : 0<L) : ∃ output,
    ClockJoin.ReadyRun (machine e den) (budget e den n L) (input e n L) output ∧
      output ⟨0,by dsimp [tapes];omega⟩=List.replicate n true ∧
      output ⟨1,by dsimp [tapes];omega⟩=CompareMachine.word L ∧
      output (divisorSlot e)=UnaryTemplate.tape (den*L^e) ∧
      output (valueSlot e)=List.replicate (n/(den*L^e)) true:=by
  have hc:=(UWalkUnary.ready false false 0 L).focus (copySlots e) (copy_injective e)
    (input e n L) (by
      intro i;fin_cases i
      · simp only [copySlots,input,UWalkUnary.input,
          UWalkUnary.source,ZeroPadding.pad_zero];rfl
      all_goals rfl)
  let c:=install (copySlots e) (input e n L) (UWalkUnary.result false false 0 L)
  have cval : c (copySlots e 1)=List.replicate L true:=by
    rw [show c=install (copySlots e) _ _ by rfl,install_slot _ (copy_injective e)];rfl
  have ckeep (i : Fin (tapes e)) (hi : i.val=0 ∨ 4 ≤ i.val) : c i=input e n L i:=
    install_other _ _ _ _ (copy_outside e i hi)
  have ht:=(DimensionTemplate.ready false L).focus (templateSlots e) (template_injective e)
    c (by
      intro i;fin_cases i
      · exact cval
      all_goals rw [ckeep _ (Or.inr (by dsimp [templateSlots];omega))];rfl)
  let t:=install (templateSlots e) c (DimensionTemplate.output false L)
  have tval : t (templateSlots e 1)=UnaryTemplate.tape L:=by
    rw [show t=install (templateSlots e) _ _ by rfl,install_slot _ (template_injective e)];rfl
  have tkeep (i : Fin (tapes e)) (hi : i.val<2 ∨ 6 ≤ i.val) : t i=c i:=
    install_other _ _ _ _ (template_outside e i hi)
  have tblank (i : Fin (tapes e)) (hi : 6 ≤ i.val) : t i=[]:=by
    rw [tkeep i (Or.inr hi),ckeep i (Or.inr (by omega))]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠1 by omega)]
  obtain ⟨p,hp,_,pv⟩:=DimensionPower.power_run e den L
  have hpf:=hp.focus (powerSlots e) (power_injective e) t (by
    intro i
    by_cases h0:i.val=0
    · have he:i=⟨0,by dsimp [DimensionPower.tapes];omega⟩:=Fin.ext h0
      rw [he];exact tval
    rw [DimensionPower.input,if_neg h0]
    exact tblank _ (by simp only [powerSlots,if_neg h0];omega))
  let pbank:=install (powerSlots e) t p
  have pval : pbank (denominatorSlot e)=List.replicate (den*L^e) true:=by
    have he:denominatorSlot e=powerSlots e (DimensionPower.valueSlot e e le_rfl):=by
      apply Fin.ext
      simp [denominatorSlot,powerSlots,DimensionPower.valueSlot]
      omega
    rw [he]
    change install (powerSlots e) t p (powerSlots e (DimensionPower.valueSlot e e le_rfl))=_
    rw [install_slot _ (power_injective e)];exact pv
  have pkeep (i : Fin (tapes e)) (hi : i.val<4 ∨ 9+2*e ≤ i.val) : pbank i=t i:=
    install_other _ _ _ _ (power_outside e i hi)
  have pblank (i : Fin (tapes e)) (hi : 9+2*e ≤ i.val) : pbank i=[]:=by
    rw [pkeep i (Or.inr hi)];exact tblank i (by omega)
  have hdt:=(DimensionTemplate.ready false (den*L^e)).focus (divisorSlots e)
    (divisor_injective e) pbank (by
      intro i;fin_cases i
      · exact pval
      all_goals exact pblank _ (by dsimp [divisorSlots,divisorSlot];omega))
  let dbank:=install (divisorSlots e) pbank (DimensionTemplate.output false (den*L^e))
  have dval : dbank (divisorSlot e)=UnaryTemplate.tape (den*L^e):=by
    change install (divisorSlots e) pbank _ (divisorSlots e 1)=_
    rw [install_slot _ (divisor_injective e)];rfl
  have dkeep (i : Fin (tapes e)) (hi : i.val<7+2*e ∨ 11+2*e ≤ i.val) : dbank i=pbank i:=
    install_other _ _ _ _ (divisor_outside e i hi)
  have keep (i : Fin (tapes e)) (hi : i.val<2) : dbank i=input e n L i:=by
    rw [dkeep i (Or.inl (by omega)),pkeep i (Or.inl (by omega)),tkeep i (Or.inl hi)]
    by_cases h0:i.val=0
    · exact ckeep i (Or.inl h0)
    have he:i=copySlots e 0:=Fin.ext (by simp only [copySlots,Matrix.cons_val_zero];omega)
    rw [he,show c=install (copySlots e) _ _ by rfl,install_slot _ (copy_injective e)]
    simp only [UWalkUnary.result,Matrix.cons_val_zero,UWalkUnary.source,ZeroPadding.pad_zero]
    rfl
  obtain ⟨d,hdRun,d0,d1,d2,dh,ds⟩:=MatrixBucketDivide.divide_run n (den*L^e)
    (Nat.mul_pos hd (pow_pos hL e))
  have hr:ClockJoin.ReadyRun MatrixBucketDivide.machine (8*n+6)
      (MatrixBucketDivide.resetInput n (den*L^e)) d.final.tapes:=⟨d,hdRun,rfl,dh,ds⟩
  have hdf:=hr.focus (divideSlots e) (divide_injective e) dbank (by
    intro i;fin_cases i
    · exact keep _ (by dsimp [divideSlots];omega)
    · exact dval
    all_goals
      rw [dkeep _ (Or.inr (by dsimp [divideSlots,valueSlot];omega))]
      exact pblank _ (by dsimp [divideSlots,valueSlot];omega))
  have hall:=ClockJoin.join (third e den) (divide e) _ _ _ _ _
    (ClockJoin.join (second e den) (divisor e) _ _ _ _ _
      (ClockJoin.join (first e) (power e den) _ _ _ _ _
        (ClockJoin.join (copy e) (template e) _ _ _ _ _ hc ht) hpf) hdt) hdf
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · change install (divideSlots e) dbank _ (divideSlots e 0)=_
    rw [install_slot _ (divide_injective e)];exact d0
  · rw [install_other _ _ _ _ (by
      intro i h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
      fin_cases i <;> simp [divideSlots,divisorSlot,valueSlot] at hv <;> omega)]
    exact keep _ (by simp)
  · change install (divideSlots e) dbank _ (divideSlots e 1)=_
    rw [install_slot _ (divide_injective e)];exact d1
  · change install (divideSlots e) dbank _ (divideSlots e 2)=_
    rw [install_slot _ (divide_injective e)];exact d2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDivide
