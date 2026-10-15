import Proof.CaseAnalysis.WitnessLegalTemplateCall

/-! The retained input-length counter physically produces both capacities.
The existing polynomial, successor-template and copy workers are paid once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev A (E : ℕ):=DimensionPolynomial.tapes E
def tapes (E : ℕ):=A E+8
def powerSlots (E : ℕ) (i : Fin (A E)) : Fin (tapes E):=i.castAdd 8
def pSlot (E : ℕ):=powerSlots E (DimensionPolynomial.rawSlot E)
def templateSlots (E : ℕ) (i : Fin 3) : Fin (tapes E):=
  if i.val=0 then pSlot E else ⟨A E+i.val,by dsimp only [tapes];omega⟩
def copySlots (E : ℕ) (i : Fin 5) : Fin (tapes E):=
  if i.val=0 then ⟨A E+1,by dsimp only [tapes];omega⟩ else ⟨A E+3+i.val,by dsimp only [tapes];omega⟩
def hSlot (E : ℕ):=copySlots E 1
def input (E N : ℕ) (i : Fin (tapes E)):=if i.val=0 then List.replicate N true else []
def power (E K : ℕ):=RecoveryFocus.machine (powerSlots E) (DimensionPolynomial.machine E K)
def template (E : ℕ):=RecoveryFocus.machine (templateSlots E) (DimensionTemplate.machine true)
def copy (E : ℕ):=RecoveryFocus.machine (copySlots E) MatrixTemplateCopy.resetMachine
def first (E K : ℕ):=Composition.machine (power E K) (template E)
def machine (E K : ℕ):=Composition.machine (first E K) (copy E)
def value (E K N : ℕ):=DimensionPolynomial.value E K N
def budget (E K N : ℕ):=DimensionPolynomial.budget E K N+1+(2*value E K N+8)+1+(4*(value E K N+1)+12)

theorem power_injective (E : ℕ) : Function.Injective (powerSlots E):=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin (tapes E)=>k.val) h)
theorem p_val (E : ℕ) : (pSlot E).val=5+2*E:=by
  simp only [pSlot,powerSlots,Fin.val_castAdd,DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots]
  change 4+2*E+1=5+2*E
  omega
theorem template_val (E : ℕ) (i : Fin 3) :
    (templateSlots E i).val=(if i.val=0 then 5+2*E else A E+i.val):=by
  unfold templateSlots
  split_ifs
  · exact p_val E
  · rfl
theorem copy_val (E : ℕ) (i : Fin 5) :
    (copySlots E i).val=(if i.val=0 then A E+1 else A E+3+i.val):=by
  unfold copySlots
  split_ifs <;> rfl
theorem template_injective (E : ℕ) : Function.Injective (templateSlots E):=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [template_val,template_val] at hv
  have he:A E=14+2*E:=rfl
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem copy_injective (E : ℕ) : Function.Injective (copySlots E):=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [copy_val,copy_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
private theorem power_outside (E : ℕ) (i : Fin (tapes E)) (hi : A E ≤ i.val) : ∀ j,powerSlots E j≠i:=by
  intro j h;have hv:=congrArg Fin.val h;change j.val=i.val at hv;omega
private theorem template_outside (E : ℕ) (i : Fin (tapes E))
    (hi : i.val≠5+2*E ∧ (i.val<A E+1 ∨ A E+3 ≤ i.val)) : ∀ j,templateSlots E j≠i:=by
  intro j h;have hv:=congrArg Fin.val h
  rw [template_val] at hv
  split_ifs at hv <;> rcases hi.2 with hl|hr <;> omega
private theorem copy_outside (E : ℕ) (i : Fin (tapes E)) (hi : i.val<A E+1) : ∀ j,copySlots E j≠i:=by
  intro j h;have hv:=congrArg Fin.val h
  rw [copy_val] at hv
  split_ifs at hv <;> omega

theorem capacity_run (E K N : ℕ) (hK : 0<K) : ∃ output,
    ClockJoin.ReadyRun (machine E K) (budget E K N) (input E N) output ∧
      output ⟨0,by dsimp [tapes,A,DimensionPolynomial.tapes];omega⟩=List.replicate N true ∧
      output (pSlot E)=List.replicate (value E K N) true ∧
      output (hSlot E)=List.replicate (value E K N+1) true:=by
  obtain ⟨po,hp,pn,pv,_,_⟩:=DimensionPolynomial.polynomial_run E K N hK
  have hpf:=hp.focus (powerSlots E) (power_injective E) (input E N) (by intro i;rfl)
  let P:=install (powerSlots E) (input E N) po
  have pf (i : Fin (A E)):P (powerSlots E i)=po i:=install_slot _ (power_injective E) _ _ _
  have fresh (i : Fin (tapes E)) (hi : A E ≤ i.val):P i=[]:=by
    rw [show P=install _ _ _ by rfl,install_other _ _ _ _ (power_outside E i hi)]
    have ha:1 ≤ A E:=by dsimp [A,DimensionPolynomial.tapes];omega
    simp only [input,if_neg (show i.val≠0 by omega)]
  have ht:=(DimensionTemplate.ready true (value E K N)).focus (templateSlots E) (template_injective E) P (by
    intro i;fin_cases i
    · exact (pf _).trans pv
    all_goals exact fresh _ (by dsimp [templateSlots];omega))
  let T:=install (templateSlots E) P (DimensionTemplate.output true (value E K N))
  have tf (i : Fin 3):T (templateSlots E i)=DimensionTemplate.output true (value E K N) i:=
    install_slot _ (template_injective E) _ _ _
  obtain ⟨c,hc,c0,c1,_,_,ch,cs⟩:=MatrixTemplateCopy.reset_run (value E K N+1)
  have ready:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*(value E K N+1)+12)
      (MatrixTemplateCopy.resetInput (value E K N+1)) c.final.tapes:=⟨c,hc,rfl,ch,cs.le⟩
  have hcf:=ready.focus (copySlots E) (copy_injective E) T (by
    intro i
    fin_cases i
    · exact tf 1
    all_goals
      rw [show T=install _ _ _ by rfl,install_other _ _ _ _ (template_outside E _ (by
        dsimp [copySlots,A,DimensionPolynomial.tapes];omega))]
      exact fresh _ (by dsimp [copySlots];omega))
  let output:=install (copySlots E) T c.final.tapes
  have keep (i : Fin (tapes E)) (hi : i.val<A E+1):output i=T i:=
    install_other _ _ _ _ (copy_outside E i hi)
  have all:=ClockJoin.join (first E K) (copy E) _ _ _ _ _
    (ClockJoin.join (power E K) (template E) _ _ _ _ _ hpf ht) hcf
  refine ⟨output,all,?_,?_,?_⟩
  · rw [keep _ (by dsimp [A,DimensionPolynomial.tapes];omega),show T=install _ _ _ by rfl,
      install_other _ _ _ _ (template_outside E _ (by dsimp [A,DimensionPolynomial.tapes];omega))]
    exact (pf ⟨0,by dsimp [A,DimensionPolynomial.tapes];omega⟩).trans pn
  · rw [keep _ (by rw [p_val];dsimp [A,DimensionPolynomial.tapes];omega)]
    exact tf 0
  · exact (install_slot (copySlots E) (copy_injective E) T c.final.tapes 1).trans c1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity
