import Proof.CaseAnalysis.RowsCircuitHalf

/-! Recover the symmetric circuit's exact description from the original
measured bottom counter and actual serialized count, using only paid native
sum and division calls. The retained policy cap stays outside this worker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricDescription
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sumSlots : Fin 4 → Fin 12 := ![0,1,2,3]
def literalSlots : Fin 2 → Fin 12 := ![4,5]
def addSlots : Fin 4 → Fin 12 := ![2,4,6,7]
def halfSlots : Fin 5 → Fin 12 := ![6,8,9,10,11]
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def literal:=RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine [true,true])
noncomputable def add:=RecoveryFocus.machine addSlots ClockUnarySum.machine
noncomputable def half:=RecoveryFocus.machine halfSlots CloseoutRowsCircuitHalf.machine
noncomputable def first:=Composition.machine sum literal
noncomputable def second:=Composition.machine first add
noncomputable def machine:=Composition.machine second half
def input (D n : ℕ) (i : Fin 12) :=
  if i=0 then List.replicate D true else if i=1 then List.replicate n true else []
def budget (D n : ℕ):=(2*(D+n)+6)+1+6+1+(2*(D+n+2)+6)+1+CloseoutRowsCircuitHalf.budget (D+n+2)

theorem description_run (D n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget D n) (input D n) out ∧
      out 0=List.replicate D true ∧ out 1=List.replicate n true ∧
      out 10=List.replicate ((D+n+2)/2) true:=by
  have s:=(ClockUnarySum.sum_ready D n).focus sumSlots (by decide) (input D n)
    (by intro i;fin_cases i <;> rfl)
  let sb:=install sumSlots (input D n)
    ![List.replicate D true,List.replicate n true,List.replicate (D+n) true,List.replicate (D+n+2) false]
  have sval:sb 2=List.replicate (D+n) true:=install_slot sumSlots (by decide) _ _ 2
  have sfresh (i : Fin 12) (hi : 4 ≤ i.val) : sb i=[]:=by
    rw [show sb=install sumSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [sumSlots] at hv <;> omega)]
    simp only [input,if_neg (show i ≠ 0 by omega),if_neg (show i ≠ 1 by omega)]
  have l:=(UWalkNumbers.fixed_ready [true,true]).focus literalSlots (by decide) sb
    (by intro i;fin_cases i <;> exact sfresh _ (by decide))
  let lb:=install literalSlots sb ![[true,true],List.replicate 2 false]
  have lvalue:lb 4=List.replicate 2 true:=install_slot literalSlots (by decide) _ _ 0
  have lkeep (i : Fin 12) (hi : i.val < 4 ∨ 6 ≤ i.val) : lb i=sb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [literalSlots] at hv <;> omega)
  have a:=(ClockUnarySum.sum_ready (D+n) 2).focus addSlots (by decide) lb (by
    intro i;fin_cases i
    · exact (lkeep 2 (Or.inl (by decide))).trans sval
    · exact lvalue
    all_goals rw [lkeep _ (Or.inr (by decide))];exact sfresh _ (by decide))
  let ab:=install addSlots lb
    ![List.replicate (D+n) true,List.replicate 2 true,List.replicate (D+n+2) true,
      List.replicate (D+n+2+2) false]
  have avalue:ab 6=List.replicate (D+n+2) true:=install_slot addSlots (by decide) _ _ 2
  have akeep (i : Fin 12) (hi : i.val < 2 ∨ 8 ≤ i.val) : ab i=lb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [addSlots] at hv <;> omega)
  obtain ⟨h,hready,_h0,h3⟩:=CloseoutRowsCircuitHalf.half_run (D+n+2)
  have hf:=hready.focus halfSlots (by decide) ab (by
    intro i;fin_cases i
    · exact avalue
    all_goals rw [akeep _ (Or.inr (by decide)),lkeep _ (Or.inr (by decide))]
    all_goals exact sfresh _ (by decide))
  have all:=ClockJoin.join second half _ _ _ _ _
    (ClockJoin.join first add _ _ _ _ _ (ClockJoin.join sum literal _ _ _ _ _ s l) a) hf
  refine ⟨_,all,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),akeep 0 (Or.inl (by decide)),lkeep 0 (Or.inl (by decide))]
    exact install_slot sumSlots (by decide) _ _ 0
  · rw [install_other _ _ _ _ (by decide),akeep 1 (Or.inl (by decide)),lkeep 1 (Or.inl (by decide))]
    exact install_slot sumSlots (by decide) _ _ 1
  · exact (install_slot halfSlots (by decide) _ _ 3).trans h3

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricDescription
