import Proof.CaseAnalysis.RowsCircuitHalf

/-! The threshold description comes from the actual serialized counters:
subtract actual bottomCount+1 and divide by two. Only the already validated
branch requires the natural subtraction premise; no policy-sized scratch
or free arithmetical input is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdDescription
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dSlots : Fin 3 → Fin 16 := ![0,2,3]
def nSlots : Fin 3 → Fin 16 := ![1,4,5]
def differenceSlots : Fin 4 → Fin 16 := ![2,4,6,7]
def copySlots : Fin 5 → Fin 16 := ![6,8,9,10,11]
def halfSlots : Fin 5 → Fin 16 := ![8,12,13,14,15]
noncomputable def templateD:=RecoveryFocus.machine dSlots (DimensionTemplate.machine false)
noncomputable def templateN:=RecoveryFocus.machine nSlots (DimensionTemplate.machine true)
noncomputable def difference:=RecoveryFocus.machine differenceSlots MatrixUnaryDifference.resetMachine
noncomputable def copy:=RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
noncomputable def half:=RecoveryFocus.machine halfSlots CloseoutRowsCircuitHalf.machine
noncomputable def first:=Composition.machine templateD templateN
noncomputable def second:=Composition.machine first difference
noncomputable def third:=Composition.machine second copy
noncomputable def machine:=Composition.machine third half
def input (D n : ℕ) (i : Fin 16) :=
  if i=0 then List.replicate D true else if i=1 then List.replicate n true else []
def budget (D n : ℕ):=
  (2*D+8)+1+(2*n+8)+1+(2*D+8)+1+(4*(D-(n+1))+12)+1+CloseoutRowsCircuitHalf.budget (D-(n+1))

theorem description_run (D n : ℕ) (hn : n+1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun machine (budget D n) (input D n) out ∧
      out 0=List.replicate D true ∧ out 1=List.replicate n true ∧
      out 14=List.replicate ((D-(n+1))/2) true:=by
  have hd:=(DimensionTemplate.ready false D).focus dSlots (by decide) (input D n)
    (by intro i;fin_cases i <;> rfl)
  let db:=install dSlots (input D n) (DimensionTemplate.output false D)
  have dvalue:db 2=UnaryTemplate.tape D:=install_slot dSlots (by decide) _ _ 1
  have dkeep (i : Fin 16) (hi : i=1 ∨ 4 ≤ i.val) : db i=input D n i:=by
    exact install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [dSlots] at hv <;> rcases hi with rfl|hi <;> omega)
  have hnrun:=(DimensionTemplate.ready true n).focus nSlots (by decide) db (by
    intro i;fin_cases i
    · exact dkeep 1 (Or.inl rfl)
    · exact dkeep 4 (Or.inr (by decide))
    · exact dkeep 5 (Or.inr (by decide)))
  let nb:=install nSlots db (DimensionTemplate.output true n)
  have nvalue:nb 4=UnaryTemplate.tape (n+1):=install_slot nSlots (by decide) _ _ 1
  have nkeep (i : Fin 16) (hi : i=0 ∨ i=2 ∨ 6 ≤ i.val) : nb i=db i:=by
    exact install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [nSlots] at hv <;> rcases hi with rfl|rfl|hi <;> omega)
  have nfresh (i : Fin 16) (hi : 6 ≤ i.val) : nb i=[]:=by
    rw [nkeep i (Or.inr (Or.inr hi)),dkeep i (Or.inr (by omega))]
    simp only [input,if_neg (show i ≠ 0 by omega),if_neg (show i ≠ 1 by omega)]
  obtain ⟨d,dr,_d0,_d1,d2,dh,ds⟩:=MatrixUnaryDifference.reset_run D (n+1) hn
  have diff:ClockJoin.ReadyRun MatrixUnaryDifference.resetMachine (2*D+8)
      (MatrixUnaryDifference.resetInput D (n+1)) d.final.tapes:=⟨d,dr,rfl,dh,ds.le⟩
  have diffused:=diff.focus differenceSlots (by decide) nb (by
    intro i;fin_cases i
    · exact (nkeep 2 (Or.inr (Or.inl rfl))).trans dvalue
    · exact nvalue
    · exact nfresh 6 (by decide)
    · exact nfresh 7 (by decide))
  let sub:=install differenceSlots nb d.final.tapes
  have subvalue:sub 6=UnaryTemplate.tape (D-(n+1)):=
    (install_slot differenceSlots (by decide) _ _ 2).trans d2
  have subkeep (i : Fin 16) (hi : i.val < 2 ∨ 8 ≤ i.val) : sub i=nb i:=by
    exact install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [differenceSlots] at hv <;> omega)
  obtain ⟨c,cr,_c0,c1,_c2,_c3,ch,cs⟩:=MatrixTemplateCopy.reset_run (D-(n+1))
  have copied:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*(D-(n+1))+12)
      (MatrixTemplateCopy.resetInput (D-(n+1))) c.final.tapes:=⟨c,cr,rfl,ch,cs.le⟩
  have cf:=copied.focus copySlots (by decide) sub (by
    intro i;fin_cases i
    · exact subvalue
    all_goals rw [subkeep _ (Or.inr (by decide))];exact nfresh _ (by decide))
  let cb:=install copySlots sub c.final.tapes
  have cvalue:cb 8=List.replicate (D-(n+1)) true:=
    (install_slot copySlots (by decide) _ _ 1).trans c1
  have ckeep (i : Fin 16) (hi : i.val < 6 ∨ 12 ≤ i.val) : cb i=sub i:=by
    exact install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [copySlots] at hv <;> omega)
  obtain ⟨h,hready,_h0,h3⟩:=CloseoutRowsCircuitHalf.half_run (D-(n+1))
  have hf:=hready.focus halfSlots (by decide) cb (by
    intro i;fin_cases i
    · exact cvalue
    all_goals rw [ckeep _ (Or.inr (by decide)),subkeep _ (Or.inr (by decide))]
    all_goals exact nfresh _ (by decide))
  have all:=ClockJoin.join third half _ _ _ _ _
    (ClockJoin.join second copy _ _ _ _ _
      (ClockJoin.join first difference _ _ _ _ _
        (ClockJoin.join templateD templateN _ _ _ _ _ hd hnrun) diffused) cf) hf
  refine ⟨_,all,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),ckeep 0 (Or.inl (by decide)),
      subkeep 0 (Or.inl (by decide)),nkeep 0 (Or.inl rfl)]
    exact install_slot dSlots (by decide) _ _ 0
  · rw [install_other _ _ _ _ (by decide),ckeep 1 (Or.inl (by decide)),
      subkeep 1 (Or.inl (by decide))]
    exact install_slot nSlots (by decide) _ _ 0
  · exact (install_slot halfSlots (by decide) _ _ 3).trans h3

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdDescription
