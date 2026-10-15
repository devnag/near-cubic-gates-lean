import Proof.CaseAnalysis.WitnessDescriptionHorner

/-! The exact gate description polynomial and the source bit length are
produced from actual n alone. The two fixed Horner steps avoid constructing
any exponential normalization bound. All scratch starts blank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GateDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def baseSlots (i : Fin 16) : Fin 34:=i.castAdd 18
def templateSlots : Fin 3→Fin 34:=![0,16,17]
def firstSlots : Fin 8→Fin 34:=![7,16,20,21,22,23,24,25]
def lastSlots : Fin 8→Fin 34:=![24,16,28,29,30,31,32,33]
def base:=RecoveryFocus.machine baseSlots (DimensionPolynomial.machine 1 1)
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def first:=RecoveryFocus.machine firstSlots (DescriptionHorner.machine 2)
def last:=RecoveryFocus.machine lastSlots (DescriptionHorner.machine 1)
def initial:=Composition.machine base template
def middle:=Composition.machine initial first
def machine:=Composition.machine middle last
def input (n : ℕ) (i : Fin 34):=if i.val=0 then List.replicate n true else []
def budget (n : ℕ):=DimensionPolynomial.budget 1 1 n+1+(2*n+8)+1+
  DescriptionHorner.budget 2 (n+1) n+1+DescriptionHorner.budget 1 ((n+1)*n+2) n

theorem base_injective : Function.Injective baseSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 34=>k.val) h)

theorem description_run (n : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget n) (input n) output ∧
      output 0=List.replicate n true ∧ output 7=List.replicate (n+1) true ∧
      output 16=UnaryTemplate.tape n ∧ output 14=CompareMachine.word (natBitLength (n+1)) ∧
      output 32=List.replicate (normalizedGateDescriptionCap n) true:=by
  obtain ⟨b,hb,b0,bv,_,bw⟩:=DimensionPolynomial.polynomial_run 1 1 n (by decide)
  simp only [DimensionPolynomial.value,pow_one,one_mul] at bv bw
  have hbf:=hb.focus baseSlots base_injective (input n) (by intro i;rfl)
  let bb:=install baseSlots (input n) b
  have old (i : Fin 16) : bb (baseSlots i)=b i:=install_slot _ base_injective _ _ _
  have fresh (i : Fin 34) (hi : 16 ≤ i.val) : bb i=[]:=by
    rw [show bb=install baseSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg (fun k : Fin 34=>k.val) h
      change j.val=i.val at hv
      omega)]
    simp only [input,if_neg (show i.val≠0 by omega)]
  have ht:=(DimensionTemplate.ready false n).focus templateSlots (by decide) bb (by
    intro i;fin_cases i
    · exact (old 0).trans b0
    all_goals exact fresh _ (by decide))
  let tb:=install templateSlots bb (DimensionTemplate.output false n)
  have tkeep (i : Fin 34) (hi : i.val≠0 ∧ i.val≠16 ∧ i.val≠17) : tb i=bb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [templateSlots] at hv <;> omega)
  have tzero:tb 0=List.replicate n true:=by
    change install templateSlots _ _ (templateSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  have tv:tb 16=UnaryTemplate.tape n:=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  obtain ⟨f,hf,f0,f1,fv⟩:=DescriptionHorner.horner_run 2 (n+1) n
  have hff:=hf.focus firstSlots (by decide) tb (by
    intro i;fin_cases i
    · rw [tkeep _ ⟨by decide,by decide,by decide⟩]
      exact (old (DimensionPolynomial.rawSlot 1)).trans bv
    · exact tv
    all_goals rw [tkeep _ ⟨by decide,by decide,by decide⟩];exact fresh _ (by decide))
  let fb:=install firstSlots tb f
  have fold (i : Fin 8) : fb (firstSlots i)=f i:=install_slot _ (by decide) _ _ _
  have fkeep (i : Fin 34) (hi : i.val<7 ∨ i.val=14 ∨ 26 ≤ i.val) : fb i=tb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [firstSlots] at hv <;> omega)
  obtain ⟨l,hl,_,l1,lv⟩:=DescriptionHorner.horner_run 1 ((n+1)*n+2) n
  have hlf:=hl.focus lastSlots (by decide) fb (by
    intro i;fin_cases i
    · exact (fold 6).trans fv
    · exact (fold 1).trans f1
    all_goals
      rw [fkeep _ (Or.inr (Or.inr (by decide))),tkeep _ ⟨by decide,by decide,by decide⟩]
      exact fresh _ (by decide))
  have lkeep (i : Fin 34) (hi : i.val<16) : install lastSlots fb l i=fb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [lastSlots] at hv <;> omega)
  have hall:=ClockJoin.join middle last _ _ _ _ _
    (ClockJoin.join initial first _ _ _ _ _ (ClockJoin.join base template _ _ _ _ _ hbf ht) hff) hlf
  refine ⟨_,hall,?_,?_,?_,?_,?_⟩
  · rw [lkeep _ (by decide),fkeep _ (Or.inl (by decide))]
    exact tzero
  · rw [lkeep _ (by decide)]
    exact (fold 0).trans f0
  · change install lastSlots fb l (lastSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective lastSlots)];exact l1
  · rw [lkeep _ (by decide),fkeep _ (Or.inr (Or.inl rfl)),tkeep _ ⟨by decide,by decide,by decide⟩]
    exact (old (DimensionPolynomial.widthSlot 1)).trans bw
  · change install lastSlots fb l (lastSlots 6)=_
    rw [install_slot _ (by decide : Function.Injective lastSlots),lv]
    congr 1
    unfold normalizedGateDescriptionCap
    ring

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.GateDescription
