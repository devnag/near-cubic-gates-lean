import Proof.CaseAnalysis.WitnessGateDescription

/-! The exact restricted description is evaluated in factored form from
the already produced source fields. Every template and multiplication is
paid; the bit-length shift never materializes the exponential parameter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RestrictedDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy ComponentwiseCircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copySlots : Fin 3→Fin 16:=![3,4,5]
def sumSlots : Fin 4→Fin 16:=![2,4,6,7]
def coreSlots : Fin 3→Fin 16:=![0,8,9]
def firstSlots : Fin 4→Fin 16:=![6,8,10,11]
def factorSlots (sym : Bool) : Fin 3→Fin 16:=![if sym then 1 else 2,12,13]
def lastSlots : Fin 4→Fin 16:=![10,12,14,15]
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false true)
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def core:=RecoveryFocus.machine coreSlots (DimensionTemplate.machine true)
def firstProduct:=RecoveryFocus.machine firstSlots ClockUnaryProduct.machine
def factorProgram (sym : Bool):=RecoveryFocus.machine (factorSlots sym) (DimensionTemplate.machine (!sym))
def lastProduct:=RecoveryFocus.machine lastSlots ClockUnaryProduct.machine
def first:=Composition.machine copy sum
def second:=Composition.machine first core
def third:=Composition.machine second firstProduct
def fourth (sym : Bool):=Composition.machine third (factorProgram sym)
def machine (sym : Bool):=Composition.machine (fourth sym) lastProduct
def factor (sym : Bool) (W L : ℕ):=if sym then W+1 else L+1
def factorInput (sym : Bool) (W L : ℕ):=if sym then W+1 else L
def height (L b : ℕ):=L+(b+1)
def value (sym : Bool) (core W L b : ℕ):=factor sym W L*(core+1)*height L b
def input (core W L b : ℕ) : Fin 16→List Bool:=
  ![List.replicate core true,List.replicate (W+1) true,List.replicate L true,
    CompareMachine.word b,[],[],[],[],[],[],[],[],[],[],[],[]]
def budget (sym : Bool) (core W L b : ℕ):=(2*b+6)+1+(2*height L b+6)+1+(2*core+8)+1+
  WilliamsUnaryProduct.budget (height L b) (core+1)+1+(2*factorInput sym W L+8)+1+
    WilliamsUnaryProduct.budget (height L b*(core+1)) (factor sym W L)

theorem factor_exact (sym : Bool) (W L : ℕ) : factorInput sym W L+(!sym).toNat=factor sym W L:=by
  cases sym <;> rfl
theorem factor_injective (sym : Bool) : Function.Injective (factorSlots sym):=by cases sym <;> decide
theorem symmetric_exact (core n W : ℕ) :
    value true core W (symmetricDescriptionCap n W) (natBitLength (n+1))=
      restrictedSymmetricDescriptionCap core n (2^symmetricDescriptionCap n W) W:=by
  rw [CloseoutWitnessPolicy.symmetric_description_exact]
  simp only [value,factor,ite_true,height]
  ring
theorem threshold_exact (core n W : ℕ) :
    value false core W (thresholdDescriptionCap n W) (natBitLength (n+1))=
      restrictedThresholdDescriptionCap core n (2^thresholdDescriptionCap n W) (thresholdDescriptionCap n W):=by
  rw [CloseoutWitnessPolicy.threshold_description_exact]
  simp only [value,factor,Bool.false_eq_true,ite_false,height]
  ring

theorem description_run (sym : Bool) (R W L b : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine sym) (budget sym R W L b) (input R W L b) output ∧
      output 0=List.replicate R true ∧ output 1=List.replicate (W+1) true ∧
      output 2=List.replicate L true ∧ output 3=CompareMachine.word b ∧
      output 14=List.replicate (value sym R W L b) true:=by
  have hc:=(UWalkUnary.ready false true 0 b).focus copySlots (by decide) (input R W L b) (by
    intro i;fin_cases i
    · change CompareMachine.word b=UWalkUnary.source 0 b
      rw [UWalkUnary.source,ZeroPadding.pad_zero]
    all_goals rfl)
  let cb:=install copySlots (input R W L b) (UWalkUnary.result false true 0 b)
  have ckeep (i : Fin 16) (hi : i.val<3 ∨ 6 ≤ i.val) : cb i=input R W L b i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [copySlots] at hv <;> omega)
  have hs:=(ClockUnarySum.sum_ready L (b+1)).focus sumSlots (by decide) cb (by
    intro i;fin_cases i
    · exact ckeep _ (Or.inl (by decide))
    · change install copySlots _ _ (copySlots 1)=_
      rw [install_slot _ (by decide : Function.Injective copySlots)];rfl
    all_goals exact ckeep _ (Or.inr (by decide)))
  let sb:=install sumSlots cb ![List.replicate L true,List.replicate (b+1) true,
    List.replicate (height L b) true,List.replicate (height L b+2) false]
  have skeep (i : Fin 16) (hi : i.val≠2 ∧ i.val≠4 ∧ i.val≠6 ∧ i.val≠7) : sb i=cb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [sumSlots] at hv <;> omega)
  have hcore:=(DimensionTemplate.ready true R).focus coreSlots (by decide) sb (by
    intro i;fin_cases i
    · rw [skeep _ ⟨by decide,by decide,by decide,by decide⟩];exact ckeep _ (Or.inl (by decide))
    all_goals rw [skeep _ ⟨by decide,by decide,by decide,by decide⟩];exact ckeep _ (Or.inr (by decide)))
  let rb:=install coreSlots sb (DimensionTemplate.output true R)
  have rkeep (i : Fin 16) (hi : i.val≠0 ∧ i.val≠8 ∧ i.val≠9) : rb i=sb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [coreSlots] at hv <;> omega)
  have hpr:ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (height L b) (R+1))
      (WilliamsUnaryProduct.input (height L b) (R+1)) (WilliamsUnaryProduct.output (height L b) (R+1)):=by
    obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready (height L b) (R+1)
    exact ⟨p,hp,pt,ph,ps.le⟩
  have hp:=hpr.focus firstSlots (by decide) rb (by
    intro i;fin_cases i
    · rw [rkeep _ ⟨by decide,by decide,by decide⟩]
      change install sumSlots _ _ (sumSlots 2)=_
      rw [install_slot _ (by decide : Function.Injective sumSlots)];rfl
    · change install coreSlots _ _ (coreSlots 1)=_
      rw [install_slot _ (by decide : Function.Injective coreSlots)];rfl
    all_goals
      rw [rkeep _ ⟨by decide,by decide,by decide⟩,skeep _ ⟨by decide,by decide,by decide,by decide⟩]
      exact ckeep _ (Or.inr (by decide)))
  let pb:=install firstSlots rb (WilliamsUnaryProduct.output (height L b) (R+1))
  have pkeep (i : Fin 16) (hi : i.val<6 ∨ 12 ≤ i.val) : pb i=rb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [firstSlots] at hv <;> omega)
  have hf:=(DimensionTemplate.ready (!sym) (factorInput sym W L)).focus (factorSlots sym)
    (factor_injective sym) pb (by
      intro i;fin_cases i
      · cases sym
        · rw [pkeep _ (Or.inl (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩]
          change install sumSlots _ _ (sumSlots 0)=_
          rw [install_slot _ (by decide : Function.Injective sumSlots)];rfl
        · rw [pkeep _ (Or.inl (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩,
            skeep _ ⟨by decide,by decide,by decide,by decide⟩]
          exact ckeep _ (Or.inl (by decide))
      all_goals cases sym
      all_goals
        rw [pkeep _ (Or.inr (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩,
          skeep _ ⟨by decide,by decide,by decide,by decide⟩]
        exact ckeep _ (Or.inr (by decide)))
  let fb:=install (factorSlots sym) pb (DimensionTemplate.output (!sym) (factorInput sym W L))
  have fkeep (i : Fin 16) (hi : i.val≠1 ∧ i.val≠2 ∧ i.val≠12 ∧ i.val≠13) : fb i=pb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      cases sym <;> fin_cases j <;> simp [factorSlots] at hv <;> omega)
  have hlast:ClockJoin.ReadyRun ClockUnaryProduct.machine
      (WilliamsUnaryProduct.budget (height L b*(R+1)) (factor sym W L))
      (WilliamsUnaryProduct.input (height L b*(R+1)) (factor sym W L))
      (WilliamsUnaryProduct.output (height L b*(R+1)) (factor sym W L)):=by
    obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready (height L b*(R+1)) (factor sym W L)
    exact ⟨p,hp,pt,ph,ps.le⟩
  have hl:=hlast.focus lastSlots (by decide) fb (by
    intro i;fin_cases i
    · rw [fkeep _ ⟨by decide,by decide,by decide,by decide⟩]
      change install firstSlots _ _ (firstSlots 2)=_
      rw [install_slot _ (by decide : Function.Injective firstSlots)];rfl
    · change install (factorSlots sym) _ _ (factorSlots sym 1)=_
      rw [install_slot _ (factor_injective sym)]
      change UnaryTemplate.tape (factorInput sym W L+(!sym).toNat)=UnaryTemplate.tape (factor sym W L)
      rw [factor_exact]
    all_goals
      rw [fkeep _ ⟨by decide,by decide,by decide,by decide⟩,pkeep _ (Or.inr (by decide)),
        rkeep _ ⟨by decide,by decide,by decide⟩,skeep _ ⟨by decide,by decide,by decide,by decide⟩]
      exact ckeep _ (Or.inr (by decide)))
  have allRun:=ClockJoin.join (fourth sym) lastProduct _ _ _ _ _
    (ClockJoin.join third (factorProgram sym) _ _ _ _ _
      (ClockJoin.join second firstProduct _ _ _ _ _
        (ClockJoin.join first core _ _ _ _ _ (ClockJoin.join copy sum _ _ _ _ _ hc hs) hcore) hp) hf) hl
  have keepLast (i : Fin 16) (hi : i.val<10) :
      install lastSlots fb (WilliamsUnaryProduct.output (height L b*(R+1)) (factor sym W L)) i=fb i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [lastSlots] at hv <;> omega)
  refine ⟨_,allRun,?_,?_,?_,?_,?_⟩
  · rw [keepLast _ (by decide),fkeep _ ⟨by decide,by decide,by decide,by decide⟩,pkeep _ (Or.inl (by decide))]
    change install coreSlots _ _ (coreSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective coreSlots)];rfl
  · rw [keepLast _ (by decide)]
    cases sym
    · rw [show fb=install (factorSlots false) _ _ by rfl,install_other _ _ _ _ (by decide),
        pkeep _ (Or.inl (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩,
        skeep _ ⟨by decide,by decide,by decide,by decide⟩]
      exact ckeep _ (Or.inl (by decide))
    · change install (factorSlots true) _ _ (factorSlots true 0)=_
      rw [install_slot _ (factor_injective true)];rfl
  · rw [keepLast _ (by decide)]
    cases sym
    · change install (factorSlots false) _ _ (factorSlots false 0)=_
      rw [install_slot _ (factor_injective false)];rfl
    · rw [show fb=install (factorSlots true) _ _ by rfl,install_other _ _ _ _ (by decide),
        pkeep _ (Or.inl (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩]
      change install sumSlots _ _ (sumSlots 0)=_
      rw [install_slot _ (by decide : Function.Injective sumSlots)];rfl
  · rw [keepLast _ (by decide),fkeep _ ⟨by decide,by decide,by decide,by decide⟩,
      pkeep _ (Or.inl (by decide)),rkeep _ ⟨by decide,by decide,by decide⟩,
      skeep _ ⟨by decide,by decide,by decide,by decide⟩]
    change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ (by decide : Function.Injective copySlots)]
    change UWalkUnary.source 0 b=CompareMachine.word b
    rw [UWalkUnary.source,ZeroPadding.pad_zero]
  · change install lastSlots _ _ (lastSlots 2)=_
    rw [install_slot _ (by decide : Function.Injective lastSlots)]
    change List.replicate ((height L b*(R+1))*factor sym W L) true=List.replicate (value sym R W L b) true
    congr 1
    unfold value
    ring

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.RestrictedDescription
