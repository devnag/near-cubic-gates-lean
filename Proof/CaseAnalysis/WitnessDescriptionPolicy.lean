import Proof.CaseAnalysis.WitnessBaseDescription
import Proof.CaseAnalysis.WitnessRestrictedDescription

/-! Complete exact mode description policy from actual core, q0 and W.
All intermediate caps, bit lengths, factors and templates are produced by
the same execution; no exponential normalization parameter is expanded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionPolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open RecoveryWitnessPolicy ComponentwiseCircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def baseSlots (i : Fin 76) : Fin 93:=i.castAdd 17
def restrictionSlots (i : Fin 16) : Fin 93:=
  ⟨if i.val=0 then 76 else if i.val=1 then 42 else if i.val=2 then 74
    else if i.val=3 then 14 else 77+i.val,by split_ifs <;> omega⟩
def first (sym : Bool):=RecoveryFocus.machine baseSlots (BaseDescription.machine sym)
def second (sym : Bool):=RecoveryFocus.machine restrictionSlots (RestrictedDescription.machine sym)
def machine (sym : Bool):=Composition.machine (first sym) (second sym)
def input (R n W : ℕ) (i : Fin 93):=
  if i.val=0 then List.replicate n true else if i.val=34 then List.replicate W true
  else if i.val=76 then List.replicate R true else []
def value (sym : Bool) (R n W : ℕ):=
  if sym then restrictedSymmetricDescriptionCap R n (2^symmetricDescriptionCap n W) W
  else restrictedThresholdDescriptionCap R n (2^thresholdDescriptionCap n W) (thresholdDescriptionCap n W)
def budget (sym : Bool) (R n W : ℕ):=BaseDescription.budget sym n W+1+
  RestrictedDescription.budget sym R W (BaseDescription.value sym n W) (natBitLength (n+1))

theorem value_exact (sym : Bool) (R n W : ℕ) :
    RestrictedDescription.value sym R W (BaseDescription.value sym n W) (natBitLength (n+1))=value sym R n W:=by
  cases sym
  · rw [BaseDescription.value_threshold]
    exact RestrictedDescription.threshold_exact R n W
  · rw [BaseDescription.value_symmetric]
    exact RestrictedDescription.symmetric_exact R n W
theorem base_injective : Function.Injective baseSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 93=>k.val) h)
theorem restriction_injective : Function.Injective restrictionSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 93=>k.val) h
  dsimp only [restrictionSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem description_run (sym : Bool) (R n W : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine sym) (budget sym R n W) (input R n W) output ∧
      output 0=List.replicate n true ∧ output 34=List.replicate W true ∧
      output 76=List.replicate R true ∧ output 91=List.replicate (value sym R n W) true:=by
  obtain ⟨b,hb,b0,bW,bW1,bb,bL⟩:=BaseDescription.description_run sym n W
  have hbf:=hb.focus baseSlots base_injective (input R n W) (by
    intro i
    have hi:=i.isLt
    simp only [baseSlots,Fin.val_castAdd,input,BaseDescription.input]
    split_ifs <;> first | rfl | omega)
  let bank:=install baseSlots (input R n W) b
  have old (i : Fin 76) : bank (baseSlots i)=b i:=install_slot _ base_injective _ _ _
  have fresh (i : Fin 93) (hi : 76 ≤ i.val) : bank i=input R n W i:=by
    apply install_other
    intro j h
    have hv:=congrArg (fun k : Fin 93=>k.val) h
    change j.val=i.val at hv
    omega
  obtain ⟨r,hr,r0,_,_,_,rv⟩:=RestrictedDescription.description_run sym R W
    (BaseDescription.value sym n W) (natBitLength (n+1))
  have hrf:=hr.focus restrictionSlots restriction_injective bank (by
    intro i;fin_cases i
    · exact fresh 76 (by decide)
    · exact (old 42).trans bW1
    · exact (old 74).trans bL
    · exact (old 14).trans bb
    all_goals exact fresh _ (by decide))
  have keep (i : Fin 76) (hi : i.val≠14 ∧ i.val≠42 ∧ i.val≠74) :
      install restrictionSlots bank r (baseSlots i)=b i:=by
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun k : Fin 93=>k.val) h
      have hj:=i.isLt
      dsimp only [restrictionSlots,baseSlots,Fin.val_castAdd] at hv
      split_ifs at hv <;> omega)]
    exact old i
  refine ⟨_,ClockJoin.join (first sym) (second sym) _ _ _ _ _ hbf hrf,?_,?_,?_,?_⟩
  · exact (keep 0 ⟨by decide,by decide,by decide⟩).trans b0
  · exact (keep 34 ⟨by decide,by decide,by decide⟩).trans bW
  · change install restrictionSlots bank r (restrictionSlots 0)=_
    rw [install_slot _ restriction_injective];exact r0
  · change install restrictionSlots bank r (restrictionSlots 14)=_
    rw [install_slot _ restriction_injective,rv,value_exact]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionPolicy
