import Proof.CaseAnalysis.WitnessGateDescription

/-! The original normalized-circuit description cap is produced exactly
for each fixed mode. Both short arguments come from the actual source
policy; no weight-size exponential is constructed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BaseDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlots (i : Fin 34) : Fin 76:=i.castAdd 42
def wireSlots (i : Fin 34) : Fin 76:=⟨if i.val=0 then 34 else 35+i.val,by split_ifs <;> omega⟩
def templateSlots : Fin 3→Fin 76:=![32,69,70]
def productSlots (sym : Bool) : Fin 4→Fin 76:=![if sym then 42 else 34,69,71,72]
def sumSlots (sym : Bool) : Fin 4→Fin 76:=![71,if sym then 73 else 67,74,75]
def source:=RecoveryFocus.machine sourceSlots GateDescription.machine
def wire:=RecoveryFocus.machine wireSlots GateDescription.machine
def template (sym : Bool):=RecoveryFocus.machine templateSlots (DimensionTemplate.machine sym)
def product (sym : Bool):=RecoveryFocus.machine (productSlots sym) ClockUnaryProduct.machine
def sum (sym : Bool):=RecoveryFocus.machine (sumSlots sym) ClockUnarySum.machine
def first:=Composition.machine source wire
def second (sym : Bool):=Composition.machine first (template sym)
def third (sym : Bool):=Composition.machine (second sym) (product sym)
def machine (sym : Bool):=Composition.machine (third sym) (sum sym)
def input (n W : ℕ) (i : Fin 76):=
  if i.val=0 then List.replicate n true else if i.val=34 then List.replicate W true else []
def factor (sym : Bool) (W : ℕ):=if sym then W+1 else W
def offset (sym : Bool) (W : ℕ):=if sym then 0 else normalizedGateDescriptionCap W
def value (sym : Bool) (n W : ℕ):=
  factor sym W*(normalizedGateDescriptionCap n+sym.toNat)+offset sym W
def budget (sym : Bool) (n W : ℕ):=GateDescription.budget n+1+GateDescription.budget W+1+
  (2*normalizedGateDescriptionCap n+8)+1+
  WilliamsUnaryProduct.budget (factor sym W) (normalizedGateDescriptionCap n+sym.toNat)+1+
  (2*value sym n W+6)

theorem value_symmetric (n W : ℕ) : value true n W=symmetricDescriptionCap n W:=rfl
theorem value_threshold (n W : ℕ) : value false n W=thresholdDescriptionCap n W:=by
  simp [value,factor,offset,thresholdDescriptionCap,Nat.add_comm]
theorem source_injective : Function.Injective sourceSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 76=>k.val) h)
theorem wire_injective : Function.Injective wireSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 76=>k.val) h
  dsimp only [wireSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem product_injective (sym : Bool) : Function.Injective (productSlots sym):=by cases sym <;> decide
theorem sum_injective (sym : Bool) : Function.Injective (sumSlots sym):=by cases sym <;> decide

theorem description_run (sym : Bool) (n W : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine sym) (budget sym n W) (input n W) output ∧
      output 0=List.replicate n true ∧ output 34=List.replicate W true ∧
      output 42=List.replicate (W+1) true ∧
      output 14=CompareMachine.word (natBitLength (n+1)) ∧
      output 74=List.replicate (value sym n W) true:=by
  obtain ⟨s,hs,s0,_,_,sb,sg⟩:=GateDescription.description_run n
  have hsf:=hs.focus sourceSlots source_injective (input n W) (by
    intro i
    have hi:=i.isLt
    simp only [sourceSlots,Fin.val_castAdd,input,GateDescription.input]
    split_ifs <;> first | rfl | omega)
  let sn:=install sourceSlots (input n W) s
  have sold (i : Fin 34) : sn (sourceSlots i)=s i:=install_slot _ source_injective _ _ _
  have sfresh (i : Fin 76) (hi : 34 ≤ i.val) : sn i=input n W i:=by
    apply install_other
    intro j h
    have hv:=congrArg (fun k : Fin 76=>k.val) h
    change j.val=i.val at hv
    omega
  obtain ⟨w,hw,w0,w1,_,_,wg⟩:=GateDescription.description_run W
  have hwf:=hw.focus wireSlots wire_injective sn (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      rw [he];exact sfresh 34 (by decide)
    rw [GateDescription.input,if_neg h0,sfresh _ (by simp only [wireSlots,if_neg h0];omega)]
    simp only [input,wireSlots,if_neg h0,if_neg (show 35+i.val≠0 by omega),
      if_neg (show 35+i.val≠34 by omega)])
  let wn:=install wireSlots sn w
  have wold (i : Fin 34) : wn (wireSlots i)=w i:=install_slot _ wire_injective _ _ _
  have wkeep (i : Fin 76) (hi : i.val<34 ∨ 69 ≤ i.val) : wn i=sn i:=
    install_other _ _ _ _ (by
      intro j h
      have hj:=j.isLt
      have hv:=congrArg (fun k : Fin 76=>k.val) h
      dsimp only [wireSlots] at hv
      split_ifs at hv <;> omega)
  have wfresh (i : Fin 76) (hi : 69 ≤ i.val) : wn i=[]:=by
    rw [wkeep i (Or.inr hi),sfresh i (by omega)]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠34 by omega)]
  have ht:=(DimensionTemplate.ready sym (normalizedGateDescriptionCap n)).focus templateSlots
    (by decide) wn (by
      intro i;fin_cases i
      · rw [wkeep _ (Or.inl (by decide))];exact (sold 32).trans sg
      all_goals exact wfresh _ (by decide))
  let tn:=install templateSlots wn (DimensionTemplate.output sym (normalizedGateDescriptionCap n))
  have tkeep (i : Fin 76) (hi : i.val≠32 ∧ i.val≠69 ∧ i.val≠70) : tn i=wn i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      fin_cases j <;> simp [templateSlots] at hv <;> omega)
  have tv:tn 69=UnaryTemplate.tape (normalizedGateDescriptionCap n+sym.toNat):=by
    change install templateSlots _ _ (templateSlots 1)=_
    rw [install_slot _ (by decide : Function.Injective templateSlots)];rfl
  have hp:ClockJoin.ReadyRun ClockUnaryProduct.machine
      (WilliamsUnaryProduct.budget (factor sym W) (normalizedGateDescriptionCap n+sym.toNat))
      (WilliamsUnaryProduct.input (factor sym W) (normalizedGateDescriptionCap n+sym.toNat))
      (WilliamsUnaryProduct.output (factor sym W) (normalizedGateDescriptionCap n+sym.toNat)):=by
    obtain ⟨p,hp,pt,ph,ps⟩:=WilliamsUnaryProduct.product_ready (factor sym W) (normalizedGateDescriptionCap n+sym.toNat)
    exact ⟨p,hp,pt,ph,ps.le⟩
  have hpf:=hp.focus (productSlots sym) (product_injective sym) tn (by
    intro i;fin_cases i
    · cases sym
      · rw [tkeep _ ⟨by decide,by decide,by decide⟩];exact (wold 0).trans w0
      · rw [tkeep _ ⟨by decide,by decide,by decide⟩];exact (wold 7).trans w1
    · exact tv
    all_goals cases sym <;> rw [tkeep _ ⟨by decide,by decide,by decide⟩] <;> exact wfresh _ (by decide))
  let pn:=install (productSlots sym) tn
    (WilliamsUnaryProduct.output (factor sym W) (normalizedGateDescriptionCap n+sym.toNat))
  have pkeep (i : Fin 76) (hi : i.val≠34 ∧ i.val≠42 ∧ i.val≠69 ∧ i.val≠71 ∧ i.val≠72) : pn i=tn i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      cases sym <;> fin_cases j <;> simp [productSlots] at hv <;> omega)
  have hs:=(ClockUnarySum.sum_ready
      (factor sym W*(normalizedGateDescriptionCap n+sym.toNat)) (offset sym W)).focus
    (sumSlots sym) (sum_injective sym) pn (by
      intro i;fin_cases i
      · change install (productSlots sym) _ _ (productSlots sym 2)=_
        rw [install_slot _ (product_injective sym)];rfl
      · cases sym
        · rw [pkeep _ ⟨by decide,by decide,by decide,by decide,by decide⟩,
            tkeep _ ⟨by decide,by decide,by decide⟩]
          exact (wold 32).trans wg
        · rw [pkeep _ ⟨by decide,by decide,by decide,by decide,by decide⟩,
            tkeep _ ⟨by decide,by decide,by decide⟩]
          exact wfresh _ (by decide)
      all_goals
        cases sym
        all_goals
        rw [pkeep _ ⟨by decide,by decide,by decide,by decide,by decide⟩,
          tkeep _ ⟨by decide,by decide,by decide⟩]
        exact wfresh _ (by decide))
  have sk (i : Fin 76) (hi : i.val<67) :
      install (sumSlots sym) pn
        ![List.replicate (factor sym W*(normalizedGateDescriptionCap n+sym.toNat)) true,
          List.replicate (offset sym W) true,List.replicate (value sym n W) true,
          List.replicate (value sym n W+2) false] i=pn i:=
    install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h
      cases sym <;> fin_cases j <;> simp [sumSlots] at hv <;> omega)
  dsimp only [value] at sk
  have hall:=ClockJoin.join (third sym) (sum sym) _ _ _ _ _
    (ClockJoin.join (second sym) (product sym) _ _ _ _ _
      (ClockJoin.join first (template sym) _ _ _ _ _
        (ClockJoin.join source wire _ _ _ _ _ hsf hwf) ht) hpf) hs
  refine ⟨_,hall,?_,?_,?_,?_,?_⟩
  · rw [sk _ (by decide),pkeep _ ⟨by decide,by decide,by decide,by decide,by decide⟩,
      tkeep _ ⟨by decide,by decide,by decide⟩,wkeep _ (Or.inl (by decide))]
    exact (sold 0).trans s0
  · rw [sk _ (by decide)]
    cases sym
    · change install (productSlots false) _ _ (productSlots false 0)=_
      rw [install_slot _ (product_injective false)];rfl
    · rw [show pn=install (productSlots true) _ _ by rfl,install_other _ _ _ _ (by decide),
        tkeep _ ⟨by decide,by decide,by decide⟩]
      exact (wold 0).trans w0
  · rw [sk _ (by decide)]
    cases sym
    · rw [show pn=install (productSlots false) _ _ by rfl,install_other _ _ _ _ (by decide),
        tkeep _ ⟨by decide,by decide,by decide⟩]
      exact (wold 7).trans w1
    · change install (productSlots true) _ _ (productSlots true 0)=_
      rw [install_slot _ (product_injective true)];rfl
  · rw [sk _ (by decide),pkeep _ ⟨by decide,by decide,by decide,by decide,by decide⟩,
      tkeep _ ⟨by decide,by decide,by decide⟩,wkeep _ (Or.inl (by decide))]
    exact (sold 14).trans sb
  · change install (sumSlots sym) _ _ (sumSlots sym 2)=_
    rw [install_slot _ (sum_injective sym)];rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BaseDescription
