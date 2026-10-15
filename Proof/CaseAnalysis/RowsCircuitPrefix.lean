import Proof.CaseAnalysis.RowsCircuitMode

/-! Complete cold circuit framing, fixed canonical family tag and actual
bottom-list count. The original ordered gate stream and top code are retained
for the full circuit worker; no circuit is reencoded for this decision. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
open LocalBitMultitape RecoveryRootRound RadixSemantics PCPPNativeCanonicalTree
open CanonicalBinary CloseoutRowsCircuitHeader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 268) : Fin 639:=i.castAdd 371
def countSlots (i : Fin 368) : Fin 639:=
  if i.val=0 then 118 else if i.val=174 then 78 else
    ⟨if i.val<174 then 267+i.val else 266+i.val,by split_ifs <;> omega⟩
def modeSlots (i : Fin 5) : Fin 639:=if i.val=0 then 38 else ⟨633+i.val,by omega⟩
def flagSlots : Fin 4→Fin 639:=![267,633,635,638]
def input (bits : List Bool) : Fin 639→List Bool:=
  Fin.addCases (m:=268) (n:=371) (motive:=fun _=>List Bool)
    (CloseoutRowsCircuitTagged.input bits) (fun _=>[])
noncomputable def header:=RecoveryFocus.machine old CloseoutRowsCircuitTagged.machine
noncomputable def counter:=RecoveryFocus.machine countSlots CloseoutRowsCircuitCount.machine
noncomputable def mode (threshold : Bool):=RecoveryFocus.machine modeSlots (CloseoutRowsCircuitMode.machine threshold)
noncomputable def finish:=RecoveryFocus.machine flagSlots CloseoutRowsCircuitCount.fold
noncomputable def phase1:=Composition.machine header counter
noncomputable def phase2 (threshold : Bool):=Composition.machine phase1 (mode threshold)
noncomputable def machine (threshold : Bool):=Composition.machine (phase2 threshold) finish
def budget (bits : List Bool):=CloseoutRowsCircuitTagged.budget bits+
  CloseoutRowsCircuitCount.budget (codeWord bits 2) (codeWord bits 1)+
  CloseoutRowsCircuitMode.budget (codeWord bits 0)+4
def valid (threshold : Bool) (bits : List Bool) : Prop:=
  structural bits ∧ decodeNat (value (codeWord bits 0))=some threshold.toNat ∧
    ∃ values,decodeBalancedList (value (codeWord bits 2))=some values ∧
      decodeNat (value (codeWord bits 1))=some values.length

theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 639=>k.val) h)
theorem count_val (i : Fin 368) : (countSlots i).val=
    if i.val=0 then 118 else if i.val=174 then 78 else
      if i.val<174 then 267+i.val else 266+i.val:=by
  unfold countSlots;split_ifs <;> rfl
theorem count_injective : Function.Injective countSlots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 639=>k.val) h
  rw [count_val,count_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem mode_injective : Function.Injective modeSlots:=by decide
theorem count_outside (i : Fin 639) (hi:i.val<268) (h78:i≠78) (h118:i≠118) :
    ∀ j,countSlots j≠i:=by
  intro j he;have hv:=congrArg (fun k : Fin 639=>k.val) he
  simp only [countSlots] at hv
  split_ifs at hv with h0 h174 hlt
  · exact h118 (Fin.ext hv.symm)
  · exact h78 (Fin.ext hv.symm)
  · change 267+j.val=i.val at hv;omega
  · change 266+j.val=i.val at hv;omega
theorem count_after (i : Fin 639) (hi:634 ≤ i.val) : ∀ j,countSlots j≠i:=by
  intro j he;have hv:=congrArg (fun k : Fin 639=>k.val) he
  simp only [countSlots] at hv
  split_ifs at hv <;> simp_all <;> omega

theorem prefix_run (threshold : Bool) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine threshold) (budget bits) (input bits) out ∧
      out 158=frame (codeWord bits 3) ∧
      out 297=PCPPNativeCanonicalWalk.atomStream (codeWord bits 2).length (tree (value (codeWord bits 2))).atoms ∧
      out 622=List.replicate (CloseoutRowsCircuitCount.count (codeWord bits 2)) true ∧
      out 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (codeWord bits 2)) ∧
      (readTapeBit (out 638) 0=true ↔ valid threshold bits):=by
  obtain ⟨hh,hflag,hfields⟩:=CloseoutRowsCircuitTagged.tagged_run bits
  have hheader:=hh.focus old old_injective (input bits) (by
    intro i;simp only [input,old,Fin.addCases_left])
  let one:=install old (input bits) (CloseoutRowsCircuitTagged.output bits)
  have one_old (i : Fin 268) : one (old i)=CloseoutRowsCircuitTagged.output bits i:=install_slot old old_injective _ _ i
  have one_new (i : Fin 639) (hi:268 ≤ i.val) : one i=[]:=by
    rw [show one=install old (input bits) _ by rfl,install_other _ _ _ _ (by
      intro j he;have hv:=congrArg (fun k : Fin 639=>k.val) he;change j.val=i.val at hv;omega)]
    simp [input,Fin.addCases,show ¬i.val<268 by omega]
  obtain ⟨ct,hc,stream,raw,template,flag⟩:=CloseoutRowsCircuitCount.public_run (codeWord bits 2) (codeWord bits 1)
  have hcount:=hc.focus countSlots count_injective one (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0;subst i
      exact (one_old 118).trans (hfields 2)
    · by_cases h174:i.val=174
      · have he:i=174:=Fin.ext h174;subst i
        exact (one_old 78).trans (hfields 1)
      · rw [one_new _ (by rw [count_val,if_neg h0,if_neg h174];split_ifs <;> omega)]
        simp only [CloseoutRowsCircuitCount.input,if_neg h0,if_neg h174])
  let two:=install countSlots one ct
  have two_old (i : Fin 268) (h78:i≠78) (h118:i≠118) :
      two (old i)=CloseoutRowsCircuitTagged.output bits i:=by
    rw [show two=install countSlots one ct by rfl,install_other _ _ _ _
      (count_outside (old i) i.isLt (by intro h;exact h78 (Fin.ext (congrArg (fun k : Fin 639=>k.val) h)))
        (by intro h;exact h118 (Fin.ext (congrArg (fun k : Fin 639=>k.val) h))))]
    exact one_old i
  have two_new (i : Fin 639) (hi:634 ≤ i.val) : two i=[]:=by
    rw [show two=install countSlots one ct by rfl,install_other _ _ _ _ (count_after i hi),one_new _ (by omega)]
  obtain ⟨mo,hm,_mraw,mflag⟩:=CloseoutRowsCircuitMode.mode_run threshold (codeWord bits 0)
  have hmode:=hm.focus modeSlots mode_injective two (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0;subst i
      exact (two_old 38 (by decide) (by decide)).trans (hfields 0)
    · rw [modeSlots,if_neg h0,two_new _ (by change 634 ≤ 633+i.val;omega)]
      fin_cases i <;> simp_all [CloseoutRowsCircuitMode.input])
  let three:=install modeSlots two mo
  have three_other (i : Fin 639) (hi:∀ j,modeSlots j≠i) : three i=two i:=install_other _ _ _ _ hi
  have tag:three 267=CloseoutRowsCircuitTagged.output bits 267:=by
    rw [three_other _ (by decide)];exact two_old 267 (by decide) (by decide)
  have cnt:three 633=ct 367:=by
    rw [three_other _ (by decide)]
    exact install_slot countSlots count_injective one ct 367
  have mod:three 635=mo 2:=install_slot modeSlots mode_injective two mo 2
  have hf:=(CloseoutRowsCircuitCount.fold_run (three 267) (three 633) (three 635)).focus flagSlots (by decide) three (by
    intro i;fin_cases i
    · rfl
    · rfl
    · rfl
    · rw [three_other _ (by decide),two_new _ (by decide)];rfl)
  have h1:=ClockJoin.join header counter _ _ _ _ _ hheader hcount
  have h2:=ClockJoin.join phase1 (mode threshold) _ _ _ _ _ h1 hmode
  have hall:=ClockJoin.join (phase2 threshold) finish _ _ _ _ _ h2 hf
  have ht:((CloseoutRowsCircuitTagged.budget bits+1+
      CloseoutRowsCircuitCount.budget (codeWord bits 2) (codeWord bits 1))+1+
      CloseoutRowsCircuitMode.budget (codeWord bits 0))+1+1=budget bits:=by unfold budget;omega
  rw [ht] at hall
  refine ⟨_,hall,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),three_other _ (by decide)]
    exact (two_old 158 (by decide) (by decide)).trans (hfields 3)
  · rw [install_other _ _ _ _ (by decide),three_other _ (by decide)]
    exact (install_slot countSlots count_injective one ct 30).trans stream
  · rw [install_other _ _ _ _ (by decide),three_other _ (by decide)]
    exact (install_slot countSlots count_injective one ct 356).trans raw
  · rw [install_other _ _ _ _ (by decide),three_other _ (by decide)]
    exact (install_slot countSlots count_injective one ct 358).trans template
  · change readTapeBit (install flagSlots three _ (flagSlots 3)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change (readTapeBit (three 267) 0 && readTapeBit (three 633) 0 && readTapeBit (three 635) 0)=true ↔_
    rw [tag,cnt,mod]
    simp only [Bool.and_eq_true,hflag,flag,mflag,valid]
    exact ⟨fun ⟨⟨a,b⟩,c⟩=>⟨a,c,b⟩,fun ⟨a,b,c⟩=>⟨⟨a,c⟩,b⟩⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
