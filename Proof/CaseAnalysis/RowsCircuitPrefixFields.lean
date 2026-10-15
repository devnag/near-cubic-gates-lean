import Proof.CaseAnalysis.RowsCircuitPrefixSupport

/-! The same canonical prefix run retains its original raw circuit field.
The enclosing circuit receipt uses this projection, without a second parse. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
open LocalBitMultitape RecoveryRootRound RadixSemantics PCPPNativeCanonicalTree
open CanonicalBinary CloseoutRowsCircuitHeader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_raw (bits : List Bool) : CloseoutRowsCircuitHeader.output bits 1=frame bits:=by
  rw [CloseoutRowsCircuitHeader.output,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [CloseoutRowsCircuitHeader.last_val] at hv
    split_ifs at hv <;> omega)]
  change CloseoutRowsCircuitHeader.middle bits (CloseoutRowsCircuitHeader.firstSlots 1)=frame bits
  rw [CloseoutRowsCircuitHeader.middle_old,CompetitorWitnessTriple.stage_stable [] bits 1 5 1 (by decide)]
  change CompetitorWitnessTriple.stage [] bits (0+1) (CompetitorWitnessTriple.slots 0 0)=frame bits
  rw [CompetitorWitnessTriple.stage,dif_pos (show 0<6 by omega)]
  exact (install_slot (CompetitorWitnessTriple.slots (0 : Fin 6))
    (CompetitorWitnessTriple.slots_injective 0) _ _ 0).trans rfl

theorem tagged_raw (bits : List Bool) : CloseoutRowsCircuitTagged.output bits 1=frame bits:=by
  rw [CloseoutRowsCircuitTagged.output,install_other _ _ _ _ (by decide),
    CloseoutRowsCircuitTagged.before_other _ _ _ (by
      intro j z;fin_cases j <;> fin_cases z <;> decide)]
  exact header_raw bits

theorem prefix_run_fields (threshold : Bool) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine threshold) (budget bits) (input bits) out ∧
      out 158=frame (codeWord bits 3) ∧
      out 297=PCPPNativeCanonicalWalk.atomStream (codeWord bits 2).length (tree (value (codeWord bits 2))).atoms ∧
      out 622=List.replicate (CloseoutRowsCircuitCount.count (codeWord bits 2)) true ∧
      out 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (codeWord bits 2)) ∧
      (readTapeBit (out 638) 0=true ↔ valid threshold bits) ∧ out 1=frame bits:=by
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
  refine ⟨_,hall,?_,?_,?_,?_,?_,?_⟩
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

  · rw [install_other _ _ _ _ (by decide),three_other _ (by decide)]
    exact (two_old 1 (by decide) (by decide)).trans (tagged_raw bits)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
