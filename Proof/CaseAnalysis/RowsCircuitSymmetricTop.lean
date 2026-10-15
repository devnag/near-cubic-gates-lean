import Proof.CaseAnalysis.RowsCircuitThresholdTop
import Proof.CaseAnalysis.RowsCircuitSymTop

/-! Total symmetric top check and publication at the frozen circuit ports.
The actual bottom count is copied once; the Boolean table is never parsed
again and the original domain template remains available for the loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 181) : Fin 1703:=
  if i.val=0 then 640 else if i.val=1 then 639 else if i.val=178 then 624 else
    if i.val=179 then 1676 else if i.val=180 then 1687 else ⟨639+i.val,by omega⟩
def publishSlots : Fin 12→Fin 1703:=![813,1691,1680,1684,622,1694,1695,1701,1692,1702,1689,1696]
def external : Fin 11→Fin 1703:=![1691,1680,1684,622,1694,1695,1701,1692,1702,1689,1696]
def externalData (cap m : ℕ) : Fin 11→List Bool:=
  ![List.replicate cap false,List.replicate cap false,List.replicate cap false,List.replicate m true,
    List.replicate cap true,List.replicate (cap+1) false,List.replicate cap false,
    List.replicate cap false,List.replicate cap false,[],List.replicate cap false]
def pads (cap : ℕ) (i : Fin 181):=if i.val=178 then 0 else cap
def padded (cap : ℕ) (A : Fin 181→List Bool) (i : Fin 181):=ZeroPadding.pad (pads cap i) (A i)
def sources (cap m : ℕ) (bits : List Bool) : Fin 3→List Bool:=
  ![ZeroPadding.pad cap (frame (BitFields.payload bits)),List.replicate cap false,List.replicate m true]
noncomputable def parser:=RecoveryFocus.machine slots CloseoutRowsCircuitSymTop.machine
noncomputable def publisher:=RecoveryFocus.machine publishSlots CloseoutRowsCircuitTopPublish.machine
noncomputable def machine:=CloseoutRowsGateColdPair.machine parser publisher (fun b=>b 1676)
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsCircuitSymTop.budget bits+8*cap+22
noncomputable def middle (cap : ℕ) (A : Fin 1703→List Bool) (bank : Fin 181→List Bool):=
  install slots A (padded cap bank)
noncomputable def output (cap m : ℕ) (bits : List Bool) (A : Fin 1703→List Bool) (bank : Fin 181→List Bool):=
  install publishSlots (middle cap A bank) (CloseoutRowsCircuitTopPublish.output cap 0 0 (sources cap m bits))

theorem slots_val (i : Fin 181) : (slots i).val=
    if i.val=0 then 640 else if i.val=1 then 639 else if i.val=178 then 624 else
      if i.val=179 then 1676 else if i.val=180 then 1687 else 639+i.val:=by
  unfold slots;split_ifs <;> rfl
theorem slots_injective : Function.Injective slots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [slots_val,slots_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega
theorem external_outside (i : Fin 11) : ∀ j,slots j≠external i:=by
  have range:(external i).val=622 ∨ 1680 ≤ (external i).val ∧ (external i).val≠1687:=by
    fin_cases i <;> decide
  intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [slots_val] at hv;split_ifs at hv <;> omega
theorem publish_injective : Function.Injective publishSlots:=by decide

theorem input_eq (m : ℕ) (bits : List Bool) (i : Fin 181) : CloseoutRowsCircuitSymTop.input m bits i=
    if i.val=178 then UnaryTemplate.tape m else if i.val=0 then frame bits else []:=by
  refine Fin.addCases (m:=178) (n:=3) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsCircuitSymTop.input,Fin.addCases_left,Fin.val_castAdd,
      if_neg (show j.val≠178 by omega)]
    refine Fin.addCases (m:=174) (n:=4) ?_ ?_ j
    · intro k
      simp only [NatCold.input,Fin.addCases_left,Fin.val_castAdd]
      rfl
    · intro k
      simp only [NatCold.input,Fin.addCases_right,Fin.val_natAdd,
        if_neg (show 174+k.val≠0 by omega)]
  · intro j;fin_cases j <;> rfl

theorem padded_run (cap m : ℕ) (bits : List Bool) (hin : 2*bits.length+1≤cap)
    (hcap : CloseoutRowsCircuitSymTop.budget bits+1≤cap) : ∃ bank,
    ClockJoin.ReadyRun CloseoutRowsCircuitSymTop.machine (CloseoutRowsCircuitSymTop.budget bits)
      (padded cap (CloseoutRowsCircuitSymTop.input m bits)) (padded cap bank) ∧
      bank 174=frame (BitFields.payload bits) ∧ bank 178=UnaryTemplate.tape m ∧
      (readTapeBit (bank 179) 0=true ↔ CloseoutRowsCircuitSymTop.valid m bits) ∧
      ∀ i : Fin 181,i.val≠178 → (padded cap bank i).length≤cap:=by
  obtain ⟨bank,⟨base,hbase,bt,bh,bs⟩,table,count,flag⟩:=CloseoutRowsCircuitSymTop.top_run m bits
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CloseoutRowsCircuitSymTop.machine (pads cap) _ _ base hbase
  refine ⟨bank,⟨r,hr,?_,?_,rs ▸ bs⟩,table,count,flag,?_⟩
  · rw [rf];change (fun i=>ZeroPadding.pad (pads cap i) (base.final.tapes i))=_
    rw [bt];rfl
  · intro i;rw [rf];exact bh i
  · intro i hi
    have bound:=PCPSerializerReuse.tape_support CloseoutRowsCircuitSymTop.machine _ _ r hr i cap 0 (by rfl)
      (by
        change (padded cap (CloseoutRowsCircuitSymTop.input m bits) i).length ≤ max cap (0+1)
        simp only [padded,ZeroPadding.pad_length,input_eq,pads,if_neg hi]
        apply max_le
        · exact Nat.le_max_left _ _
        · split_ifs
          · exact (frame_length bits ▸ hin).trans (Nat.le_max_left _ _)
          · exact Nat.zero_le _)
    rw [rf,rs] at bound
    change (ZeroPadding.pad (pads cap i) (base.final.tapes i)).length≤_ at bound
    rw [bt] at bound
    simpa only [padded,Nat.max_eq_left (by omega : 0+base.steps+1≤cap)] using bound

theorem top_run (cap m : ℕ) (bits : List Bool) (H : Fin 1703→ℕ) (A : Fin 1703→List Bool)
    (hh : ∀ i,H (slots i)=0)
    (ha : ∀ i,A (slots i)=padded cap (CloseoutRowsCircuitSymTop.input m bits) i)
    (eh : ∀ i,H (external i)=0) (ea : ∀ i,A (external i)=externalData cap m i)
    (hin : 2*bits.length+1≤cap) (hcap : CloseoutRowsCircuitSymTop.budget bits+1≤cap)
    (hm : m≤cap) (hc : 2≤cap) : ∃ bank result,
    ReadyAt machine (budget cap bits) H A result ∧
      bank 174=frame (BitFields.payload bits) ∧ bank 178=UnaryTemplate.tape m ∧
      (∀ i : Fin 181,i.val≠178 → (padded cap bank i).length≤cap) ∧
      (CloseoutRowsCircuitSymTop.valid m bits → result=output cap m bits A bank) ∧
      (¬CloseoutRowsCircuitSymTop.valid m bits → result=middle cap A bank):=by
  obtain ⟨bank,hb,table,count,flag,bounds⟩:=padded_run cap m bits hin hcap
  obtain ⟨r,hr,rh,rt,rs⟩:=hb.focus_at slots slots_injective H A ha hh
  have first:ReadyAt parser (CloseoutRowsCircuitSymTop.budget bits) H A (middle cap A bank):=⟨r,hr,rt,rh,rs⟩
  have get (j : Fin 181):middle cap A bank (slots j)=padded cap bank j:=install_slot slots slots_injective _ _ j
  have ext (j : Fin 11):middle cap A bank (external j)=externalData cap m j:=
    (install_other _ _ _ _ (external_outside j)).trans (ea j)
  have flag':readTapeBit (middle cap A bank 1676) (H 1676)=true ↔ CloseoutRowsCircuitSymTop.valid m bits:=by
    rw [show H 1676=0 from hh 179]
    change readTapeBit (middle cap A bank (slots 179)) 0=true ↔_
    rw [get,padded,ZeroPadding.read_pad];exact flag
  by_cases valid:CloseoutRowsCircuitSymTop.valid m bits
  · have hs:∀ j,(sources cap m bits j).length≤cap:=by
      intro j;fin_cases j
      · have ht:=bounds 174 (by decide);change (ZeroPadding.pad cap (bank 174)).length≤cap at ht
        rw [table] at ht;exact ht
      · change (List.replicate cap false).length ≤ cap
        exact List.length_replicate.le
      · change (List.replicate m true).length ≤ cap
        simpa only [List.length_replicate] using hm
    obtain ⟨p,hp,ps,ph,pt⟩:=CloseoutRowsCircuitTopPublish.publish_run cap 0 0 (sources cap m bits) hs hc
    have publicationReady:ClockJoin.ReadyRun CloseoutRowsCircuitTopPublish.machine (8*cap+20)
        (CloseoutRowsCircuitTopPublish.bank cap 0 0 (sources cap m bits) 0)
        (CloseoutRowsCircuitTopPublish.output cap 0 0 (sources cap m bits)):=
      ⟨p,hp,pt,by intro i;rw [ph];simp [CloseoutRowsCircuitTopPublish.heads],ps⟩
    have inputCopy:∀ i,middle cap A bank (publishSlots i)=
        CloseoutRowsCircuitTopPublish.bank cap 0 0 (sources cap m bits) 0 i:=by
      intro i;fin_cases i
      · change middle cap A bank (slots 174)=_
        rw [get];change ZeroPadding.pad cap (bank 174)=_;rw [table];rfl
      · exact ext 0
      · change middle cap A bank (external 1)=ZeroPadding.pad cap []
        rw [ext];change List.replicate cap false=ZeroPadding.pad cap []
        simp [ZeroPadding.pad]
      · change middle cap A bank (external 2)=ZeroPadding.pad cap []
        rw [ext];change List.replicate cap false=ZeroPadding.pad cap []
        simp [ZeroPadding.pad]
      · exact ext 3
      · exact ext 4
      · exact ext 5
      · exact ext 6
      · exact ext 7
      · exact ext 8
      · exact ext 9
      · exact ext 10
    have headCopy:∀ i,H (publishSlots i)=0:=by
      intro i;fin_cases i
      · exact hh 174
      · exact eh 0
      · exact eh 1
      · exact eh 2
      · exact eh 3
      · exact eh 4
      · exact eh 5
      · exact eh 6
      · exact eh 7
      · exact eh 8
      · exact eh 9
      · exact eh 10
    obtain ⟨q,hq,qh,qt,qs⟩:=publicationReady.focus_at publishSlots publish_injective H (middle cap A bank) inputCopy headCopy
    have second:ReadyAt publisher (8*cap+20) H (middle cap A bank) (output cap m bits A bank):=⟨q,hq,qt,qh,qs⟩
    have all:=CloseoutRowsGatePairHeads.joined parser publisher (fun b=>b 1676) _ _ H A _ _ first second (flag'.mpr valid)
    have hf:CloseoutRowsCircuitSymTop.budget bits+1+(8*cap+20)+1=budget cap bits:=by unfold budget;omega
    rw [hf] at all
    exact ⟨bank,_,all,table,count,bounds,fun _=>rfl,fun hn=>False.elim (hn valid)⟩
  · have no:=CloseoutRowsGatePairHeads.rejected parser publisher (fun b=>b 1676) _ H A _ first
      (Bool.eq_false_iff.mpr (fun h=>valid (flag'.mp h)))
    exact ⟨bank,_,enlarge _ _ (budget cap bits) _ _ _ no (by unfold budget;omega),table,count,bounds,
      fun hv=>False.elim (valid hv),fun _=>rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
