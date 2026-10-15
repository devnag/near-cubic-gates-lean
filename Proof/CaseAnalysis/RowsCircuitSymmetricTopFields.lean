import Proof.CaseAnalysis.RowsCircuitPrefixFields
import Proof.CaseAnalysis.RowsCircuitSymmetric

/-! Retain the same symmetric top parser flag in its original whole
parser-and-publication receipt. No instruction, copy or traversal changes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem top_run_fields (cap m : ℕ) (bits : List Bool) (H : Fin 1703→ℕ) (A : Fin 1703→List Bool)
    (hh : ∀ i,H (slots i)=0)
    (ha : ∀ i,A (slots i)=padded cap (CloseoutRowsCircuitSymTop.input m bits) i)
    (eh : ∀ i,H (external i)=0) (ea : ∀ i,A (external i)=externalData cap m i)
    (hin : 2*bits.length+1≤cap) (hcap : CloseoutRowsCircuitSymTop.budget bits+1≤cap)
    (hm : m≤cap) (hc : 2≤cap) : ∃ bank result,
    ReadyAt machine (budget cap bits) H A result ∧
      bank 174=frame (BitFields.payload bits) ∧ bank 178=UnaryTemplate.tape m ∧
      (∀ i : Fin 181,i.val≠178 → (padded cap bank i).length≤cap) ∧
      (readTapeBit (bank 179) 0=true ↔ CloseoutRowsCircuitSymTop.valid m bits) ∧
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
    exact ⟨bank,_,all,table,count,bounds,flag,fun _=>rfl,fun hn=>False.elim (hn valid)⟩
  · have no:=CloseoutRowsGatePairHeads.rejected parser publisher (fun b=>b 1676) _ H A _ first
      (Bool.eq_false_iff.mpr (fun h=>valid (flag'.mp h)))
    exact ⟨bank,_,enlarge _ _ (budget cap bits) _ _ _ no (by unfold budget;omega),table,count,bounds,flag,
      fun hv=>False.elim (valid hv),fun _=>rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
