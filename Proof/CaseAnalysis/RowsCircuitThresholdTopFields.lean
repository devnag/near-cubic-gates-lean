import Proof.CaseAnalysis.RowsCircuitThresholdFields

/-! Expose the SAME accepted threshold-top bitmap through its complete
parser/publication receipt, so the bottom loop preserves retained order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem focused_fields {t u s : ℕ} (p : Machine t s) (slots : Fin t→Fin u)
    (hi : Function.Injective slots) (fuel : ℕ) (h : Fin t→ℕ) (a b : Fin t→List Bool)
    (run : ReadyAt p fuel h a b) (H : Fin u→ℕ) (A : Fin u→List Bool)
    (hh : ∀ i,H (slots i)=h i) (ht : ∀ i,A (slots i)=a i) :
    ReadyAt (RecoveryFocus.machine slots p) fuel H A (install slots A b):=by
  classical
  obtain ⟨base,hbase,bt,bh,bs⟩:=run
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots hi p fuel H A _ hh ht base hbase
  refine ⟨r,hr,?_,?_,rs ▸ bs⟩
  · funext i
    by_cases hx:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hx;rw [rt,bt,install_slot slots hi]
    · rw [install_other _ _ _ _ (by simpa only [not_exists] using hx)]
      exact (keep i (by simpa only [not_exists] using hx)).2
  · funext i
    by_cases hx:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hx;rw [rh,bh,hh]
    · exact (keep i (by simpa only [not_exists] using hx)).1

theorem top_run_fields (cap core : ℕ) (bits : List Bool) (H : Fin 1703→ℕ) (A : Fin 1703→List Bool)
    (hh : ∀ i,H (gateSlots i)=CloseoutRowsGateMeasured.heads i)
    (ha : ∀ i,A (gateSlots i)=CloseoutRowsGateBank.input cap core bits i)
    (eh : ∀ i,H (external i)=0) (ea : ∀ i,A (external i)=externalData cap i)
    (hin : 2*bits.length+1≤cap) (hcap : 2*CloseoutRowsGateMeasured.budget bits+4≤cap) :
    ∃ bank r,runFrom machine (budget cap bits) (RecoveryCalls.restarted machine H A)=some r ∧
      r.steps≤budget cap bits ∧ CloseoutRowsGateMeasured.Output true core bits bank ∧
      (∀ i : Fin 1049,i.val≠1035 → (CloseoutRowsGateBank.padded cap bank i).length≤cap) ∧
      (∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
        CloseoutRowsGateBank.padded cap bank 994=ZeroPadding.pad cap (frame (CloseoutRowsGateSupport.gateMembers g.support))) ∧
      (∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
        r.final.tapes=output cap A bank g ∧ r.final.heads=Function.update H 1689 (weights g+theta g)) ∧
      (¬(decodeSupportedNormalizedGate core (value bits)).isSome →
        r.final.tapes=middle cap A bank ∧ r.final.heads=H):=by
  obtain ⟨bank,gate,meaning,bounds⟩:=CloseoutRowsGateBank.gate_run true cap core bits hin (by omega)
  have bitmap : ∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
      CloseoutRowsGateBank.padded cap bank 994=ZeroPadding.pad cap (frame (CloseoutRowsGateSupport.gateMembers g.support)):=by
    intro g hg
    exact CloseoutRowsGateBank.bitmap_retained true cap bits g hg _ (CloseoutRowsGateBank.padded cap bank) gate
  have hp:=focused_fields (CloseoutRowsGateMeasured.machine true) gateSlots gate_injective _ _ _ _ gate H A hh ha
  have hflag:readTapeBit (middle cap A bank 1676) (H 1676)=true ↔
      (decodeSupportedNormalizedGate core (value bits)).isSome:=by
    have hc:=hh 1037
    change H 1676=0 at hc
    rw [hc]
    change readTapeBit (middle cap A bank (gateSlots 1037)) 0=true ↔_
    rw [middle,install_slot gateSlots gate_injective]
    change readTapeBit (ZeroPadding.pad cap (bank 1037)) 0=true ↔_
    rw [ZeroPadding.read_pad]
    exact meaning.2.1
  by_cases hd:(decodeSupportedNormalizedGate core (value bits)).isSome
  · obtain ⟨g,hg⟩:=Option.isSome_iff_exists.mp hd
    have hab:weights g+theta g+2≤cap:=(CloseoutRowsCircuitBottom.gate_counter_bounds g bits hg).1.trans hcap
    have hs:∀ j,(sources cap bank j).length≤cap:=by
      intro j;fin_cases j;exact bounds 1033 (by decide);exact bounds 994 (by decide);exact bounds 1047 (by decide)
    obtain ⟨p,hp0,ps,ph,pt⟩:=CloseoutRowsCircuitTopPublish.publish_run cap (weights g) (theta g) (sources cap bank) hs hab
    obtain ⟨q,hq,_qf,qs,qh,qt,keep⟩:=RecoveryFocus.dock topPublishSlots topPublish_injective
      CloseoutRowsCircuitTopPublish.machine _ H (middle cap A bank) _
      (publish_heads H hh eh) (publish_input cap bits bank g hg meaning A ea) p hp0
    have qT:q.final.tapes=output cap A bank g:=by
      classical
      funext i
      by_cases hx:∃ j,topPublishSlots j=i
      · obtain ⟨j,rfl⟩:=hx;rw [qt,pt,output,install_slot topPublishSlots topPublish_injective]
      · rw [output,install_other _ _ _ _ (by simpa only [not_exists] using hx)]
        exact (keep i (by simpa only [not_exists] using hx)).2
    have qH:q.final.heads=Function.update H 1689 (weights g+theta g):=by
      classical
      funext i
      by_cases hx:∃ j,topPublishSlots j=i
      · obtain ⟨j,rfl⟩:=hx;rw [qh,ph]
        have hpH:=publish_heads H hh eh j
        fin_cases j <;> simp [CloseoutRowsCircuitTopPublish.heads,topPublishSlots]
        all_goals exact hpH.symm
      · rw [Function.update_of_ne (by intro he;exact hx ⟨10,he.symm⟩)]
        exact (keep i (by simpa only [not_exists] using hx)).1
    obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsGateSourceCalls.joined parser publish (fun b=>b 1676)
      _ _ H A (middle cap A bank) hp q hq (hflag.mpr hd)
    have hfuel:CloseoutRowsGateMeasured.budget bits+1+CloseoutRowsCircuitTopPublish.budget cap+1=budget cap bits:=by
      unfold budget CloseoutRowsCircuitTopPublish.budget;omega
    rw [hfuel] at hr rs
    refine ⟨bank,r,?_,?_,meaning,bounds,bitmap,?_,fun hn=>False.elim (hn hd)⟩
    · exact hr
    · exact rs
    · intro g' hg';have he:g'=g:=Option.some.inj (hg'.symm.trans hg);subst g'
      exact ⟨rt.trans qT,rh.trans qH⟩
  · have hf:=Bool.eq_false_iff.mpr (fun ht=>hd (hflag.mp ht))
    have no:=CloseoutRowsGatePairHeads.rejected parser publish (fun b=>b 1676) _ H A (middle cap A bank) hp hf
    obtain ⟨r,hr,rt,rh,rs⟩:=enlarge _ _ (budget cap bits) _ _ _ no (by unfold budget;omega)
    refine ⟨bank,r,hr,rs,meaning,bounds,bitmap,?_,fun _=>⟨rt,rh⟩⟩
    intro g hg;exact False.elim (hd (by rw [hg];rfl))

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop
