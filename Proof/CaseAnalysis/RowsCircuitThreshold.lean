import Proof.CaseAnalysis.RowsCircuitPorts

/-! Cold original circuit input reaches the existing complete threshold
top consumer. The actual serialized-bottom template is positioned once;
no arity word, initialized bank or top field is an additional input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
open CloseoutRowsCircuit CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool):=Function.update (CloseoutRowsCircuitColdEntry.heads out) 624 1
noncomputable def positioned:=Composition.machine (CloseoutRowsCircuitColdEntry.machine true)
  (CompetitorCountTable.moveMachine (624 : Fin 1703))
noncomputable def machine:=Composition.machine positioned CloseoutRowsCircuitThresholdTop.machine
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsCircuitColdEntry.budget cap bits+3+
  CloseoutRowsCircuitThresholdTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)

private theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H H' : Fin t → ℕ) (A B : Fin t → List Bool)
    (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,H,A⟩=some first)
    (ph : first.final.heads=H') (pt : first.final.tapes=B) (ps : first.steps ≤ fp)
    (hq : runFrom q fq ⟨q.start,H',B⟩=some last) (qs : last.steps ≤ fq) :
    ∃ r,runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,H,A⟩=some r ∧
      r.steps ≤ fp+1+fq ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=by
  have he:Composition.restart first.final q.start=⟨q.start,H',B⟩:=configuration_ext rfl ph pt
  have hlast:runFrom q fq (Composition.restart first.final q.start)=some last:=by rw [he];exact hq
  refine ⟨Composition.joinedReceipt first last,Composition.run_join p q fp fq _ first last hp hlast,?_,rfl,rfl⟩
  change first.steps+1+last.steps ≤ fp+1+fq
  omega

theorem gate_heads (out : List Bool) (i : Fin 1049) :
    heads out (gateSlots i)=CloseoutRowsGateMeasured.heads i:=by
  rw [CloseoutRowsGateBank.heads_eq]
  by_cases hi:i.val=1035
  · rw [if_pos hi]
    have he:gateSlots i=624:=by apply Fin.ext;rw [gate_val,if_pos hi];rfl
    rw [he];exact Function.update_self _ _ _
  · rw [if_neg hi]
    have he:gateSlots i≠624:=by
      intro h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
      rw [gate_val,if_neg hi] at hv
      change 639+i.val=624 at hv;omega
    rw [heads,Function.update_of_ne he]
    unfold CloseoutRowsCircuitColdEntry.heads CloseoutRowsCircuit.heads
    have hv:(gateSlots i).val=639+i.val:=by rw [gate_val,if_neg hi]
    split_ifs <;> first | rfl | (rename_i h;have h':=congrArg (fun k : Fin 1703=>k.val) h;rw [hv] at h';change 639+i.val=1688 at h';omega) | omega

theorem external_heads (out : List Bool) (i : Fin 7) :
    heads out (CloseoutRowsCircuitThresholdTop.external i)=0:=by
  fin_cases i <;> rfl

theorem cold_run (cap core W L : ℕ) (bits out : List Bool)
    (hin : 2*bits.length+1 ≤ cap)
    (hcap : 2*CloseoutRowsGateMeasured.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+4 ≤ cap) :
    ∃ prefixBank gateBank r,
      runFrom machine (budget cap bits)
        ⟨machine.start,CloseoutRowsCircuitColdEntry.heads out,
          CloseoutRowsCircuitColdEntry.input cap core W L bits out⟩=some r ∧
      r.steps ≤ budget cap bits ∧
      (readTapeBit (prefixBank 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid true bits) ∧
      prefixBank 297=PCPPNativeCanonicalWalk.atomStream (CloseoutRowsCircuitHeader.codeWord bits 2).length
        (PCPPNativeCanonicalTree.tree (value (CloseoutRowsCircuitHeader.codeWord bits 2))).atoms ∧
      prefixBank 622=List.replicate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) true ∧
      prefixBank 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      CloseoutRowsGateMeasured.Output true (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) gateBank ∧
      (∀ i : Fin 1049,i.val≠1035 → (CloseoutRowsGateBank.padded cap gateBank i).length ≤ cap) ∧
      (∀ g,decodeSupportedNormalizedGate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (value (CloseoutRowsCircuitHeader.codeWord bits 3))=some g →
        r.final.tapes=CloseoutRowsCircuitThresholdTop.output cap
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) gateBank g ∧
        r.final.heads=Function.update (heads out) 1689
          (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g)) ∧
      (¬(decodeSupportedNormalizedGate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (value (CloseoutRowsCircuitHeader.codeWord bits 3))).isSome →
        r.final.tapes=CloseoutRowsCircuitThresholdTop.middle cap
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) gateBank ∧
        r.final.heads=heads out):=by
  obtain ⟨bank,⟨p,hp,pt,ph,ps⟩,_top,stream,count,template,flag⟩:=
    CloseoutRowsCircuitColdEntry.cold_run true cap core W L bits out hin
  let A:=CloseoutRowsCircuitColdEntry.output cap core W L bits out bank
  obtain ⟨m,hm,mh,mt,ms⟩:=CompetitorCountTable.move_run (624 : Fin 1703)
    (CloseoutRowsCircuitColdEntry.heads out) A
  have mh':m.final.heads=heads out:=by
    rw [mh];funext i
    by_cases hi:i=624
    · subst i;rfl
    · simp only [if_neg hi,heads,Function.update_of_ne hi]
  obtain ⟨start,hstart,ss,sh,st⟩:=joined (CloseoutRowsCircuitColdEntry.machine true)
    (CompetitorCountTable.moveMachine (624 : Fin 1703)) _ _ _ _ _ _ p m hp ph pt ps hm ms.le
  have sh':start.final.heads=heads out:=sh.trans mh'
  have st':start.final.tapes=A:=st.trans mt
  have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
    (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
  obtain ⟨gates,top,toprun,tops,meaning,bounds,accepted,rejected⟩:=CloseoutRowsCircuitThresholdTop.top_run
    cap (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
    (CloseoutRowsCircuitHeader.codeWord bits 3) (heads out) A (gate_heads out)
    (CloseoutRowsCircuitColdEntry.output_gate cap core W L bits out bank _ template)
    (external_heads out) (CloseoutRowsCircuitColdEntry.output_external cap core W L bits out bank)
    (by rw [width];exact hin) hcap
  obtain ⟨actual,hr,rs,rh,rt⟩:=joined positioned CloseoutRowsCircuitThresholdTop.machine
    _ _ _ _ _ _ start top hstart sh' st' ss toprun tops
  have budgetEq:(CloseoutRowsCircuitColdEntry.budget cap bits+1+1)+1+
      CloseoutRowsCircuitThresholdTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)=budget cap bits:=by
    unfold budget;omega
  rw [budgetEq] at hr rs
  refine ⟨bank,gates,actual,hr,rs,flag,stream,count,template,meaning,bounds,?_,?_⟩
  · intro g hg;obtain ⟨gt,gh⟩:=accepted g hg
    exact ⟨rt.trans gt,rh.trans gh⟩
  · intro hn;obtain ⟨gt,gh⟩:=rejected hn
    exact ⟨rt.trans gt,rh.trans gh⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
