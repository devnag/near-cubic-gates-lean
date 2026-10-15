import Proof.CaseAnalysis.WitnessOracleCompare

/-! The cold counted oracle parser appends its retained canonical output
payload to the same native descriptor. Canonical and node flags remain at
head zero for the final finite acceptance transition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics SignedSortKey
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compare_outside (i : Fin tapes) (h0 : i.val≠1220) (h1 : i.val≠1221)
    (h2 : i.val≠1222) (h3 : i.val≠1223) (h4 : i.val≠548)
    (hr : i.val<1357 ∨ 1373 ≤ i.val) : ∀ j,compareSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  by_cases hj:j.val<5
  · have hh:j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4:=by omega
    rcases hh with hh|hh|hh|hh|hh <;> simp [compareSlots,hh,tapes] at hv <;> omega
  · rw [compare_high j (by omega)] at hv
    rcases hr with hr|hr <;> omega

theorem footer_val (j : Fin 9) : (footerSlots j).val=
    if j.val=0 then 548 else if j.val=1 then 415 else if j.val=8 then 1299 else 1371+j.val:=by
  unfold footerSlots
  split_ifs <;> rfl

theorem footer_outside (i : Fin tapes) (h0 : i.val≠548) (h1 : i.val≠415)
    (h8 : i.val≠1299) (hr : i.val<1373 ∨ 1379 ≤ i.val) : ∀ j,footerSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [footer_val] at hv
  split_ifs at hv <;> rcases hr with hr|hr <;> omega

theorem NodesOutput.future {x bits arityBits : List Bool} {base ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (hp : Prepared x bits arityBits base)
    (h : NodesOutput x bits arityBits base heads ts) (i : Fin tapes) (hi : 1357 ≤ i.val) :
    heads i=0 ∧ ts i=[]:=by
  obtain ⟨hh,ht⟩:=h.outside i (node_outside i (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (Or.inr hi))
  refine ⟨hh,ht.trans (hp.fresh i (by omega) ?_)⟩
  intro he
  have hv:=congrArg Fin.val he
  change i.val=1306 at hv
  omega

theorem Compared.future {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) (i : Fin tapes)
    (hi : 1373 ≤ i.val) : heads i=0 ∧ ts i=[]:=by
  obtain ⟨base,before,co,hp,hn,_,_,rfl⟩:=h
  rw [install_other _ _ _ _ (compare_outside i (by omega) (by omega) (by omega)
    (by omega) (by omega) (Or.inr hi))]
  exact hn.future hp i (by omega)

theorem Compared.descriptor {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) :
    heads 1299=(nodesDescriptor arityBits bits).length ∧ ts 1299=nodesDescriptor arityBits bits:=by
  obtain ⟨base,before,co,_,hn,_,_,rfl⟩:=h
  rw [install_other _ _ _ _ (compare_outside 1299 (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (by decide)))]
  have hh:=hn.coreHeads 747
  have ht:=hn.core 747
  change heads 1299=(nodesDescriptor arityBits bits).length at hh
  change before 1299=NodeRound.data _ _ _ _ _ _ _ _ 747 at ht
  rw [DAGNodes.data_output] at ht
  exact ⟨hh,ht⟩

theorem Compared.payload {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) :
    heads 548=0 ∧ ts 548=frame (outputPayload bits):=by
  obtain ⟨base,before,co,_,hn,_,hc,rfl⟩:=h
  have hh:heads 548=0:=(hn.outside 548 (node_outside _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)))).1
  refine ⟨hh,?_⟩
  change install compareSlots before co (compareSlots 4)=_
  rw [install_slot _ compare_injective,hc]

theorem Compared.payload_count {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) :
    heads 415=0 ∧ ts 415=CompareMachine.word (outputPayload bits).length:=by
  obtain ⟨base,before,co,hp,hn,_,_,rfl⟩:=h
  rw [install_other _ _ _ _ (compare_outside 415 (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (by decide)))]
  obtain ⟨hh,ht⟩:=hn.outside 415 (node_outside _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)))
  exact ⟨hh,ht.trans hp.payloadCount⟩

theorem footer_input {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) : ∀ i,
    ts (footerSlots i)=DAGFooter.input (outputPayload bits) (nodesDescriptor arityBits bits) i:=by
  intro i
  fin_cases i
  · exact h.payload.2
  · exact h.payload_count.2
  · exact (h.future 1373 (by decide)).2
  · exact (h.future 1374 (by decide)).2
  · exact (h.future 1375 (by decide)).2
  · exact (h.future 1376 (by decide)).2
  · exact (h.future 1377 (by decide)).2
  · exact (h.future 1378 (by decide)).2
  · exact h.descriptor.2

theorem footer_heads {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) : ∀ i,
    heads (footerSlots i)=DAGFooter.heads (nodesDescriptor arityBits bits) i:=by
  intro i
  fin_cases i
  · exact h.payload.1
  · exact h.payload_count.1
  · exact (h.future 1373 (by decide)).1
  · exact (h.future 1374 (by decide)).1
  · exact (h.future 1375 (by decide)).1
  · exact (h.future 1376 (by decide)).1
  · exact (h.future 1377 (by decide)).1
  · exact (h.future 1378 (by decide)).1
  · exact h.descriptor.1

def descriptor (arityBits bits : List Bool):=
  nodesDescriptor arityBits bits++NativeWord.word (outputPayload bits)
noncomputable def described:=Composition.machine comparedNodes footer
def describedBudget (x bits arityBits : List Bool):=
  compareBudget x bits arityBits+1+(10*(outputPayload bits).length+28)
def Described (x bits arityBits : List Bool) (heads : Fin tapes→ℕ) (ts : Fin tapes→List Bool) : Prop:=
  ∃ beforeHeads before,Compared x bits arityBits beforeHeads before ∧
    heads 1299=(descriptor arityBits bits).length ∧ ts 1299=descriptor arityBits bits ∧
    ∀ i,(∀ j,footerSlots j≠i) → heads i=beforeHeads i ∧ ts i=before i

theorem described_cold_run (x bits arityBits : List Bool) (hN : 2 ≤ x.length)
    (hcap : 16*bits.length ≤ x.length) (hb : arityBits.length ≤ x.length+1) : ∃ actual,
    run described (describedBudget x bits arityBits) (input x bits arityBits)=some actual ∧
      actual.steps ≤ describedBudget x bits arityBits ∧
      Described x bits arityBits actual.final.heads actual.final.tapes:=by
  obtain ⟨c,hc,cs,cout⟩:=compare_cold_run x bits arityBits hN hcap hb
  obtain ⟨localRun,hl,ls,lt,lh⟩:=DAGFooter.footer_run (outputPayload bits) (nodesDescriptor arityBits bits)
  obtain ⟨a,ha,_,asteps,ah,atape,outside⟩:=RecoveryFocus.dock footerSlots footer_injective DAGFooter.machine _
    c.final.heads c.final.tapes (DAGFooter.entry (outputPayload bits) (nodesDescriptor arityBits bits))
    (footer_heads cout) (footer_input cout) localRun hl
  have hall:=Composition.run_join comparedNodes footer _ _ _ c a hc ha
  refine ⟨Composition.joinedReceipt c a,hall,?_,?_⟩
  · change c.steps+1+a.steps ≤ describedBudget x bits arityBits
    unfold describedBudget
    omega
  rw [PCPTripleGlobal.joined_heads,PCPTripleGlobal.joined_tapes]
  refine ⟨c.final.heads,c.final.tapes,cout,?_,?_,outside⟩
  · exact (ah 8).trans lh
  · exact (atape 8).trans lt

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
