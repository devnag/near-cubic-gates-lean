import Proof.CaseAnalysis.WitnessOracleNodes
import Proof.PCP.PCPTripleGlobalLayout

/-! The output address is compared against the retained final node counter.
The same payload frame then feeds the native footer; no padded-field copy or
additional canonical traversal is introduced at this enclosing join. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics SignedSortKey
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputPayload (bits : List Bool):=BitFields.payload (PCPPNativeCanonical.outputWord bits)

theorem payload_bound (bits : List Bool) : (outputPayload bits).length ≤ bits.length+1:=by
  have h:=Reencode.count_bound (PCPPNativeCanonical.outputWord bits)
  simpa only [outputPayload,BitFields.payload,Reencode.fields,List.length_map,TraversalCounted.count,
    DAGFields.output_word_length] using h

theorem NodesOutput.common {x bits arityBits : List Bool} {base ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : NodesOutput x bits arityBits base heads ts) (j : Fin 4) :
    ts (nodeSlots (DAGNodes.coreSlots ((NodeGuard.common j).castAdd 9)))=
      ZeroPadding.pad (NodeReady.capacity (x.length+1))
        (NodeGuard.shared (x.length+1) (binary (x.length+1) (value arityBits))
          (binary (x.length+1) (DAGChecks.words bits).length) j):=by
  rw [h.core]
  rw [show (NodeGuard.common j).castAdd 9=NodeRound.nodeSlots ((NodeGuard.common j).castAdd 3) by rfl,
    NodeRound.data_node,NodeReady.entry_common]

theorem NodesOutput.common_head {x bits arityBits : List Bool} {base ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : NodesOutput x bits arityBits base heads ts) (j : Fin 4) :
    heads (nodeSlots (DAGNodes.coreSlots ((NodeGuard.common j).castAdd 9)))=0:=by
  rw [h.coreHeads]
  have h747:(NodeGuard.common j).castAdd 9≠(747 : Fin 755):=by
    intro he
    have hv:=congrArg Fin.val he
    change 668+j.val=747 at hv
    omega
  have h751:(NodeGuard.common j).castAdd 9≠(751 : Fin 755):=by
    intro he
    have hv:=congrArg Fin.val he
    change 668+j.val=751 at hv
    omega
  simp only [NodeRound.heads,if_neg h747,if_neg h751]

theorem compare_high (i : Fin 21) (hi : 5 ≤ i.val) : (compareSlots i).val=1352+i.val:=by
  simp only [compareSlots,dif_neg (show ¬i.val<5 by omega)]

theorem compare_payload (cap w : ℕ) (left right bits : List Bool) :
    DAGOutput.input cap w left right bits 4=frame bits:=by
  change ZeroPadding.pad 0 (frame bits)=frame bits
  exact ZeroPadding.pad_zero _

theorem compare_heads {x bits arityBits : List Bool} {base ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : NodesOutput x bits arityBits base heads ts) :
    ∀ i,heads (compareSlots i)=0:=by
  intro i
  refine Fin.addCases (m:=5) (n:=16) ?_ ?_ i
  · intro j
    fin_cases j
    · exact h.common_head 0
    · exact h.common_head 1
    · exact h.common_head 2
    · exact h.common_head 3
    · exact (h.outside 548 (node_outside _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (Or.inl (by decide)))).1
  · intro j
    have hj:5 ≤ (j.natAdd 5).val:=by simp
    have hv:=compare_high (j.natAdd 5) hj
    exact (h.outside _ (node_outside _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)))).1

theorem compare_input {x bits arityBits : List Bool} {base ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (hp : Prepared x bits arityBits base)
    (h : NodesOutput x bits arityBits base heads ts) : ∀ i,
    ts (compareSlots i)=DAGOutput.input (NodeReady.capacity (x.length+1)) (x.length+1)
      (binary (x.length+1) (value arityBits)) (binary (x.length+1) (DAGChecks.words bits).length)
      (outputPayload bits) i:=by
  intro i
  refine Fin.addCases (m:=5) (n:=16) ?_ ?_ i
  · intro j
    fin_cases j
    · exact h.common 0
    · exact h.common 1
    · exact h.common 2
    · exact h.common 3
    · have ht:ts 548=base 548:=(h.outside 548 (node_outside _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (Or.inl (by decide)))).2
      change ts (compareSlots 4)=DAGOutput.input _ _ _ _ _ 4
      rw [compare_payload]
      exact ht.trans hp.payload
  · intro j
    have hj:5 ≤ (j.natAdd 5).val:=by simp
    have hv:=compare_high (j.natAdd 5) hj
    rw [(h.outside _ (node_outside _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inr (by omega)))).2]
    rw [hp.fresh _ (by omega) (by
      intro he
      have hh:=congrArg Fin.val he
      rw [hv] at hh
      change 1352+(j.natAdd 5).val=1306 at hh
      omega)]
    fin_cases j <;> rfl

noncomputable def comparedNodes:=Composition.machine parsedNodes compare
def compareBudget (x bits arityBits : List Bool):=nodesBudget x bits arityBits+1+NodeScalar.budget (x.length+1)
def Compared (x bits arityBits : List Bool) (heads : Fin tapes→ℕ) (ts : Fin tapes→List Bool) : Prop:=
  ∃ base before localOutput,Prepared x bits arityBits base ∧ NodesOutput x bits arityBits base heads before ∧
    localOutput 19=[decide ((DAGChecks.words bits).length ≤ DAGChecks.output bits)] ∧
    localOutput 4=frame (outputPayload bits) ∧ ts=install compareSlots before localOutput

theorem compare_cold_run (x bits arityBits : List Bool) (hN : 2 ≤ x.length)
    (hcap : 16*bits.length ≤ x.length) (hb : arityBits.length ≤ x.length+1) : ∃ actual,
    run comparedNodes (compareBudget x bits arityBits) (input x bits arityBits)=some actual ∧
      actual.steps ≤ compareBudget x bits arityBits ∧
      Compared x bits arityBits actual.final.heads actual.final.tapes:=by
  obtain ⟨base,hbase,n,hn,ns,nout⟩:=nodes_cold_run x bits arityBits hN hcap hb
  have hp:(outputPayload bits).length ≤ x.length+1:=by have h:=payload_bound bits;omega
  obtain ⟨co,hco,cflag,ckeep⟩:=DAGOutput.compare_run (NodeReady.capacity (x.length+1)) (x.length+1)
    (binary (x.length+1) (value arityBits)) (binary (x.length+1) (DAGChecks.words bits).length)
    (outputPayload bits) (binary_length _ _) (binary_length _ _) hp
  obtain ⟨c,hc,ch,ct,cs⟩:=hco.focus_at compareSlots compare_injective n.final.heads n.final.tapes
    (compare_input hbase nout) (compare_heads nout)
  have hall:=Composition.run_join parsedNodes compare _ _ _ n c hn hc
  refine ⟨Composition.joinedReceipt n c,hall,?_,?_⟩
  · change n.steps+1+c.steps ≤ compareBudget x bits arityBits
    unfold compareBudget
    omega
  rw [PCPTripleGlobal.joined_heads,PCPTripleGlobal.joined_tapes,ch,ct]
  refine ⟨base,n.final.tapes,co,hbase,nout,?_,?_,rfl⟩
  · obtain ⟨_,_,hcount⟩:=DAGBounds.guarded_fields x.length bits hN hcap
    rw [binary_value _ _ hcount] at cflag
    exact cflag
  · simpa only [show (4 : Fin 5).castAdd 16=(4 : Fin 21) by rfl,compare_payload] using ckeep 4

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
