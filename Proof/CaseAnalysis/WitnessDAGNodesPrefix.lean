import Proof.CaseAnalysis.WitnessDAGNodesLayout

/-! The node loop's complete bank and native descriptor prefix are produced
by the cold allocation and existing header program. Their live count and
descriptor ports retain exact identities across the physical join. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
open LocalBitMultitape RecoveryRootRound RadixSemantics SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_run (w : ℕ) (arityBits source : List Bool) (flag : Bool) (count : ℕ)
    (hw : 1≤w) (hb : arityBits.length≤w) : ∃ actual,
    run prefixMachine (prefixBudget w arityBits count) (input w arityBits source flag count)=some actual ∧
      actual.steps≤prefixBudget w arityBits count ∧
      (∀ i,actual.final.heads (coreSlots i)=NodeRound.heads (nativeHeader arityBits count) 0 i) ∧
      (∀ i,actual.final.tapes (coreSlots i)=
        NodeRound.data (NodeReady.capacity w) w (binary w (value arityBits)) (binary w 0)
          [] (nativeHeader arityBits count) source flag i) ∧
      actual.final.tapes 766=CompareMachine.word count ∧ actual.final.heads 766=0:=by
  obtain ⟨hc,hfields⟩:=capacity_fields w arityBits hw
  obtain ⟨out,ho,hdata⟩:=NodeColdBank.bank_run (NodeReady.capacity w) w arityBits source flag hb hc hfields
  obtain ⟨a,ha,atape,ah,as⟩:=ho.focus bankSlots bank_injective (input w arityBits source flag count)
    (by intro i;simp only [input,bankSlots,Fin.addCases_left])
  obtain ⟨base,hbase,bs,bo,bhead,bc,bch,_,_,_,_⟩:=DAGHeader.header_run (value arityBits) count
  obtain ⟨b,hb,_,bt,bheads,btapes,bkeep⟩:=RecoveryFocus.dock headerSlots header_injective
    DAGHeader.machine _ a.final.heads a.final.tapes (initialConfiguration DAGHeader.machine (DAGHeader.input (value arityBits) count))
    (by intro j;exact ah _)
    (by intro j;rw [atape];exact header_input w arityBits source flag count out hdata j) base hbase
  have h:=Composition.run_join bank header _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤prefixBudget w arityBits count
    unfold prefixBudget
    omega
  · intro i
    change b.final.heads (coreSlots i)=_
    by_cases hi:i=747
    · subst i
      change b.final.heads (headerSlots 20)=_
      rw [bheads,bhead]
      rfl
    · rw [(bkeep _ (header_core i hi)).1,ah]
      simp [NodeRound.heads,hi]
  · intro i
    change b.final.tapes (coreSlots i)=_
    by_cases hi:i=747
    · subst i
      change b.final.tapes (headerSlots 20)=_
      rw [btapes,bo,data_output]
      rfl
    · rw [(bkeep _ (header_core i hi)).2,atape]
      change install bankSlots _ out (bankSlots (NodeColdBank.loopSlots i))=_
      rw [install_slot _ bank_injective,hdata]
      exact data_output_other _ _ _ _ _ _ _ _ _ i hi
  · exact (btapes 1).trans bc
  · exact (bheads 1).trans bch

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
