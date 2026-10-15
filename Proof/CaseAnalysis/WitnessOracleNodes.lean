import Proof.CaseAnalysis.WitnessOraclePrepare

/-! The cold preparation feeds the complete counted node execution. This
consumer supplies its own polynomial bank, fixed-width metadata, native
header and validity seed; its caller supplies only the actual raw inputs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics SignedSortKey
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_nodes (x bits arityBits : List Bool) (ts : Fin tapes→List Bool)
    (h : Prepared x bits arityBits ts) : ∀ i,
    ts (nodeSlots i)=DAGNodes.input (x.length+1) arityBits
      ((DAGChecks.words bits).flatMap frame) true (DAGChecks.words bits).length i:=by
  intro i
  rw [node_input_shape]
  by_cases h749:i.val=749
  · rw [if_pos h749,show nodeSlots i=63 by simp [nodeSlots,h749]]
    exact h.capacity
  by_cases h751:i.val=751
  · rw [if_neg h749,if_pos h751,show nodeSlots i=231 by simp [nodeSlots,h751]]
    exact h.stream
  by_cases h754:i.val=754
  · rw [if_neg h749,if_neg h751,if_pos h754,
      show nodeSlots i=1306 by apply Fin.ext;simp [nodeSlots,h754,tapes]]
    exact h.flag
  by_cases h756:i.val=756
  · rw [if_neg h749,if_neg h751,if_neg h754,if_pos h756,show nodeSlots i=11 by simp [nodeSlots,h756]]
    exact h.width
  by_cases h759:i.val=759
  · rw [if_neg h749,if_neg h751,if_neg h754,if_neg h756,if_pos h759,
      show nodeSlots i=2 by simp [nodeSlots,h759]]
    exact h.arity
  by_cases h766:i.val=766
  · rw [if_neg h749,if_neg h751,if_neg h754,if_neg h756,if_neg h759,if_pos h766,
      show nodeSlots i=242 by simp [nodeSlots,h766]]
    exact h.count
  by_cases h767:i.val=767
  · rw [if_neg h749,if_neg h751,if_neg h754,if_neg h756,if_neg h759,if_neg h766,if_pos h767,
      show nodeSlots i=3 by simp [nodeSlots,h767]]
    exact h.rawArity
  rw [if_neg h749,if_neg h751,if_neg h754,if_neg h756,if_neg h759,if_neg h766,if_neg h767]
  have hv:(nodeSlots i).val=552+i.val:=by
    rw [node_val,if_neg h749,if_neg h751,if_neg h756,if_neg h759,if_neg h766,if_neg h767]
  exact h.fresh _ (by omega) (by
    intro he
    have hh:=congrArg Fin.val he
    rw [hv] at hh
    change 552+i.val=1306 at hh
    omega)

theorem node_outside (i : Fin tapes) (h63 : i.val≠63) (h231 : i.val≠231)
    (h11 : i.val≠11) (h2 : i.val≠2) (h242 : i.val≠242) (h3 : i.val≠3)
    (hr : i.val<552 ∨ 1357 ≤ i.val) : ∀ j,nodeSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [node_val] at hv
  split_ifs at hv <;> rcases hr with hr|hr <;> omega

def nodesDescriptor (arityBits bits : List Bool):=
  DAGNodes.nativeHeader arityBits (DAGChecks.words bits).length++
    (DAGChecks.words bits).flatMap DAGMeaning.emitted
noncomputable def parsedNodes:=Composition.machine prepare nodes
def nodesBudget (x bits arityBits : List Bool):=
  prepareBudget x bits+1+DAGNodes.budget (x.length+1) arityBits (DAGChecks.words bits).length

structure NodesOutput (x bits arityBits : List Bool) (base : Fin tapes→List Bool)
    (heads : Fin tapes→ℕ) (ts : Fin tapes→List Bool) : Prop where
  coreHeads : ∀ i,heads (nodeSlots (DAGNodes.coreSlots i))=
    NodeRound.heads (nodesDescriptor arityBits bits) ((DAGChecks.words bits).flatMap frame).length i
  core : ∀ i,ts (nodeSlots (DAGNodes.coreSlots i))=
    NodeRound.data (NodeReady.capacity (x.length+1)) (x.length+1)
      (binary (x.length+1) (value arityBits)) (binary (x.length+1) (DAGChecks.words bits).length)
      [] (nodesDescriptor arityBits bits) ((DAGChecks.words bits).flatMap frame)
      (NodeLoop.validity (value (binary (x.length+1) (value arityBits))) true
        (DAGChecks.words bits) (DAGChecks.words bits).length) i
  outside : ∀ i,(∀ j,nodeSlots j≠i) → heads i=0 ∧ ts i=base i

theorem nodes_cold_run (x bits arityBits : List Bool) (hN : 2 ≤ x.length)
    (hcap : 16*bits.length ≤ x.length) (hb : arityBits.length ≤ x.length+1) :
    ∃ base,Prepared x bits arityBits base ∧ ∃ actual,
      run parsedNodes (nodesBudget x bits arityBits) (input x bits arityBits)=some actual ∧
      actual.steps ≤ nodesBudget x bits arityBits ∧
      NodesOutput x bits arityBits base actual.final.heads actual.final.tapes:=by
  obtain ⟨base,⟨p,hp,pt,ph,ps⟩,hprep⟩:=prepare_run x bits arityBits
  obtain ⟨_,hwords,hcount⟩:=DAGBounds.guarded_fields x.length bits hN hcap
  obtain ⟨localRun,hl,ls,lh,lt,_,_⟩:=DAGNodes.nodes_run (x.length+1) arityBits true
    (DAGChecks.words bits) (by omega) hb hwords hcount
  obtain ⟨a,ha,_,asteps,ah,atape,outside⟩:=RecoveryFocus.dock nodeSlots node_injective DAGNodes.machine _
    p.final.heads p.final.tapes (initialConfiguration DAGNodes.machine
      (DAGNodes.input (x.length+1) arityBits ((DAGChecks.words bits).flatMap frame)
        true (DAGChecks.words bits).length))
    (by intro i;exact ph _) (by intro i;rw [pt];exact prepared_nodes x bits arityBits base hprep i)
    localRun hl
  have hall:=Composition.run_join prepare nodes _ _ _ p a hp ha
  refine ⟨base,hprep,Composition.joinedReceipt p a,hall,?_,?_⟩
  · change p.steps+1+a.steps ≤ nodesBudget x bits arityBits
    unfold nodesBudget
    omega
  constructor
  · intro i
    change a.final.heads (nodeSlots (DAGNodes.coreSlots i))=_
    rw [ah,lh]
    simp only [NodeLoop.entry,NodeRound.cfg,List.length_nil,List.take_length,List.nil_append,
      Nat.zero_add]
    rfl
  · intro i
    change a.final.tapes (nodeSlots (DAGNodes.coreSlots i))=_
    rw [atape,lt]
    simp only [NodeLoop.entry,NodeRound.cfg,List.nil_append,List.append_nil]
    rfl
  · intro i hi
    obtain ⟨hh,ht⟩:=outside i hi
    exact ⟨hh.trans (ph i),ht.trans (congrFun pt i)⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
