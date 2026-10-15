import Proof.PCP.PCPPRequestCircuitIndexLayout

/-! The actual two canonical operands of encodeBooleanCircuit, from the
original framed native DAG alone. The balanced list is retained while its
output index is parsed and encoded at the existing streaming cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitIndex
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem index_run {n : ℕ} (c : BooleanCircuit n) :
    ∃ r,run machine (budget c) (input c)=some r ∧
      (∃ padding,r.final.tapes nodeField=frame
        (CanonicalBinary.encodeBalancedList (c.nodes.map ExecutableInterfaces.encodeBooleanNode)).bits++
          List.replicate padding false) ∧ r.final.heads nodeField=0 ∧
      (∃ padding,r.final.tapes indexField=frame (CanonicalBinary.encodeNat c.output.val).bits++
        List.replicate padding false) ∧ r.final.heads indexField=0 ∧
      r.final.tapes indexRaw=(CanonicalBinary.encodeNat c.output.val).bits ∧
      r.final.tapes nativeSource=PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val) ∧
      r.final.heads nativeSource=(PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)).length ∧
      r.steps ≤ budget c := by
  let pre := (natWord n++natWord c.nodes.length)++PCPPRequestNodeLoop.stream c.nodes
  have hs : PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)=pre++natWord c.output.val++[] := by
    simp only [PCPPRequestNodeGlobal.payload,DecompositionInputCounts.word,pre,List.append_assoc,List.append_nil]
  obtain ⟨base,hb,_,_,bf,bhf,bsource,bpos,bs⟩ := PCPPRequestCircuitNodes.nodes_run c.nodes (natWord c.output.val)
  let prep := TapeEmbedding.receipt (fun _ : Fin 136 => 0) (fun _ : Fin 136 => []) base
  have hp := TapeEmbedding.run_embed PCPPRequestCircuitNodes.machine
    (fun _ : Fin 136 => 0) (fun _ : Fin 136 => []) _ _ base hb
  have oldT (i : Fin PCPPRequestCircuitNodes.tapes) : prep.final.tapes (i.castAdd 136)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin PCPPRequestCircuitNodes.tapes) : prep.final.heads (i.castAdd 136)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have pt (j : Fin 136) : prep.final.tapes (slots j)=if j=0 then pre++natWord c.output.val++[] else [] := by
    by_cases hj : j=0
    · subst j
      exact (oldT _).trans (bsource.trans hs)
    have hv : j.val≠0 := fun h => hj (Fin.ext h)
    simp only [slots,hv,hj,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_right]
  have ph (j : Fin 136) : prep.final.heads (slots j)=if j=0 then pre.length else 0 := by
    by_cases hj : j=0
    · subst j
      change prep.final.heads (PCPPRequestCircuitNodes.nativeSource.castAdd 136)=pre.length
      exact (oldH _).trans (bpos.trans List.length_append.symm)
    have hv : j.val≠0 := fun h => hj (Fin.ext h)
    simp only [slots,hv,hj,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_right]
  obtain ⟨called,hcall,cs,ci,cih,craw,csource,cpos,keep⟩ := PCPPRequestNatural.focus_run slots slots_injective
    prep.final pre [] c.output.val pt ph
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 136 => 0)
      (fun _ : Fin 136 => []) (initialConfiguration PCPPRequestCircuitNodes.machine
        (PCPPRequestCircuitNodes.input c.nodes (natWord c.output.val))))=
      initialConfiguration machine (input c) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPPRequestCircuitNodes.tapes) (n:=136) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitNodes.tapes,
          PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitNodes.tapes,
          PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hin] at whole
  have noNode : RecoveryFocus.pick slots nodeField=none := by
    have hn : ¬∃ j,slots j=nodeField := by rintro ⟨j,hj⟩; exact slots_ne_node j hj
    simp only [RecoveryFocus.pick,dif_neg hn]
  obtain ⟨nt,nh⟩ := keep nodeField noNode
  refine ⟨Composition.joinedReceipt prep called,whole,?_,nh.trans ((oldH _).trans bhf),ci,cih,craw,
    csource.trans hs.symm,?_,?_⟩
  · refine ⟨_,nt.trans ((oldT _).trans bf)⟩
  · change called.final.heads (slots 0)=_
    calc
      _ = pre.length+(natWord c.output.val).length := cpos
      _ = (PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)).length := by
        rw [hs]
        simp only [List.length_append,List.length_nil,Nat.add_zero]
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitIndex
