import Proof.PCP.PCPPRequestCircuitCodeLayout

/-! Original native DAG to the literal two-field canonical Boolean circuit
code. Both operands are physically produced by the same streaming run. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitCode
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem code_run {n : ℕ} (c : BooleanCircuit n) :
    ∃ r,run machine (budget c) (input c)=some r ∧
      (∃ padding,r.final.tapes framedSlot=frame
        (ExecutableInterfaces.encodeBooleanCircuit c).bits++List.replicate padding false) ∧
      r.final.heads framedSlot=0 ∧
      r.final.tapes rawSlot=(ExecutableInterfaces.encodeBooleanCircuit c).bits ∧
      r.final.heads rawSlot=0 ∧
      r.final.tapes nativeSource=PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val) ∧
      r.final.heads nativeSource=(PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)).length ∧
      r.steps ≤ budget c := by
  obtain ⟨base,hb,⟨pa,ba⟩,bha,⟨pb,bb⟩,bhb,_,bn,bhn,bs⟩ := PCPPRequestCircuitIndex.index_run c
  let prep := TapeEmbedding.receipt (fun _ : Fin 234 => 0) (fun _ : Fin 234 => []) base
  have hp := TapeEmbedding.run_embed PCPPRequestCircuitIndex.machine
    (fun _ : Fin 234 => 0) (fun _ : Fin 234 => []) _ _ base hb
  have oldT (i : Fin PCPPRequestCircuitIndex.tapes) : prep.final.tapes (i.castAdd 234)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin PCPPRequestCircuitIndex.tapes) : prep.final.heads (i.castAdd 234)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_left]
  have newH (j : Fin 234) : prep.final.heads (j.natAdd PCPPRequestCircuitIndex.tapes)=0 := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_right]
  have pt (j : Fin 234) : prep.final.tapes (slots j)=PCPPRequestCircuitTag.input
      (CanonicalBinary.encodeBalancedList (c.nodes.map ExecutableInterfaces.encodeBooleanNode))
      (CanonicalBinary.encodeNat c.output.val) pa pb j := by
    by_cases h0 : j=0
    · subst j; exact (oldT _).trans ba
    by_cases h1 : j=1
    · subst j; exact (oldT _).trans bb
    have hv0 : j.val≠0 := fun h => h0 (Fin.ext h)
    have hv1 : j.val≠1 := fun h => h1 (Fin.ext h)
    simp only [slots,hv0,hv1,ite_false,PCPPRequestCircuitTag.input,h0,h1,prep,
      TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_right]
  have ph (j : Fin 234) : prep.final.heads (slots j)=0 := by
    by_cases h0 : j=0
    · subst j; exact (oldH _).trans bha
    by_cases h1 : j=1
    · subst j; exact (oldH _).trans bhb
    have hv0 : j.val≠0 := fun h => h0 (Fin.ext h)
    have hv1 : j.val≠1 := fun h => h1 (Fin.ext h)
    simp only [slots,hv0,hv1,ite_false]
    exact newH j
  obtain ⟨out,ready,⟨padding,oframe⟩,oraw⟩ := PCPPRequestCircuitTag.tag_run
    (CanonicalBinary.encodeBalancedList (c.nodes.map ExecutableInterfaces.encodeBooleanNode))
    (CanonicalBinary.encodeNat c.output.val) pa pb
  obtain ⟨called,hcall,ch,ct,cs⟩ := ready.focus_at slots slots_injective
    prep.final.heads prep.final.tapes pt ph
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 234 => 0)
      (fun _ : Fin 234 => []) (initialConfiguration PCPPRequestCircuitIndex.machine
        (PCPPRequestCircuitIndex.input c)))=initialConfiguration machine (input c) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPPRequestCircuitIndex.tapes) (n:=234) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitIndex.tapes,
          PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
          DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitIndex.tapes,
          PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
          DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hin] at whole
  have selected (j : Fin 234) : called.final.tapes (slots j)=out j := by
    rw [ct]
    exact install_slot slots slots_injective _ _ j
  refine ⟨Composition.joinedReceipt prep called,whole,⟨padding,(selected 222).trans oframe⟩,
    ?_,(selected 232).trans oraw,?_,?_,?_,?_⟩
  · change called.final.heads (slots 222)=0
    exact (congrFun ch _).trans (ph _)
  · change called.final.heads (slots 232)=0
    exact (congrFun ch _).trans (ph _)
  · change called.final.tapes nativeSource=_
    rw [ct,install_other slots _ _ nativeSource slots_ne_native]
    exact (oldT _).trans bn
  · change called.final.heads nativeSource=_
    exact (congrFun ch _).trans ((oldH _).trans bhn)
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitCode
