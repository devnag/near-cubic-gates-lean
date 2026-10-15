import Proof.PCP.PCPPRequestInputLayout

/-! Whole original native descriptor to the exact, externally framed PCPP
source request. Arity and circuit code are physically read and produced. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestInput
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_run {n : ℕ} (c : BooleanCircuit n) :
    ∃ r,run machine (budget c) (input c)=some r ∧
      r.final.tapes outputSlot=frame (natWord n++(ExecutableInterfaces.encodeBooleanCircuit c).bits) ∧
      r.final.heads outputSlot=0 ∧ r.steps ≤ budget c := by
  let tail := natWord c.nodes.length++(PCPPRequestNodeLoop.stream c.nodes++natWord c.output.val)
  have payload : PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)=natWord n++tail := by
    simp only [PCPPRequestNodeGlobal.payload,DecompositionInputCounts.word,tail,List.append_assoc]
  obtain ⟨base,hb,⟨padding,bf⟩,bhf,_,_,bn,bhn,bs⟩ := PCPPRequestCircuitReady.ready_run c
  let prep := TapeEmbedding.receipt (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) base
  have hp := TapeEmbedding.run_embed PCPPRequestCircuitReady.machine
    (fun _ : Fin 9 => 0) (fun _ : Fin 9 => []) _ _ base hb
  have oldT (i : Fin PCPPRequestCircuitReady.tapes) : prep.final.tapes (i.castAdd 9)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitReady.tapes,
      PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin PCPPRequestCircuitReady.tapes) : prep.final.heads (i.castAdd 9)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitReady.tapes,
      PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have freshT (i : Fin 9) : prep.final.tapes (i.natAdd PCPPRequestCircuitReady.tapes)=[] := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitReady.tapes,
      PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
  have freshH (i : Fin 9) : prep.final.heads (i.natAdd PCPPRequestCircuitReady.tapes)=0 := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestCircuitReady.tapes,
      PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
      PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
  have pt (j : Fin 9) : prep.final.tapes (slots j)=PCPPRequestWordFramed.input n tail
      (ExecutableInterfaces.encodeBooleanCircuit c).bits (List.replicate padding false) j := by
    fin_cases j
    · exact (oldT _).trans (bn.trans payload)
    · exact (oldT _).trans bf
    all_goals exact freshT _
  have ph (j : Fin 9) : prep.final.heads (slots j)=0 := by
    fin_cases j
    · exact (oldH _).trans bhn
    · exact (oldH _).trans bhf
    all_goals exact freshH _
  obtain ⟨out,ready,oframe⟩ := PCPPRequestWordFramed.ready n tail
    (ExecutableInterfaces.encodeBooleanCircuit c).bits (List.replicate padding false)
  obtain ⟨called,hcall,ch,ct,cs⟩ := ready.focus_at slots slots_injective
    prep.final.heads prep.final.tapes pt ph
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 9 => 0)
      (fun _ : Fin 9 => []) (initialConfiguration PCPPRequestCircuitReady.machine
        (PCPPRequestCircuitReady.input c)))=initialConfiguration machine (input c) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPPRequestCircuitReady.tapes) (n:=9) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitReady.tapes,
          PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
          PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestCircuitReady.tapes,
          PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,
          PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hi] at whole
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_,?_⟩
  · change called.final.tapes (slots 7)=_
    rw [ct,install_slot slots slots_injective]
    exact oframe
  · change called.final.heads (slots 7)=0
    exact (congrFun ch _).trans (ph 7)
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

theorem request_run {n0 : ℕ} (request : PCPPRequest n0) :
    ∃ r,run machine (budget request.circuit) (input request.circuit)=some r ∧
      r.final.tapes outputSlot=frame (pcppInput request) ∧
      r.final.heads outputSlot=0 ∧ r.steps ≤ budget request.circuit := input_run request.circuit

end NearCubicWires.RepairOrdinary.PCPPRequestInput
