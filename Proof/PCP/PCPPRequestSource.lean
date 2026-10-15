import Proof.PCP.PCPPRequestSourceLayout

/-! The faithful PCPP constructor is invoked exactly once on the request
physically emitted from the original descriptor; its literal object is cached. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestSource
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (budget a request) (input a request)=some r ∧
      r.final.tapes (outputSlot a)=pcppOutput request (a.output request) ∧
      r.final.heads (outputSlot a)=0 ∧ r.steps ≤ budget a request := by
  obtain ⟨base,hb,bf,bhf,bs⟩ := PCPPRequestInput.request_run request
  let prep := TapeEmbedding.receipt (fun _ : Fin (program a).tapeCount => 0)
    (fun _ : Fin (program a).tapeCount => []) base
  have hp := TapeEmbedding.run_embed PCPPRequestInput.machine
    (fun _ : Fin (program a).tapeCount => 0) (fun _ : Fin (program a).tapeCount => []) _ _ base hb
  have oldT (i : Fin PCPPRequestInput.tapes) :
      prep.final.tapes (i.castAdd (program a).tapeCount)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestInput.tapes,
      PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin PCPPRequestInput.tapes) :
      prep.final.heads (i.castAdd (program a).tapeCount)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,PCPPRequestInput.tapes,
      PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,
      PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
      DecompositionColdPrepare.tapes,Fin.addCases_left]
  have pt (j : Fin (program a).tapeCount) : prep.final.tapes (slots a j)=
      (program a).inputTapes (pcppInput request) j := by
    by_cases hj : j.val=0
    · simp only [slots,hj,ite_true,Program.inputTapes]
      exact (oldT _).trans bf
    simp only [slots,hj,ite_false,Program.inputTapes,prep,TapeEmbedding.receipt,TapeEmbedding.config,
      PCPPRequestInput.tapes,PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,
      PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
  have ph (j : Fin (program a).tapeCount) : prep.final.heads (slots a j)=0 := by
    by_cases hj : j.val=0
    · simp only [slots,hj,ite_true]
      exact (oldH _).trans bhf
    simp only [slots,hj,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,
      PCPPRequestInput.tapes,PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,
      PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
  obtain ⟨source,hs,so,sh⟩ := a.constructor.reset_realizes request
  have hs' : run (program a).machine (2*sourceBudget a request+2)
      ((program a).inputTapes (pcppInput request))=some source := hs
  have ready : ClockJoin.ReadyRun (program a).machine (2*sourceBudget a request+2)
      ((program a).inputTapes (pcppInput request)) source.final.tapes :=
    ⟨source,hs',rfl,sh,runFrom_steps_le _ _ _ source hs'⟩
  obtain ⟨called,hcall,ch,ct,cs⟩ := ready.focus_at (slots a) (slots_injective a)
    prep.final.heads prep.final.tapes pt ph
  have whole := Composition.run_join (first a) (second a) _ _ _ prep called hp hcall
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin (program a).tapeCount => 0)
      (fun _ : Fin (program a).tapeCount => []) (initialConfiguration PCPPRequestInput.machine
        (PCPPRequestInput.input request.circuit)))=initialConfiguration (machine a) (input a request) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPPRequestInput.tapes) (n:=(program a).tapeCount) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestInput.tapes,
          PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,
          PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
          DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,PCPPRequestInput.tapes,
          PCPPRequestCircuitReady.tapes,PCPPRequestCircuitCode.tapes,PCPPRequestCircuitIndex.tapes,
          PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,PCPPRequestNodeGlobal.tapes,
          DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hi] at whole
  have htime : PCPPRequestInput.budget request.circuit+1+(2*sourceBudget a request+2)=budget a request := by
    unfold budget
    omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_,?_⟩
  · change called.final.tapes (slots a (program a).outputTape)=_
    rw [ct,install_slot (slots a) (slots_injective a)]
    exact so
  · change called.final.heads (slots a (program a).outputTape)=0
    exact (congrFun ch _).trans (ph _)
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestSource
