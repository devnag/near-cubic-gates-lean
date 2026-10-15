import Proof.PCP.PCPPRequestNodeGlobalLayout
import Proof.PCP.PCPPRequestNodeCapacity

/-! Original framed native circuit descriptors and blank work suffice for the
entire node stream. Capacity, counts, allocation and all repeated calls are
executed, using the existing cold header producer unchanged. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem global_run {n : ℕ} (D C E a : ℕ) (nodes : List (BooleanNode n)) (suffix : List Bool)
    (hE : E=C*((frame (DecompositionInputCounts.word a nodes.length
      (PCPPRequestNodeLoop.stream nodes++suffix))).length+1)^D)
    (hcap : ∀ node∈nodes,PCPPRequestNodeCold.budget node+1 ≤ E) :
    ∃ r,run (machine D C) (budget D C E a nodes suffix)
      (input D (DecompositionInputCounts.word a nodes.length
        (PCPPRequestNodeLoop.stream nodes++suffix)))=some r ∧
      r.final.tapes (outputSlot D)=PCPPRequestNodeLoop.encoded nodes ∧
      r.final.heads (outputSlot D)=(PCPPRequestNodeLoop.encoded nodes).length ∧
      r.final.tapes (slots D 0)=DecompositionInputCounts.word a nodes.length
        (PCPPRequestNodeLoop.stream nodes++suffix) ∧
      r.final.heads (slots D 0)=(natWord a++natWord nodes.length).length+
        (PCPPRequestNodeLoop.stream nodes).length ∧
      r.final.tapes (slots D 644)=List.replicate E true ∧ r.final.heads (slots D 644)=0 ∧
      r.final.tapes (slots D 646)=RepairSource.VerifierDecoding.CompareMachine.word nodes.length ∧
      r.final.heads (slots D 646)=1 ∧
      r.steps ≤ budget D C E a nodes suffix := by
  let source := DecompositionInputCounts.word a nodes.length (PCPPRequestNodeLoop.stream nodes++suffix)
  let pre := natWord a++natWord nodes.length
  obtain ⟨base,hb,_,_,bsource,bpos,bcount,bheads,bcap,bch,bs⟩ :=
    DecompositionColdPrepare.prepare_run D C a nodes.length (PCPPRequestNodeLoop.stream nodes++suffix)
  let prep := TapeEmbedding.receipt (fun _ : Fin 647 => 0) (fun _ : Fin 647 => []) base
  have hp := TapeEmbedding.run_embed (DecompositionColdPrepare.machine D C)
    (fun _ : Fin 647 => 0) (fun _ : Fin 647 => []) _ _ base hb
  have oldT (i : Fin (DecompositionColdPrepare.tapes D)) :
      prep.final.tapes (i.castAdd 647)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin (DecompositionColdPrepare.tapes D)) :
      prep.final.heads (i.castAdd 647)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have pt (j : Fin 647) : prep.final.tapes (slots D j)=
      (PCPPRequestNodeList.entry E nodes.length source pre.length []).tapes j := by
    rw [PCPPRequestNodeList.entry_tapes]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldT _).trans bsource
    by_cases h644 : j.val=644
    · have he : j=644 := Fin.ext h644
      subst j
      exact (oldT _).trans (bcap.trans (congrArg (fun z => List.replicate z true) hE.symm))
    by_cases h646 : j.val=646
    · have he : j=646 := Fin.ext h646
      subst j
      exact (oldT _).trans (bcount 6)
    simp only [slots,h0,h644,h646,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,
      Fin.addCases_right]
  have ph (j : Fin 647) : prep.final.heads (slots D j)=
      (PCPPRequestNodeList.entry E nodes.length source pre.length []).heads j := by
    rw [PCPPRequestNodeList.entry_heads]
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldH _).trans bpos
    by_cases h644 : j.val=644
    · have he : j=644 := Fin.ext h644
      subst j
      exact (oldH _).trans bch
    by_cases h646 : j.val=646
    · have he : j=646 := Fin.ext h646
      subst j
      exact (oldH _).trans (bheads 6)
    simp only [slots,h0,h644,h646,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,DecompositionColdPrepare.tapes,
      Fin.addCases_right]
  obtain ⟨body,hbody,bt0,bh0,bout,boh,btc,bhc,btn,bhn,bstep⟩ :=
    PCPPRequestNodeList.stream_run pre nodes suffix E hcap
  have source_eq : pre++PCPPRequestNodeLoop.stream nodes++suffix=source := by
    simp only [pre,source,DecompositionInputCounts.word,List.append_assoc]
  rw [source_eq] at hbody bt0
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config (slots D) (slots_injective D)
    PCPPRequestNodeList.machine prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config (slots D) prep.final.heads prep.final.tapes
      (PCPPRequestNodeList.entry E nodes.length source pre.length [])=
      Composition.restart prep.final (second D).start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick (slots D) i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick (slots D) hi
        simp only [RecoveryFocus.config,hi,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing (slots D) prep.final.tapes _ pt
  rw [he] at hcall
  have whole := Composition.run_join (first D C) (second D) _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 647 => 0)
      (fun _ : Fin 647 => []) (initialConfiguration (DecompositionColdPrepare.machine D C)
        (DecompositionColdPrepare.input D source)))=
      initialConfiguration (machine D C) (input D source) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=DecompositionColdPrepare.tapes D) (n:=647) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_left,initialConfiguration]
      · simp only [Composition.leftConfig,TapeEmbedding.config,DecompositionColdPrepare.tapes,Fin.addCases_right,initialConfiguration]
    · rfl
  rw [hin] at whole
  have ct (j : Fin 647) : called.final.tapes (slots D j)=body.final.tapes j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots D) (slots_injective D)]
  have ch (j : Fin 647) : called.final.heads (slots D j)=body.final.heads j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots D) (slots_injective D)]
  refine ⟨Composition.joinedReceipt prep called,whole,
    (ct 643).trans bout,(ch 643).trans boh,(ct 0).trans bt0,(ch 0).trans bh0,
    (ct 644).trans btc,(ch 644).trans bhc,(ct 646).trans btn,(ch 646).trans bhn,?_⟩
  change base.steps+1+called.steps ≤ _
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
