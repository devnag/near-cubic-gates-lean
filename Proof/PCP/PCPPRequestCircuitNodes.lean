import Proof.PCP.PCPPRequestCircuitNodesLayout

/-! Whole original native descriptor stream to its literal balanced node-list
code. The same cold serializer reads the produced stream/count directly. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitNodes
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSource : Fin tapes := ((PCPPRequestNodeGlobal.slots 12 0).castAdd 1).castAdd 128
theorem slots_ne_native (j : Fin 128) : slots j≠nativeSource := by
  intro he
  have hv := congrArg Fin.val he
  by_cases h0 : j.val=0
  · have hi : PCPPRequestNodeGlobal.slots 12 643=PCPPRequestNodeGlobal.slots 12 0 := by
      apply Fin.ext
      rw [slots,if_pos h0] at hv
      exact hv
    have h := congrArg Fin.val (PCPPRequestNodeGlobal.slots_injective 12 hi)
    contradiction
  by_cases h2 : j.val=2
  · have hi : PCPPRequestNodeGlobal.slots 12 646=PCPPRequestNodeGlobal.slots 12 0 := by
      apply Fin.ext
      rw [slots,if_neg h0,if_pos h2] at hv
      exact hv
    have h := congrArg Fin.val (PCPPRequestNodeGlobal.slots_injective 12 hi)
    contradiction
  have hn := (PCPPRequestNodeGlobal.slots 12 0).isLt
  simp only [slots,h0,h2,ite_false,nativeSource,Fin.val_castAdd,Fin.val_natAdd,prefixTapes] at hv
  omega

theorem nodes_run {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    ∃ r,run machine (budget nodes suffix) (input nodes suffix)=some r ∧
      r.final.tapes outputSlot=(CanonicalBinary.encodeBalancedList
        (nodes.map ExecutableInterfaces.encodeBooleanNode)).bits ∧
      r.final.heads outputSlot=0 ∧
      r.final.tapes framedSlot=ZeroPadding.pad
        (PCPPairReusable.capacity (PCPSerializerMass.mass (fields nodes)))
        (frame (CanonicalBinary.encodeBalancedList (nodes.map ExecutableInterfaces.encodeBooleanNode)).bits) ∧
      r.final.heads framedSlot=0 ∧
      r.final.tapes nativeSource=PCPPRequestNodeGlobal.payload nodes suffix ∧
      r.final.heads nativeSource=(natWord n++natWord nodes.length).length+
        (PCPPRequestNodeLoop.stream nodes).length ∧
      r.steps ≤ budget nodes suffix := by
  obtain ⟨base,hb,bout,bhout,bcount,bhcount,bsource,bpos,bs⟩ := PCPPRequestNodeGlobal.ready_run nodes suffix
  let prep := TapeEmbedding.receipt (fun _ : Fin 128 => 0) (fun _ : Fin 128 => []) base
  have hp := TapeEmbedding.run_embed PCPPRequestNodeGlobal.readyMachine
    (fun _ : Fin 128 => 0) (fun _ : Fin 128 => []) _ _ base hb
  have oldT (i : Fin prefixTapes) : prep.final.tapes (i.castAdd 128)=base.final.tapes i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have oldH (i : Fin prefixTapes) : prep.final.heads (i.castAdd 128)=base.final.heads i := by
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
  have pt (j : Fin 128) : prep.final.tapes (slots j)=
      PCPTraversal.input (PCPPRequestNodeLoop.encoded nodes) (fields nodes).length j := by
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldT _).trans bout
    by_cases h2 : j.val=2
    · have he : j=2 := Fin.ext h2
      subst j
      change prep.final.tapes (nodeCount.castAdd 128)=CompareMachine.word (fields nodes).length
      simpa only [fields,List.length_map] using (oldT nodeCount).trans bcount
    have hj0 : j≠0 := fun h => h0 (congrArg Fin.val h)
    have hj2 : j≠2 := fun h => h2 (congrArg Fin.val h)
    simp only [slots,h0,h2,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right,
      PCPTraversal.input,hj0,hj2]
  have ph (j : Fin 128) : prep.final.heads (slots j)=PCPTraversal.heads 0 j := by
    by_cases h0 : j.val=0
    · have he : j=0 := Fin.ext h0
      subst j
      exact (oldH _).trans bhout
    by_cases h2 : j.val=2
    · have he : j=2 := Fin.ext h2
      subst j
      exact (oldH _).trans bhcount
    have hj0 : j≠0 := fun h => h0 (congrArg Fin.val h)
    have hj2 : j≠2 := fun h => h2 (congrArg Fin.val h)
    simp only [slots,h0,h2,ite_false,prep,TapeEmbedding.receipt,TapeEmbedding.config,prefixTapes,
      PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right,
      PCPTraversal.heads,hj0,hj2]
  obtain ⟨body,hbody,bframed,braw,_,_,bh,_,bstep⟩ := PCPTraversal.cold_run [] (fields nodes) []
  simp only [List.nil_append,List.append_nil,List.length_nil] at hbody
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config slots slots_injective PCPTraversal.machine
    prep.final.heads prep.final.tapes _ _ body hbody
  have he : RecoveryFocus.config slots prep.final.heads prep.final.tapes
      (PCPTraversal.entry (FieldList.stream (fields nodes)) 0 (fields nodes).length)=
      Composition.restart prep.final second.start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick slots i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick slots hi
        simp only [RecoveryFocus.config,hi,PCPTraversal.entry,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing slots prep.final.tapes _ pt
  rw [he] at hcall
  have whole := Composition.run_join first second _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 128 => 0)
      (fun _ : Fin 128 => []) (initialConfiguration PCPPRequestNodeGlobal.readyMachine
        (PCPPRequestNodeGlobal.readyInput nodes suffix)))=initialConfiguration machine (input nodes suffix) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=prefixTapes) (n:=128) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,prefixTapes,
          PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,prefixTapes,
          PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hin] at whole
  have ct (j : Fin 128) : called.final.tapes (slots j)=body.final.tapes j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have ch (j : Fin 128) : called.final.heads (slots j)=body.final.heads j := by
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have noNative : RecoveryFocus.pick slots nativeSource=none := by
    have hn : ¬∃ j,slots j=nativeSource := by rintro ⟨j,hj⟩; exact slots_ne_native j hj
    simp only [RecoveryFocus.pick,dif_neg hn]
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ct 78).trans (by simpa only [literal_code] using braw)
  · exact (ch 78).trans (by rw [bh]; rfl)
  · exact (ct 77).trans (by simpa only [literal_code] using bframed)
  · exact (ch 77).trans (by rw [bh]; rfl)
  · change called.final.tapes nativeSource=_
    rw [cf]
    simp only [RecoveryFocus.config,noNative]
    exact (oldT _).trans bsource
  · change called.final.heads nativeSource=_
    rw [cf]
    simp only [RecoveryFocus.config,noNative]
    exact (oldH _).trans bpos
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitNodes
