import Proof.PCP.PCPPNativeClauseDescriptorConsumer
import Proof.PCP.PCPPNativeClauseDescriptorTyped
import Proof.PCP.PCPPNativeClauseDescriptorForward
import Proof.PCP.PCPPNativeHierarchyNodesReady
import Proof.PCP.PCPPNativeFrame

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization

/-- The descriptor bytes assembled with minimum arity `0` are the native descriptor of `padToArity`. -/
theorem emitted_zero {n : ℕ} (c : BooleanCircuit n) :
    PCPPNativeClauseDescriptor.emitted 0 n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native) =
      PCPPNative.descriptor c.padToArity := by
  rw [PCPPNative.descriptor_eq]
  simp only [PCPPNativeClauseDescriptor.emitted, PCPPNativeDescriptorTail.emitted, PCPPNativePadding.emitted_nodes n,
    PCPPNativeColdMetadata.domain, PCPPNativeColdMetadata.padded, PCPPNativeColdMetadata.padding,
    BooleanCircuit.padToArity, BooleanCircuit.padSize, BooleanDAGBuilder.finish, BooleanDAGBuilder.appendFalse_nodes,
    BooleanCircuit.toBuilder, BooleanDAGExtension.lift_val, List.length_append, List.length_replicate,
    List.flatMap_append, List.flatMap_replicate, BooleanCircuit.size, List.append_assoc, Nat.max_zero]
  have h : max n c.nodes.length = c.nodes.length + (n - c.nodes.length) := by omega
  rw [h]

/-- The shared descriptor consumer with minimum arity `0`. -/
noncomputable def last {t : ℕ} (width size index : Fin t) :=
  RecoveryFocus.machine (PCPPNativeClauseDescriptorConsumer.slots width size index)
    (PCPPNativeClauseDescriptor.machine 0)
noncomputable def consumer {t s : ℕ} (p : Machine t s) (target width size index : Fin t) :=
  Composition.machine (PCPPNativeClauseDescriptorConsumer.first p target) (last width size index)
def consumerBudget {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ) :=
  6*fuel+8+PCPPNativeClauseDescriptor.budget 0 n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)

theorem consumer_run {t s n : ℕ} (p : Machine t s)
    (target width size index : Fin t) (ws : width≠size) (wi : width≠index) (si : size≠index)
    (forward : CursorRestore.NoLeft p target) (c : BooleanCircuit n)
    (fuel : ℕ) (nativeInput : Fin t→List Bool) (native : ExecutionReceipt t s)
    (hr : run p fuel nativeInput=some native)
    (hout : native.final.tapes target=c.nodes.flatMap PCPPRequestNodeSchema.native)
    (hhead : native.final.heads target=(c.nodes.flatMap PCPPRequestNodeSchema.native).length)
    (hwidth : native.final.tapes width=List.replicate n true)
    (hsize : native.final.tapes size=List.replicate c.size true)
    (hindex : native.final.tapes index=List.replicate c.output.val true) :
    ∃ result,run (consumer p target width size index) (consumerBudget c fuel)
        (PCPPNativeClauseDescriptorConsumer.input nativeInput)=some result ∧
      result.steps≤consumerBudget c fuel ∧
      result.final.tapes (PCPPNativeClauseDescriptorConsumer.slots width size index 26)=
        PCPPNative.descriptor c.padToArity ∧
      result.final.heads (PCPPNativeClauseDescriptorConsumer.slots width size index 26)=
        (PCPPNative.descriptor c.padToArity).length := by
  obtain ⟨framed,hf,ft,fh,fkeep,fs⟩:=PCPPNativeFrame.frame_run p target forward fuel nativeInput native hr
    (c.nodes.flatMap PCPPRequestNodeSchema.native) hout hhead
  let prepared:=TapeEmbedding.receipt (fun _ : Fin 65=>0) (fun _ : Fin 65=>[]) framed
  have hp:=TapeEmbedding.run_embed (AppendOutputFrame.machine p target)
    (fun _ : Fin 65=>0) (fun _ : Fin 65=>[]) _ _ framed hf
  have allH : ∀ i,prepared.final.heads i=0 := by
    intro i
    refine Fin.addCases (m:=(t+2)+2) (n:=65) (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ _ _).trans (fh j)
    · exact TapeEmbedding.receipt_heads_new _ _ _ _
  have hinput : ∀ j,prepared.final.tapes (PCPPNativeClauseDescriptorConsumer.slots width size index j)=
      PCPPNativeClauseDescriptor.input n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native) j := by
    apply PCPPNativeClauseDescriptorConsumer.descriptor_input width size index n c.size c.output.val _
      prepared.final.tapes
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep width).trans hwidth)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep size).trans hsize)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep index).trans hindex)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ft
    · intro j
      exact TapeEmbedding.receipt_tapes_new _ _ _ _
  obtain ⟨base,hb,bs,bt,bh,_,_,_,_⟩:=
    PCPPNativeClauseDescriptor.assemble_run 0 n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)
  rw [emitted_zero] at bt bh
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩:=RecoveryFocus.dock (PCPPNativeClauseDescriptorConsumer.slots width size index)
    (PCPPNativeClauseDescriptorConsumer.slots_injective width size index ws wi si)
    (PCPPNativeClauseDescriptor.machine 0) _
    prepared.final.heads prepared.final.tapes
    (initialConfiguration (PCPPNativeClauseDescriptor.machine 0)
      (PCPPNativeClauseDescriptor.input n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)))
    (by intro j; exact allH _) hinput base hb
  have joined:=Composition.run_join (PCPPNativeClauseDescriptorConsumer.first p target) (last width size index)
    _ _ _ prepared lastReceipt hp hl
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 65=>0) (fun _ : Fin 65=>[])
      (initialConfiguration (AppendOutputFrame.machine p target) (AppendOutputFrame.input nativeInput)))=
      initialConfiguration (consumer p target width size index)
        (PCPPNativeClauseDescriptorConsumer.input nativeInput) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at joined
  have hlen:=SelectiveReset.prefix_head (prefix_of_run p fuel _ native hr).1 target
  rw [hhead] at hlen
  change (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤0+native.steps at hlen
  have hbudget : (2*native.steps+4*(c.nodes.flatMap PCPPRequestNodeSchema.native).length+7)+1+
      PCPPNativeClauseDescriptor.budget 0 n c.size c.output.val
        (c.nodes.flatMap PCPPRequestNodeSchema.native)≤consumerBudget c fuel := by
    have nativeSteps:=runFrom_steps_le p fuel _ native hr
    unfold consumerBudget
    omega
  let result:=Composition.joinedReceipt prepared lastReceipt
  have more:=run_moreFuel (consumer p target width size index) _
    (consumerBudget c fuel-((2*native.steps+4*(c.nodes.flatMap PCPPRequestNodeSchema.native).length+7)+1+
      PCPPNativeClauseDescriptor.budget 0 n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)))
    _ result joined
  rw [Nat.add_sub_of_le hbudget] at more
  refine ⟨result,more,?_,?_,?_⟩
  · change framed.steps+1+lastReceipt.steps≤_
    rw [ls]
    omega
  · exact (lt 26).trans bt
  · exact (lh 26).trans bh

theorem consumer_forward {t s : ℕ} (p : Machine t s)
    (target width size index : Fin t) (ws : width≠size) (wi : width≠index) (si : size≠index) :
    CursorRestore.NoLeft (consumer p target width size index)
      (PCPPNativeClauseDescriptorConsumer.slots width size index 26) :=
  CursorRestore.composition_forward _ _ _
    (EquationRowRaw.embedded_extra_forward (AppendOutputFrame.machine p target) (26 : Fin 65))
    (CursorRestore.focus_forward (PCPPNativeClauseDescriptorConsumer.slots width size index)
      (PCPPNativeClauseDescriptorConsumer.slots_injective width size index ws wi si)
      _ 26 (PCPPNativeClauseDescriptor.forward 0))

end NearCubicGates.Close.CheckedPCPP
