import Proof.PCP.PCPPNativeClauseDescriptorConsumerLayout

/-! Execute the original node producer, measure and frame its actual output,
and assemble exactly the padded request consumed by the faithful source. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ) :=
  6*fuel+8+PCPPNativeClauseDescriptor.budget a.minimumArity n c.size c.output.val
    (c.nodes.flatMap PCPPRequestNodeSchema.native)

theorem descriptor_run (a : PointwisePCPPAlgorithm) {t s n : ℕ} (p : Machine t s)
    (target width size index : Fin t) (ws : width≠size) (wi : width≠index) (si : size≠index)
    (forward : CursorRestore.NoLeft p target) (c : BooleanCircuit n)
    (fuel : ℕ) (nativeInput : Fin t→List Bool) (native : ExecutionReceipt t s)
    (hr : run p fuel nativeInput=some native)
    (hout : native.final.tapes target=c.nodes.flatMap PCPPRequestNodeSchema.native)
    (hhead : native.final.heads target=(c.nodes.flatMap PCPPRequestNodeSchema.native).length)
    (hwidth : native.final.tapes width=List.replicate n true)
    (hsize : native.final.tapes size=List.replicate c.size true)
    (hindex : native.final.tapes index=List.replicate c.output.val true) :
    ∃ result,run (machine a p target width size index) (budget a c fuel) (input nativeInput)=some result ∧
      result.steps≤budget a c fuel ∧
      result.final.tapes (slots width size index 26)=PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit ∧
      result.final.heads (slots width size index 26)=(PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit).length ∧
      result.final.heads (slots width size index 10)=0 ∧
      result.final.tapes (slots width size index 10)=List.replicate (PCPPRequestBoundary.request a c).arity true ∧
      result.final.heads (slots width size index 27)=0 ∧
      result.final.tapes (slots width size index 27)=List.replicate (PCPPRequestBoundary.request a c).circuit.size true := by
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
  have hinput : ∀ j,prepared.final.tapes (slots width size index j)=
      PCPPNativeClauseDescriptor.input n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native) j := by
    apply descriptor_input width size index n c.size c.output.val _ prepared.final.tapes
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep width).trans hwidth)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep size).trans hsize)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ((fkeep index).trans hindex)
    · exact (TapeEmbedding.receipt_tapes_old _ _ _ _).trans ft
    · intro j
      exact TapeEmbedding.receipt_tapes_new _ _ _ _
  obtain ⟨base,hb,bs,bt,bh,bdh,bd,bsh,bsz⟩:=PCPPNativeClauseDescriptor.request_run a c
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩:=RecoveryFocus.dock (slots width size index)
    (slots_injective width size index ws wi si) (PCPPNativeClauseDescriptor.machine a.minimumArity) _
    prepared.final.heads prepared.final.tapes
    (initialConfiguration (PCPPNativeClauseDescriptor.machine a.minimumArity)
      (PCPPNativeClauseDescriptor.input n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)))
    (by intro j; exact allH _) hinput base hb
  have joined:=Composition.run_join (first p target) (last a width size index)
    _ _ _ prepared lastReceipt hp hl
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 65=>0) (fun _ : Fin 65=>[])
      (initialConfiguration (AppendOutputFrame.machine p target) (AppendOutputFrame.input nativeInput)))=
      initialConfiguration (machine a p target width size index) (input nativeInput) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at joined
  have nativeSteps:=runFrom_steps_le p fuel _ native hr
  have hlen:=SelectiveReset.prefix_head (prefix_of_run p fuel _ native hr).1 target
  rw [hhead] at hlen
  change (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤0+native.steps at hlen
  have hbudget : (2*native.steps+4*(c.nodes.flatMap PCPPRequestNodeSchema.native).length+7)+1+
      PCPPNativeClauseDescriptor.budget a.minimumArity n c.size c.output.val
        (c.nodes.flatMap PCPPRequestNodeSchema.native)≤budget a c fuel := by
    unfold budget
    omega
  let result:=Composition.joinedReceipt prepared lastReceipt
  have more:=run_moreFuel (machine a p target width size index) _
    (budget a c fuel-((2*native.steps+4*(c.nodes.flatMap PCPPRequestNodeSchema.native).length+7)+1+
      PCPPNativeClauseDescriptor.budget a.minimumArity n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)))
    _ result joined
  rw [Nat.add_sub_of_le hbudget] at more
  refine ⟨result,more,?_,?_,?_,?_,?_,?_,?_⟩
  · change framed.steps+1+lastReceipt.steps≤_
    rw [ls]
    omega
  · exact (lt 26).trans bt
  · exact (lh 26).trans bh
  · exact (lh 10).trans bdh
  · exact (lt 10).trans bd
  · exact (lh 27).trans bsh
  · exact (lt 27).trans bsz

theorem forward (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target width size index : Fin t) (ws : width≠size) (wi : width≠index) (si : size≠index) :
    CursorRestore.NoLeft (machine a p target width size index) (slots width size index 26) :=
  CursorRestore.composition_forward _ _ _
    (EquationRowRaw.embedded_extra_forward (AppendOutputFrame.machine p target) (26 : Fin 65))
    (CursorRestore.focus_forward (slots width size index) (slots_injective width size index ws wi si)
      _ 26 (PCPPNativeClauseDescriptor.forward a.minimumArity))

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
