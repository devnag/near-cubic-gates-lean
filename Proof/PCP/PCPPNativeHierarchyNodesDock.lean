import Proof.PCP.PCPPNativeHierarchyNodesLayout

/-! Same original hierarchy-field handoff into the entire node program. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem dock_input {s : ℕ} (k CH Cpad : ℕ) (code x bound : List Bool)
    (oracle : BooleanCircuit (HierarchyStreams.R source k CH Cpad code x))
    (a : ExecutionReceipt (base source k) s)
    (hf : HierarchyStreams.Fields source k CH Cpad code x bound (PCPPNativeHierarchy.projected source k a.final))
    (ho : a.final.heads (PCPPNativeHierarchy.loadSlots source k 2)=0 ∧
      a.final.tapes (PCPPNativeHierarchy.loadSlots source k 2)=PCPPNative.descriptor oracle)
    (i : Fin 438) :
    let lifted := TapeEmbedding.receipt (fun _ : Fin 438=>0) (fun _=>[]) a
    lifted.final.heads (slots source k i)=PCPPNativeCounterNodes.heads i ∧
    lifted.final.tapes (slots source k i)=PCPPNativeCounterNodes.input (PCPPNative.descriptor oracle)
      (source.output (HierarchyStreams.request k CH Cpad code x))
      (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) i := by
  intro lifted
  by_cases h0 : i=0
  · subst i; exact ho
  by_cases h40 : i=40
  · subst i; simpa [lifted,base,PCPPNativeHierarchyCounters.base,TapeEmbedding.receipt,TapeEmbedding.config,slots,PCPPNativeHierarchyCounters.sourcePorts,PCPPNativeHierarchy.projected,node_heads,node_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queriesHead hf.queries
  by_cases h47 : i=47
  · subst i; simpa [lifted,base,PCPPNativeHierarchyCounters.base,TapeEmbedding.receipt,TapeEmbedding.config,slots,PCPPNativeHierarchyCounters.sourcePorts,PCPPNativeHierarchy.projected,node_heads,node_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.clauseCountHead hf.clauseCount
  by_cases h52 : i=52
  · subst i; simpa [lifted,base,PCPPNativeHierarchyCounters.base,TapeEmbedding.receipt,TapeEmbedding.config,slots,PCPPNativeHierarchyCounters.sourcePorts,PCPPNativeHierarchy.projected,node_heads,node_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queryStreamHead hf.queryStream
  by_cases h54 : i=54
  · subst i; simpa [lifted,base,PCPPNativeHierarchyCounters.base,TapeEmbedding.receipt,TapeEmbedding.config,slots,PCPPNativeHierarchyCounters.sourcePorts,PCPPNativeHierarchy.projected,node_heads,node_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queryCountHead hf.queryCount
  by_cases h57 : i=57
  · subst i; simpa [lifted,base,PCPPNativeHierarchyCounters.base,TapeEmbedding.receipt,TapeEmbedding.config,slots,PCPPNativeHierarchyCounters.sourcePorts,PCPPNativeHierarchy.projected,node_heads,node_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.clauseStreamHead hf.clauseStream
  simp [lifted,slots,h0,h40,h47,h52,h54,h57,node_input,node_heads]

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
