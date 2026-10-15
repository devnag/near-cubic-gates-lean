import Proof.PCP.PCPPNativeHierarchyCountersLayout

/-! The original hierarchy's retained physical fields satisfy the exact
entry of the metadata and measured-counter program. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem counter_input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) (i : Fin 75) :
    PCPPNativeColdCounters.input oracle p R Q i=
      if i=0 then oracle else if i=40 then frame Q.bits
      else if i=47 then VerifierDecoding.CompareMachine.word (Codec.clauses p).length
      else if i=52 then PCPPNativeMetadataMass.queryBytes p R Q
      else if i=54 then VerifierDecoding.CompareMachine.word (R*Q)
      else if i=57 then DedupBytes.fields p else [] := by
  fin_cases i <;> rfl
theorem counter_heads (i : Fin 75) :
    PCPPNativeColdCounters.heads i=if i=47 then 1 else if i=54 then 1 else 0 := by
  fin_cases i <;> rfl

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem dock_input {s : ℕ} (k CH Cpad : ℕ) (code x bound : List Bool)
    (oracle : BooleanCircuit (HierarchyStreams.R source k CH Cpad code x))
    (a : ExecutionReceipt (base source k) s)
    (hf : HierarchyStreams.Fields source k CH Cpad code x bound (PCPPNativeHierarchy.projected source k a.final))
    (ho : a.final.heads (PCPPNativeHierarchy.loadSlots source k 2)=0 ∧
      a.final.tapes (PCPPNativeHierarchy.loadSlots source k 2)=PCPPNative.descriptor oracle)
    (i : Fin 75) :
    let lifted := TapeEmbedding.receipt (fun _ : Fin 75=>0) (fun _=>[]) a
    lifted.final.heads (slots source k i)=PCPPNativeColdCounters.heads i ∧
    lifted.final.tapes (slots source k i)=PCPPNativeColdCounters.input (PCPPNative.descriptor oracle)
      (source.output (HierarchyStreams.request k CH Cpad code x))
      (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) i := by
  intro lifted
  by_cases h0 : i=0
  · subst i; exact ho
  by_cases h40 : i=40
  · subst i; simpa [lifted,slots,sourcePorts,PCPPNativeHierarchy.projected,counter_heads,counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queriesHead hf.queries
  by_cases h47 : i=47
  · subst i; simpa [lifted,slots,sourcePorts,PCPPNativeHierarchy.projected,counter_heads,counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.clauseCountHead hf.clauseCount
  by_cases h52 : i=52
  · subst i; simpa [lifted,slots,sourcePorts,PCPPNativeHierarchy.projected,counter_heads,counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queryStreamHead hf.queryStream
  by_cases h54 : i=54
  · subst i; simpa [lifted,slots,sourcePorts,PCPPNativeHierarchy.projected,counter_heads,counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.queryCountHead hf.queryCount
  by_cases h57 : i=57
  · subst i; simpa [lifted,slots,sourcePorts,PCPPNativeHierarchy.projected,counter_heads,counter_input,PCPPNativeMetadataMass.queryBytes] using And.intro hf.clauseStreamHead hf.clauseStream
  simp [lifted,slots,h0,h40,h47,h52,h54,h57,counter_input,counter_heads]

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
