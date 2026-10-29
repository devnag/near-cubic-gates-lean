import SourceAdapters.Proximity.DecoderMachine
import SourceAdapters.Proximity.SourceComposition

/-! Q01/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": complete target-circuit to CW19 source-word
ordinary conversion. Target decoding, physical banks, native printing and
output framing are all adapters, absent from the published statement. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins NearCubicGates.Published.CW19Proximity

theorem target_source_polytime (hX8 : CappedWordRun) :
    SourcePolyTime Circuit.word (fun C => sourceCircuitWord (sourceCircuit C)) := by
  apply source_polytime_comp hX8 Circuit.word (fun C => PCPPNative.descriptor C.D)
  · exact ⟨20005 + 2 * DecoderBank.decodeCoefficient, 25, ⟨DecoderBank.targetNativeWordFunction⟩⟩
  · refine ⟨20005 + 2 * SourcePrinting.nativeCoefficient, 4, ⟨?_⟩⟩
    exact {
      program := SourcePrinting.nativeSourceWordFunction.program
      realizes := fun C => SourcePrinting.nativeSourceWordFunction.realizes (sourceCircuit C) }

end NearCubicGates.Adapters.Proximity
