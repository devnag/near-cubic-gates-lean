import SourceAdapters.Proximity.CappedCalls
import SourceAdapters.Proximity.NativePolynomial
import SourceAdapters.Code.SourcePrograms

/-! Q04: paid source calls on their original input encoding. CODE supplies
both the polynomial unary-cap loader and the exact result parser. Only the
shared X8 implementation join remains a hypothesis here. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins NearCubicGates.Published.CW19Proximity

/-- Every promised source run can be called and framed with a polynomial
ordinary clock on the same source input word, including its full cap loading. -/
theorem source_framed_polytime (hX8 : CappedWordRun) {Request : Type}
    (input output : Request → List Bool) (source : SourcePolyTime input output) :
    SourcePolyTime input (fun r => frame (output r)) := by
  obtain ⟨K, e, ⟨W⟩⟩ := source
  obtain ⟨A, d, ⟨caller⟩⟩ := NearCubicGates.Adapters.Code.clocked_wordFunction hX8 W.program K 1 e
  refine ⟨A, d, ⟨{ program := caller.program, realizes := ?_ }⟩⟩
  intro r
  obtain ⟨receipt, hr, ho⟩ := caller.realizes (input r)
  obtain ⟨sourceReceipt, hs, hout⟩ := W.realizes r
  refine ⟨receipt, hr, ?_⟩
  simpa only [Code.cappedOutput, hs, hout] using ho

/-- The whole proved native codec is immediately callable by another ordinary
program once X8 is supplied; no change to CW19's source encoding is assumed. -/
theorem framed_native_source_polytime (hX8 : CappedWordRun) :
    SourcePolyTime (fun S : SourceCircuit => PCPPNative.descriptor S.circuit)
      (fun S => frame (sourceCircuitWord S)) :=
  source_framed_polytime hX8 _ _
    ⟨20005 + 2 * SourcePrinting.nativeCoefficient, 4, ⟨SourcePrinting.nativeSourceWordFunction⟩⟩

end NearCubicGates.Adapters.Proximity
