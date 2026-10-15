import Proof.CaseAnalysis.CaseTwoOriginalSource

/-! The full retained source worker has one literal compound input and
otherwise blank tapes. Its real producer therefore owes only that word. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OriginalSource
open LocalBitMultitape RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_word (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy oracle : List Bool) :
    input source a k hierarchy oracle=SourceHandoff.sourceTapes (PCPPNativeInputFields.word hierarchy oracle):=by
  unfold input NativeSourceDock.input RequestDescriptor.input PCPPNativeClauseDescriptorConsumer.input
    AppendOutputFrame.input AppendOutputLength.input
  rw [PCPPNativeHierarchyNodes.input_word]
  repeat' apply PCPPRequestSource.single_input_from (by
    dsimp [RequestDescriptor.tapes,RequestDescriptor.base,PCPPNativeClauseDescriptorConsumer.tapes,
      PCPPNativeHierarchyNodes.tapes,PCPPNativeHierarchyNodes.base,PCPPNativeHierarchy.tapes]
    omega)
  rfl

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OriginalSource
