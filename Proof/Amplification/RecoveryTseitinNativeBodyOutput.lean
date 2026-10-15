import Proof.Amplification.RecoveryTseitinNativeOutputProjection

/-! Expose the original native body at its exact descriptor and append
cursor before any particular circuit node is substituted. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_output {n : Nat} (index : Nat) (node : BooleanNode n)
    (hw : node.WellFormedAt index) (pre tail out : List Bool) (cap : Nat)
    (hc : coldNodeBudget index node ≤ cap) : ∃ r,
    runFrom machine (4*cap+7)
      ⟨machine.start,heads pre.length out.length,
        data n index (pre++PCPPRequestNodeSchema.native node++tail) out cap⟩=some r ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input
        (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input
        (CircuitInputCNF.circuitInputNodeClauses index node) ∧ r.steps ≤ 4*cap+7 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=body_run index node hw pre tail out cap hc
  refine ⟨r,?_,?_,?_,rs⟩
  · simpa only [original_source] using hr
  · exact output_head r _ _ rh
  · exact output_tape r _ _ _ _ _ rt

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
