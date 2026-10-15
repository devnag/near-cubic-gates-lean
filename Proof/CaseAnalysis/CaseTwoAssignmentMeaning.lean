import Proof.CaseAnalysis.CaseTwoAssignmentSystematic
import Proof.CaseAnalysis.CaseTwoAssignmentAuxiliary

/-! The two actual paths compute the original PCPP assignment on every named
proof variable. Literal signs are absent, as required by the unsigned core. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem bit_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity)
    (index : Fin ((a.output r).systematicBits+(a.output r).auxiliaryBits)) (oldIndex : ℕ) : ∃ out,
    runFrom (machine a) (budget a r u index.val)
      ⟨(machine a).start,heads a,input a r u index.val oldIndex⟩=some out ∧
    out.steps ≤ budget a r u index.val ∧
    out.final.tapes (low a 25)=[(a.output r).assignment u ((a.output r).honestAuxiliary u) index]:=by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) index
  · simpa only [Fin.val_castAdd,PointwisePCPP.assignment,Fin.addCases_left]
      using systematic_run a r u j oldIndex
  · simpa only [Fin.val_natAdd,PointwisePCPP.assignment,Fin.addCases_right]
      using auxiliary_run a r u j oldIndex

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
