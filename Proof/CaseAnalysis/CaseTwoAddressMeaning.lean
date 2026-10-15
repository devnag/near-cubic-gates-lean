import Proof.CaseAnalysis.CaseTwoAddressWindow

/-! The actual unsigned bit coordinates of the original padded seed. The
position remains at the end of the fixed clause cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressWindow
open SourceInterfaces RepairSource RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem padded_value {N q : ℕ} {c : BooleanCircuit q} (pcpp : PointwisePCPP c)
    (point : BitInput N) (offset cap : ℕ) (hcb : pcpp.clauseBits≤cap) :
    CloseoutLanguage.paddedUnsigned pcpp hcb (field point offset (q+cap+1))=
      pcpp.assignment (field point offset q) (pcpp.honestAuxiliary (field point offset q))
        (OccurrenceSliceTransport.occurrenceVariable pcpp
          (binaryAddress (field point (offset+q) pcpp.clauseBits),read point (offset+q+cap))):=by
  have hu : @occurrenceInput q pcpp.clauseBits
      (projectPaddedOccurrenceInput hcb (field point offset (q+cap+1)))=field point offset q:=by
    funext i
    have hi : i.val<q+pcpp.clauseBits:=by have hb:=i.isLt;omega
    simp [occurrenceInput,projectPaddedOccurrenceInput,field,hi]
  have hc : @occurrenceClauseAddress q pcpp.clauseBits
      (projectPaddedOccurrenceInput hcb (field point offset (q+cap+1)))=
        field point (offset+q) pcpp.clauseBits:=by
    funext i
    have hi : q+i.val<q+pcpp.clauseBits:=by have hb:=i.isLt;omega
    simp [occurrenceClauseAddress,projectPaddedOccurrenceInput,field,hi,Nat.add_assoc]
  have hp : @occurrencePosition q pcpp.clauseBits
      (projectPaddedOccurrenceInput hcb (field point offset (q+cap+1)))=read point (offset+q+cap):=by
    simp [occurrencePosition,projectPaddedOccurrenceInput,field,Nat.add_assoc]
  unfold CloseoutLanguage.paddedUnsigned CloseoutWitness.unsignedHonest
  rw [hu,hc,hp]

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressWindow
