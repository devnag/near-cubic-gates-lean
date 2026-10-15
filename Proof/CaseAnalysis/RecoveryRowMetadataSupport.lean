import Proof.CaseAnalysis.RecoveryRowPacketFields

/-! Exact support of the original fifteen metadata fields, including all
sentinel bytes and original C padding. This discharges the row input hmeta. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryRowMetadataSupport
open LocalBitMultitape RepairSource.VerifierDecoding RecoveryBoundedRowPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_bound (C F R count Q clauses S : ℕ)
    (hC : C≤S) (hF : F+6≤S) (hR : R+2≤S) (hc : count+1≤S)
    (hQ : Q+1≤S) (hcl : clauses+1≤S) (h7 : 7≤S) (j : Fin 15) :
    (fields C F R count Q clauses j).length≤S := by
  fin_cases j <;>
    simp [fields,ZeroPadding.pad_length,CompareMachine.word,UnaryTemplate.tape] <;> omega

theorem original_fields (C D F L R count Q clauses S : ℕ)
    (hC : C≤S) (hF : F+6≤S) (hR : R+2≤S) (hc : count+1≤S)
    (hQ : Q+1≤S) (hcl : clauses+1≤S) (h7 : 7≤S)
    (j : Fin 78) (hj : j∈RecoveryBoundedRowReload.ports) :
    (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses j).length≤S := by
  have ports : RecoveryBoundedRowReload.ports=List.ofFn port := by decide
  rw [ports,List.mem_ofFn] at hj
  obtain ⟨i,rfl⟩:=hj
  rw [←original C D F L R count Q clauses i]
  exact fields_bound C F R count Q clauses S hC hF hR hc hQ hcl h7 i

end NearCubicWires.RepairOrdinary.CloseoutRecoveryRowMetadataSupport
