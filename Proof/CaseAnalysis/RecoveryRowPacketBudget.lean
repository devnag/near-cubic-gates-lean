import Proof.CaseAnalysis.RecoveryRowPacketRefresh

/-! All original prototype printing, erasure and rewind fit in one linear
multiple of the already paid row backing. No sharper recovery estimate is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (C F R count Q clauses : ℕ) :
    budget C F R count Q clauses=24*C+8*F+4*R+4*count+4*Q+4*clauses+177 := by
  simp [budget,paddedBudget,fieldBudget,header,frame_length,CompareMachine.word]
  omega

theorem refresh_bound (C F R count Q clauses B : ℕ)
    (hC : C≤B) (hF : F≤B) (hR : R≤B) (hc : count≤B) (hQ : Q≤B) (hcl : clauses≤B) :
    refreshBudget C F R count Q clauses B≤512*(B+1) := by
  rw [refreshBudget,readyBudget,budget_eq]
  omega

theorem Loaded.refresh_bound {C F R count Q clauses B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded (values C F R count Q clauses) B H A) :
    refreshBudget C F R count Q clauses B≤512*(B+1) := by
  have h0:=h.bounds 0
  have h1:=h.bounds 1
  have h2:=h.bounds 2
  have h3:=h.bounds 3
  have h4:=h.bounds 4
  have h5:=h.bounds 5
  change 2*C+4≤B at h0
  change 2*F+4≤B at h1
  change 2*R+4≤B at h2
  change 2*count+4≤B at h3
  change 2*Q+4≤B at h4
  change 2*clauses+4≤B at h5
  exact RecoveryBoundedRowPacketAppend.refresh_bound C F R count Q clauses B
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
